#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_logic_utils
import ivy_transrel
import ivy_solver

import logging
import abc

logger = logging.getLogger(__file__)
           
class ClausesClauses(object):
    def __init__(self, clauses_list=None):
        if clauses_list is None:
            clauses_list = []
        self._conjuncts_clauses_list = clauses_list
       
    def get_conjuncts_clauses_list(self):
        return self._conjuncts_clauses_list
    
    # TODO: remove?
    def to_single_clauses(self):
        res = ivy_logic_utils.true_clauses()
        for clauses in self.get_conjuncts_clauses_list():
            res = ivy_transrel.conjoin(res, clauses)
        return res
   
    def conjoin(self, clauses):
        self._conjuncts_clauses_list.append(clauses)
        
    def get_model(self):
        import z3
        
        s = z3.Solver()
        
        for clauses1 in self.get_conjuncts_clauses_list():
            z3c = ivy_solver.clauses_to_z3(clauses1)
            s.add(z3c)
        res = s.check()
        if res == z3.unsat:
            return None
        
        m = ivy_solver.get_model(s)
        
        used_symbols = set.union(*[ivy_logic_utils.used_symbols_clauses(clauses1) 
                                  for clauses1 in self.get_conjuncts_clauses_list()]) 
        
        return ivy_solver.HerbrandModel(s,m,used_symbols)
        
    def __str__(self, *args, **kwargs):
        return str(self._conjuncts_clauses_list)
    
class PdrElements(object):
    __metaclass__ = abc.ABCMeta
    
    @abc.abstractmethod
    def initial_summary(self):
        pass
    
    @abc.abstractmethod
    def top_summary(self):
        pass
    
    # Return None if safe or proof obligation otherwise
    @abc.abstractmethod
    def check_summary_safety(self, summaries):
        pass
    
    # return None or a new proof obligation
    @abc.abstractmethod
    def check_transformability_to_violation(self, summaries_by_symbol, proof_obligation):
        pass
    
    @abc.abstractmethod
    def generalize_intransformability(self, prestate_summaries, poststate_clauses):
        pass
           
class PredicateSummary(object):
    def __init__(self, predicate_symbol, summary_single_clauses):
        self._predicate_symbol = predicate_symbol
       
        self._summary = ClausesClauses([summary_single_clauses])
       
    def get_summary(self):
        return self._summary
       
    def get_predicate_symbol(self):
        return self._predicate_symbol
   
    def strengthen(self, summary_strengthening):
        self._summary.conjoin(summary_strengthening)
        
class SummaryProofObligation(object):
    def __init__(self, predicate, obligation_clauses):
        self._predicate = predicate
        self._proof_obligation = obligation_clauses
        
    def predicate(self):
        return self._predicate
    
    def obligation_clauses(self):
        return self._proof_obligation

class PdrFrame(object):
    def __init__(self, summaries_by_symbol):
        super(PdrFrame, self).__init__()
           
        self._summaries_by_symbol = summaries_by_symbol
   
    def get_summaries_by_symbol_dict(self):
        return self._summaries_by_symbol
   
    def strengthen(self, predicate_to_strengthen, summary_strengthening):
        self._summaries_by_symbol[predicate_to_strengthen].strengthen(summary_strengthening)

def are_frames_converged(frame1, frame2):
    summaries_dict_1 = frame1.get_summaries_by_symbol_dict()
    summaries_dict_2 = frame2.get_summaries_by_symbol_dict()
   
    for predicate_symbol in summaries_dict_2.iterkeys():
        summary1 = summaries_dict_1.get(predicate_symbol)
        summary2 = summaries_dict_2.get(predicate_symbol)
        if not all(ivy_solver.clauses_list_imply_list(summary2.get_summary().get_conjuncts_clauses_list(),
                                                  summary1.get_summary().get_conjuncts_clauses_list())):

            return False

    return True

# TODO: rename current_bound to current_frame?
def backwards_prove_at_least_one_goal(frames, current_bound, summary_proof_obligations, pdr_elements):
    logger.debug("Can block by refining summeries in: %s", 
                 [pred for pred, _ in summary_proof_obligations])
    
    for predicate, summary_proof_obligation in summary_proof_obligations:
        logger.debug("Trying to block %s for predicate %s from frame %d", summary_proof_obligation, 
                                                                          predicate,
                                                                          current_bound)
        if current_bound == 0:
            return False
       
        previous_bound = current_bound - 1
       
        while True:
            previous_frame_summaries = frames[previous_bound].get_summaries_by_symbol_dict()
            previous_bound_proof_obligation = pdr_elements.check_transformability_to_violation(predicate,
                                                                                               previous_frame_summaries,
                                                                                               summary_proof_obligation)
            if previous_bound_proof_obligation is None:
                logger.debug("pdr goal at frame %d provable from previous frame: %s", current_bound, summary_proof_obligation)
                break
           
            successfully_blocked_this_predicate = backwards_prove_at_least_one_goal(frames, previous_bound,
                                                                                    previous_bound_proof_obligation, pdr_elements)
            if not successfully_blocked_this_predicate:
                # couldn't block with this predicate, try to refine the next predicate
                continue
           
        for i in xrange(1, current_bound + 1):
            summary_proof_obligation_generalization = pdr_elements.generalize_intransformability(predicate,
                                                                                                 frames[i-1].get_summaries_by_symbol_dict(),
                                                                                                 summary_proof_obligation)
            logger.debug("pdr strenghening frames up to bound %d with %s", current_bound, summary_proof_obligation_generalization)
            frames[i].strengthen(predicate, summary_proof_obligation_generalization)
           
        # successfully proved at least one proof goal
        return True
    
    # couldn't prove any proof goal, cex
    return False
       
def check_pdr_convergence(frames, current_bound):
    for i in xrange(0, current_bound):
        if are_frames_converged(frames[i], frames[i+1]):
            return frames[i].get_summaries_by_symbol_dict()
    return None

def backward_refine_frames_or_counterexample(frames, new_bound,
                                             pdr_elements):
    while True:
        new_frame_summaries = frames[new_bound].get_summaries_by_symbol_dict()
       
        safety_proof_obligations = pdr_elements.check_summary_safety(new_frame_summaries)
        if safety_proof_obligations is None:
            logger.debug("pdr frame %d is safe", new_bound)
            return True
        
    
        successfully_blocked = backwards_prove_at_least_one_goal(frames, new_bound, safety_proof_obligations, pdr_elements)
        if not successfully_blocked:
            # TODO: collect counter-trace
            return False

def pdr(pdr_elements):
    frames = []
   
    frames.insert(0, PdrFrame(pdr_elements.initial_summary()))
    current_bound = 0
   
    while True:
        logger.debug("pdr: unroll to %d", current_bound + 1)
        new_bound = current_bound + 1
        frames.insert(new_bound, PdrFrame(pdr_elements.top_summary()))
       
        successfully_blocked = backward_refine_frames_or_counterexample(frames, new_bound, pdr_elements)
        if not successfully_blocked:
            return None
       
        current_bound = new_bound
       
        fixpoint_summaries = check_pdr_convergence(frames, current_bound)
        if fixpoint_summaries is not None:
            logger.debug("pdr frames at fixpoint")
            assert pdr_elements.check_summary_safety(fixpoint_summaries) is None

            return fixpoint_summaries
        else:
            logger.debug("pdr frames not at fixpoint, continue unrolling")