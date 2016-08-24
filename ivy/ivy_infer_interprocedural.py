#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# A DAG of calls represents a compressed call stack potentially leading to a counterexample
# Our goal is to prove that the DAG is unrealizable
#
# Every node contains: in the GPDR paper, a structure and a stack level (current frame)
#
# (rule Decide, p. 7) Each node points to "children" that correspond to a realization of the 
# state of the procedure with summaries of the callee procedures from the current previous frame - right?
# We go and try to refine the previous frame procedures to make sure this can't happen (spurious)
# How?
# I think really the local variables from the current procedure are not that important
# What's important is a realization of the *callees* local variables (in their last stack frame),
# which are allowed by those procedures' summaries (and together lead to the violation).
# SO WE NEED A MODEL OF EVERY CALLEE SUMMARY that together violate the current procedure proof obligation
# we then continue to try to refine AT LEAST ONE callee summary to show that this model is actually unreachable,
# then we can close this branch of the DAG.
# Why? Because the frames i should now exclude M, so we can remove M,i from the DAG.
# Once a node has no children (because we blocked all possible callee states that we previously expanded)
# and cannot be expanded --- because the summaries at frame i-1 show that the procedure at bound i must satisfy
# the proof goal --- we can remove this node as well (recursively or something).

# We use UPDR, so what we keep in the nodes is not states but their generalization, because every generalization
# (in the universal cone) leads to violating the "proof goal" (we begin with safety, of course).

# this is a cache of REACHABLE states
# GPDR also uses a CACHE, not sure what this is
# for us this is diagrams? how to check equality?...
# TODO: Why do we need this?...

# TODO: how does the algorithm traverse the DAG? recursively, DFS?
# TODO: do we really need to hold the DAG explicitly, then?

# Different paths in the same procedure:
# 1. One solution is to assume that all calls are relevant to every path
# TODO: why is this not good enough? Efficiency of calls to Z3?
# 2. Another solution is to break the procedure to all distinct paths,
# So there are now several different transforms for the same procedure
# How is this represented in the graph? I think it's not represented,
# it's just something you use in the expansion rule, and once you can't expand
# by any procedural path, you are done.

# TODO: PRECONDITION AND POSTCONDITION

# TODO: also need to decide SAFETY and INIT

# TODO: EA summaries?


# Technical solution of interprocedural Ivy semantics:
# a History where each state is a subcall to a procedure?
# Obtain the update function (for the history_forward_step) by modifying
# ivy_actions.CallAction.int_udpate?
# see also CallAction.get_callee(self) which may be a good place to change
# but returns type Action
# perhaps return an AssumeAction according to the summary? No.
# perhaps a designated action?

# history = self.get_history(state, bound) in ivy_art.bmc has the state
# in which we will check satisfy, that is: the final state
# the state argument in history_satisfy seems to have lesser effect.

import ivy
import ivy_interp as itp
import ivy_utils as utl
import tk_ui as ui
import ivy_utils as iu
import ivy_module as im
import ivy_alpha
import ivy_art
import ivy_interp
import ivy_isolate
import ivy_module

import ivy_infer_universal
import ivy_logic_utils
import ivy_solver
import ivy_infer

import sys
import logging

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)

logger = logging.getLogger(__file__)

import ivy_actions
import ivy_transrel

def zzz_new_no_error_clauses():
    sig = ivy_module.module.sig
    for sym in sig.symbols.items():
        if sym[0] == 'errorush':
            errorush_sym = sym[1]
            break
    no_error_clauses = ivy_logic_utils.dual_clauses(ivy_logic_utils.Clauses([ivy_transrel.new(errorush_sym)]))
    return no_error_clauses

def get_signature_symbols():
    sig = ivy_module.module.sig
    sig_symbols = [sym[1] for sym in sig.symbols.items()]
    # including both constants and relations!
    return sig_symbols
    

class ProcedureSummary(object):
    def __init__(self):
        super(ProcedureSummary, self).__init__()
        
        self._update_clauses = ivy_logic_utils.true_clauses()                                                             
    
    def strengthen(self, summary_strengthening):
        self._update_clauses = ivy_transrel.conjoin(self._update_clauses, 
                                                    summary_strengthening)
        
    def get_updated_vars(self):
        # including both constants and relations!
        return get_signature_symbols()
    
    def get_update_clauses(self):
        return self._update_clauses
    
    def get_precondition(self):
        return ivy_logic_utils.true_clauses() # no precondition
    
    def implies(self, other_summary):
        assert self.get_precondition() == other_summary.get_precondition()
        assert self.get_updated_vars() == other_summary.get_updated_vars()
        return ivy_solver.clauses_imply(self.get_update_clauses(),
                                        other_summary.get_update_clauses())

class SummarizedAction(ivy_actions.Action):
    def __init__(self, name, original_action, procedure_summary):
        super(SummarizedAction, self).__init__()
        
        self._procedure_summary = procedure_summary
        
        self._name = name
        
        self._original_action = original_action
        
        if hasattr(original_action,'formal_params'):
            self.formal_params = original_action.formal_params
        if hasattr(original_action,'formal_returns'):
            self.formal_returns = original_action.formal_returns
            
    def name(self):
        return self._name
            
    # Override AST.clone()
    def clone(self,args):
        return SummarizedAction(self._name, self._original_action, 
                                self._procedure_summary)
            
    # Override
    def action_update(self, domain, pvars):
        updated  = self._procedure_summary.get_updated_vars()
        clauses  = self._procedure_summary.get_update_clauses()
        pre      = self._procedure_summary.get_precondition()
        return (updated, clauses, pre)
    
# Used for interpreting the semantics of called procedures by their summary
# Affects ivy_actions.CallAction.get_callee()
class SummarizedActionsContext(ivy_actions.ActionContext):
    def __init__(self, procedure_summaries):
        super(SummarizedActionsContext, self).__init__()
        
        self._procedure_summaries = procedure_summaries
        
    # Override
    def get(self, symbol):
        original_action = ivy_module.find_action(symbol)
        return SummarizedAction(symbol, original_action, 
                                self._procedure_summaries[symbol])
        
def subprocedures_states_iter(ag, state_to_decompose):
    analysis_graph = ag.decompose_state_partially_repsect_context(state_to_decompose)
    assert analysis_graph is not None
    
    subprocedures_states = []
    
    # Note: the first state is the initial state, and it is not associated with any action
    for i in xrange(1, len(analysis_graph.states)):
        state = analysis_graph.states[i]
        if state.expr is None:
            continue
        
        action = ivy_interp.eval_action(state.expr.rep)
        
        if isinstance(action, ivy_actions.AssignAction) or \
           isinstance(action, ivy_actions.AssumeAction) or \
           isinstance(action, ivy_actions.AssertAction) or \
           isinstance(action, ivy_actions.HavocAction) or \
           isinstance(action, SummarizedAction):
            continue
        
        if isinstance(action, ivy_actions.CallAction):
            previous_state = analysis_graph.states[i-1]
            subprocedures_states.append((action, previous_state, state))
        
        rec_res = subprocedures_states_iter(ag, state)
        subprocedures_states += rec_res
        
    return subprocedures_states

def clauses_to_new_vocabulary(clauses):
    """"Type of vocabulary used by actions, see ivy_transrel.state_to_action"""
#     ivy_transrel.state_to_action((callee_current_summary.get_updated_vars(), 
#                                         after_state.clauses, 
#                                         callee_current_summary.get_precondition()))[1]
    renaming = dict()
    for s in clauses.symbols():
        if s.is_numeral():
            continue
        if ivy_transrel.is_skolem(s):
            continue
        renaming[s] = ivy_transrel.new(s)
    return ivy_logic_utils.rename_clauses(clauses, renaming)

def clauses_from_new_vocabulary(clauses):
    renaming = dict()
    for s in clauses.symbols():
        if s.is_numeral():
            continue
        if ivy_transrel.is_skolem(s):
            continue
        if ivy_transrel.is_new(s):
            renaming[s] = ivy_transrel.new_of(s)
    return ivy_logic_utils.rename_clauses(clauses, renaming)

def hide_callers_local_variables(clauses, call_action):
    callee_action = call_action.get_callee()
    formals = callee_action.formal_params + callee_action.formal_returns
    symbols_can_be_modified = get_signature_symbols() + formals
    symbols_can_be_modified_two_vocab = symbols_can_be_modified + \
                                        [ivy_transrel.new(s) for s in symbols_can_be_modified]
    
    unrelated_syms = [s for s in clauses.symbols() 
                        if s not in symbols_can_be_modified_two_vocab and not s.is_numeral()]
    return ivy_transrel.hide_clauses(unrelated_syms, clauses)

    # TODO: MUST TEST this with global variables, local variables, and nested calls
     
def transition_states_to_summary(before_state, after_state):
    # TODO: translate formal parameters back before this call
    # TODO: because get_updated_vars() uses them and not the uniquely renamed ones
    # TODO: perhaps rename the rest and keep the names of the formal params?...
    
#     print call_action, before_state, after_state
    
    after_clauses_locals_hidden_new_vocab = clauses_to_new_vocabulary(after_state.clauses) 
    
    return ivy_transrel.conjoin(before_state.clauses,
                                after_clauses_locals_hidden_new_vocab)
    
def update_from_action(ivy_action):
    # TODO: int_update? update? rename our function name?
    return ivy_action.int_update(im.module, {})
    
def get_action_two_vocabulary_clauses(ivy_action, axioms):
    # based on ivy_transrel.forward_image_map, without existential quantification
    updated, clauses, _precond = update_from_action(ivy_action)
    pre_ax = ivy_logic_utils.clauses_using_symbols(updated, axioms)
    pre = pre_ax
    # no existential quantification on pre clauses, just convert to new
    clauses_new_vocab = ivy_logic_utils.rename_clauses(clauses, 
                                                        dict((ivy_transrel.new(x), x) 
                                                                 for x in clauses.symbols() 
                                                                 if x not in updated))
    res = ivy_transrel.conjoin(pre, clauses_new_vocab)
    logger.debug("two vocab for procedure: %s", res)
    return updated, res
    

def get_two_vocab_transition_clauses_wrt_summary(ivy_action, procedure_summaries, axioms):
    with SummarizedActionsContext(procedure_summaries):
        res = get_action_two_vocabulary_clauses(ivy_action, axioms)
        
    return res

def extend_two_vocab_update_with_frames(two_vocab_update, updated_syms, all_syms):
    not_updated_syms = filter(lambda s: s not in updated_syms, all_syms)
    other_syms_not_updated = ivy_transrel.frame(not_updated_syms,
                                                None,
                                                ivy_transrel.new)
    
    return ivy_transrel.conjoin(two_vocab_update, other_syms_not_updated)


def get_two_vocabulary_update_clauses_wrt_vocab(ivy_action, procedure_summaries, 
                                                more_two_vocab_syms, axioms):
    updated_syms, two_vocab_update = get_two_vocab_transition_clauses_wrt_summary(ivy_action, 
                                                                                  procedure_summaries, 
                                                                                  axioms)
    
    more_syms = set()
    for s in more_two_vocab_syms:
        if not ivy_transrel.is_new(s):
            more_syms.add(s)
        else:
            more_syms.add(ivy_transrel.new_of(s))
    
    two_vocab_update_with_frames =  extend_two_vocab_update_with_frames(two_vocab_update, 
                                                                        updated_syms, 
                                                                        more_syms)
    return two_vocab_update_with_frames

def get_transition_cex_to_obligation_two_vocab(ivy_action, proc_name, 
                                               procedure_summaries, two_vocab_obligation):    
    axioms = im.module.background_theory()
    
    two_vocab_update_with_frames = get_two_vocabulary_update_clauses_wrt_vocab(ivy_action, 
                                                                               procedure_summaries, 
                                                                               two_vocab_obligation.symbols(), 
                                                                               axioms)
    
    clauses_to_check_sat = ivy_transrel.conjoin(two_vocab_update_with_frames,
                                                ivy_logic_utils.dual_clauses(two_vocab_obligation))
    
    cex_model = ivy_solver.get_model_clauses(clauses_to_check_sat)
    if cex_model is None:
        return None

    clauses_cex = ivy_solver.clauses_model_to_clauses(clauses_to_check_sat,
                                                      model=cex_model)
    assert clauses_cex != None    
    return clauses_cex

def separate_two_vocab_cex(ivy_action, two_vocab_cex_clauses):
    updated_syms, _, _ = update_from_action(ivy_action)

    hide_in_pre_syms = [s for s in two_vocab_cex_clauses.symbols() 
                            if ivy_transrel.is_new(s)]
    hide_in_post_syms   = [s for s in two_vocab_cex_clauses.symbols() 
                            if not ivy_transrel.is_new(s) and s in updated_syms]

    pre_clauses = ivy_transrel.hide_clauses(hide_in_pre_syms,
                                             two_vocab_cex_clauses)
    post_clauses_post_vocab = ivy_transrel.hide_clauses(hide_in_post_syms,
                                             two_vocab_cex_clauses)
    post_clauses = clauses_from_new_vocabulary(post_clauses_post_vocab)
    
    return (ivy_interp.State(value=ivy_transrel.pure_state(pre_clauses)),
            ivy_interp.State(value=ivy_transrel.pure_state(post_clauses)))
    
def ag_from_two_vocab_cex(action_name, ivy_action, two_vocab_cex_clauses):
    pre_state, post_state = separate_two_vocab_cex(ivy_action, two_vocab_cex_clauses)
    
    ag = ivy_art.AnalysisGraph()
    # based on AnalysisGraph.execute
    ag.add(pre_state)
    ag.add(post_state, ivy_interp.action_app(action_name, pre_state))
    return ag
    
def generate_summary_obligations_from_cex(procedure_summaries, ag):
    with SummarizedActionsContext(procedure_summaries):
        assert len(ag.states) == 2
        subprocedures_transitions = subprocedures_states_iter(ag, ag.states[-1])
        
        for call_action, before_state, after_state in subprocedures_transitions:
            transition_summary = transition_states_to_summary(before_state, after_state)
            print transition_summary
            # TODO: use utils from ivy_infer_universal
            universal_transition_summary = ivy_logic_utils.dual_clauses(ivy_solver.clauses_model_to_diagram(transition_summary, model=None))
            summary_locals_hidden = hide_callers_local_variables(universal_transition_summary, call_action)
            # TODO: yield, not return
            return [(call_action.callee_name(), summary_locals_hidden)]
        
    # TODO: this actually assumes that the action consists of at least something more than the
    # TODO: call, otherwise the result is still [] although we have what to refine
    # FIXME: make sure that such procedures are inlined or treated carefully
    return []
    
def check_procedure_transition(ivy_action, proc_name,
                               procedure_summaries, two_vocab_obligation):
    with SummarizedActionsContext(procedure_summaries):
        two_vocab_cex = get_transition_cex_to_obligation_two_vocab(ivy_action, proc_name,
                                         procedure_summaries, two_vocab_obligation)
        if two_vocab_cex is None:
            return None
        logger.debug("Got cex: %s", two_vocab_cex)
    
        ag = ag_from_two_vocab_cex(proc_name, ivy_action, two_vocab_cex)
        summary_obligations = generate_summary_obligations_from_cex(procedure_summaries, ag)
        assert summary_obligations != None
        return summary_obligations

def generelize_summary_blocking(ivy_action, proc_name, 
                                procedure_summaries, proof_obligation):
    assert proof_obligation is not None
    axioms = im.module.background_theory()
    
    proc_transition_clauses = get_two_vocabulary_update_clauses_wrt_vocab(ivy_action, 
                                                                          procedure_summaries, 
                                                                           proof_obligation.symbols(), 
                                                                           axioms)
    
    obligation_not = ivy_logic_utils.dual_clauses(proof_obligation)
    
    NO_INTERPRETED = None
    res = ivy_transrel.interpolant(proc_transition_clauses, obligation_not,
                                  axioms, NO_INTERPRETED)
    assert res != None
    return res[1]
                                        
                
def infer_safe_summaries():
    exported_actions_names = [ed.exported() for ed in ivy_module.module.exports]
    res = ivy_infer.pdr(GUPDRElements(ivy_module.module.actions,
                                      exported_actions_names))
    
    if res is None:
        logger.info("Not safe!")
    else:
        logger.info("Safe!")
        for name, summary in res.iteritems():
            logger.debug("Summary of procedure %s:", name)
            logger.debug("%s" % summary.get_update_clauses())
            logger.debug("")

#     procedure_summaries = {}
#     actions_dict = ivy_module.module.actions
#     for name, ivy_action in actions_dict.iteritems():
#         procedure_summaries[name] = ProcedureSummary()
#         
#     #proof_goal = ivy_logic_utils.to_clauses('~errorush()')
#     proof_goal = zzz_new_no_error_clauses()    
#     
#     name, ivy_action = actions_dict.items()[0]
#     if True:
#         new_proof_goal = check_procedure_transition(ivy_action, name, 
#                                                 procedure_summaries, 
#                                                 proof_goal)
#         print new_proof_goal
#         procedure_summaries[name].strengthen(ivy_logic_utils.to_clauses('~errorush()'))
#         for subp in actions_dict.iterkeys():
#             if subp.strip() != "get_next":
#                 continue
#             else:
#                 print "found our action"
#             procedure_summaries[subp].strengthen(zzz_new_no_error_clauses())
#             
#         new_proof_goal = check_procedure_transition(ivy_action, name, 
#                                                 procedure_summaries, 
#                                                 proof_goal)
#         print new_proof_goal
#         assert new_proof_goal is None
#         
#         procedure_summaries[name].strengthen(zzz_new_no_error_clauses())
#         proc_strengthening = generelize_summary_blocking(procedure_summaries[name].get_update_clauses(),
#                                      ivy_logic_utils.dual_clauses(proof_goal))
#         assert proc_strengthening is not None
#         procedure_summaries[name].strengthen(proc_strengthening)
#         print procedure_summaries[name].get_update_clauses()
#         

# TODO: remove
def global_initial_state():
    with im.module.copy():
        ivy_isolate.create_isolate(None) # ,ext='ext'
        ag = ivy_art.AnalysisGraph(initializer=ivy_alpha.alpha)
        with ivy_interp.EvalContext(check=False):
            assert len(ag.states) == 1
            # TODO: need the background theory?
            # state1 = ag.states[0]
            # initial_state_clauses = ivy_logic_utils.and_clauses(state1.clauses,state1.domain.background_theory(state1.in_scope))
            initial_state_clauses = ag.states[0].clauses
            logger.debug("initial state clauses: %s", initial_state_clauses)
            return initial_state_clauses
        
class GUPDRElements(ivy_infer_universal.UnivPdrElements):
    def __init__(self, actions_dict, exported_actions_names):
        super(GUPDRElements, self).__init__()
        
        self._actions_dict = actions_dict
        self._exported_actions_names = exported_actions_names
        
    def initial_summary(self):
#         procedure_summaries = {}
#         
#         # TODO: hack?
#         global_initial_pre_vocab = global_initial_state()
#     
#         for name, _ in self._actions_dict.iteritems():
#             procedure_summaries[name] = ProcedureSummary()
#             procedure_summaries[name]._update_clauses = global_initial_pre_vocab
#             
#         return procedure_summaries
        procedure_summaries = {}
    
        for name, _ in self._actions_dict.iteritems():
            procedure_summaries[name] = ProcedureSummary()
            # TODO: hack, and explain
            procedure_summaries[name]._update_clauses = ivy_logic_utils.false_clauses()
            
        return procedure_summaries
    
    
    def top_summary(self):
        procedure_summaries = {}
    
        for name, _ in self._actions_dict.iteritems():
            procedure_summaries[name] = ProcedureSummary()
            
        return procedure_summaries
    
    # Return None if safe or proof obligation otherwise
    def check_summary_safety(self, summaries):
        for name in self._exported_actions_names:
            logger.debug("Checking safety of proc %s", name)
            ivy_action = self._actions_dict[name]
            proof_goals = check_procedure_transition(ivy_action, name, 
                                                     summaries, self._get_safety_property())
            if proof_goals is not None:
                return proof_goals
        return None
    
    def _get_safety_property(self):
        no_cme = ivy_logic_utils.to_clauses('~cme(I)')
        no_cme_next = clauses_to_new_vocabulary(no_cme)
        return ivy_transrel.conjoin(no_cme, no_cme_next) 
    
    # Return None or a new proof obligation
    def check_transformability_to_violation(self, predicate, summaries_by_symbol, 
                                            proof_obligation):
        procedure_name_to_check = predicate
        procedure_summaries = summaries_by_symbol
        
        ivy_action = self._actions_dict[procedure_name_to_check]
        
        new_proof_goals = check_procedure_transition(ivy_action, procedure_name_to_check, 
                                                   procedure_summaries, 
                                                   proof_obligation)
        if new_proof_goals is None:
            return None
        
        return new_proof_goals
    
    def generalize_intransformability(self, predicate, summaries, proof_obligation):
        logger.debug("Generalizing intransformability for predicate %s with proof obligation %s",
                     predicate, proof_obligation)
        
        return generelize_summary_blocking(self._actions_dict[predicate], predicate,
                                           summaries,
                                           proof_obligation)

        
def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)
        
def main():
    logging.basicConfig(level=logging.DEBUG)
   
    ivy.read_params()
    iu.set_parameters({'mode':'induction'})
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        with utl.ErrorPrinter():
            ivy.source_file(sys.argv[1],ivy.open_read(sys.argv[1]),create_isolate=False)
            infer_safe_summaries()

if __name__ == "__main__":
    main()