#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy
import ivy_interp as itp
import ivy_actions as act
import ivy_utils as utl
import ivy_logic_utils as lut
import tk_ui as ui
import ivy_logic as lg
import ivy_utils as iu
import ivy_module as im
import ivy_alpha
import ivy_art
import ivy_interp
import ivy_compiler
import ivy_isolate

import ivy_logic_utils
import ivy_transrel
import ivy_solver

import sys

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)


def display_cex(msg,ag):
    print msg
    if diagnose.get():
        ui.ui_main_loop(ag)
    exit(1)
    
def check_properties():
    if itp.false_properties():
        if diagnose.get():
            print "Some properties failed."
            gui = ui.new_ui()
            gui.tk.update_idletasks() # so that dialog is on top of main window
            gui.try_property()
            gui.mainloop()
            exit(1)
        raise iu.IvyError(None,"Some properties failed.")
    im.module.labeled_axioms.extend(im.module.labeled_props)


def check_conjectures(kind,msg,ag,state):
    failed = itp.undecided_conjectures(state)
    if failed:
        if diagnose.get():
            print "{} failed.".format(kind)
            gui = ui.new_ui()
            agui = gui.add(ag)
            gui.tk.update_idletasks() # so that dialog is on top of main window
            agui.try_conjecture(state,msg="{}\nChoose one to see counterexample.".format(msg))
            gui.tk.mainloop()
            exit(1)
        raise iu.IvyError(None,"{} failed, {}".format(kind,msg))
    
def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)
                    
def check():
    ivy_isolate.create_isolate(None)
    check_properties()
    ag = ivy_art.AnalysisGraph(initializer=ivy_alpha.alpha)
    with ivy_interp.EvalContext(check=False):
        #check_conjectures('Initiation','These conjectures are false initially.',ag,ag.states[0])
        for a in sorted(im.module.public_actions):
            print "trying {}...".format(a)
            ag.execute_action(a,prestate=ag.states[0])
            cex = ag.check_bounded_safety(ag.states[-1])
            if cex is not None:
                display_cex("safety failed",cex)
            check_conjectures('Consecution','These conjectures are not inductive.',ag,ag.states[-1])
            
class PredicateSummary(object):
    def __init__(self, predicate_symbol, summary):
        self._predicate_symbol
        
        self._summary = summary
        
    def get_summary(self):
        return self._summary
        
    def get_predicate_symbol(self):
        return self._predicate_symbol
    
    def strengthen(self, summary_strengthening):
        self._summary = ivy_transrel.conjoin(self._summary, summary_strengthening)

class PdrFrame(object):
    def __init__(self, predicate_summary=None):
        super(PdrFrame, self).__init__()
        
        self._inv_predicate = "inv"
        
        if predicate_summary is None:
            predicate_summaries_lst = [PredicateSummary(self._inv_predicate, ivy_logic_utils.true_clauses())]
        else:
            predicate_summaries_lst = [predicate_summary]
            
        self._summaries_by_symbol = dict((predicate_summary.get_predicate_symbol(), predicate_summary) 
                                                for predicate_summary in predicate_summaries_lst)
    
    def get_summaries_by_symbol_dict(self):
        return self._summaries_by_symbol
        
    def substitute_summaries(self, formula):
        # TODO:
        return formula
    
    def strengthen(self, summary_strengthening):
        self._summaries_by_symbol[self._inv_predicate].strengthen(summary_strengthening)

def are_frames_converged(frame1, frame2):
    summaries_dict_1 = frame1.get_summaries_by_symbol_dict()
    summaries_dict_2 = frame2.get_summaries_by_symbol_dict()
    
    for predicate_symbol in summaries_dict_2:
        summary1 = summaries_dict_1.get(predicate_symbol)
        summary2 = summaries_dict_2.get(predicate_symbol)
        if not ivy_solver.clauses_imply(summary2.get_summary(),
                                        summary1.get_summary()):
            return False

    return True

# TODO: rename current_bound to current_frame?
def prove_goal(frames, current_bound, summary_proof_obligation, check_transformability_to_violation):
    if current_bound == 0:
        return False
    
    previous_bound = current_bound - 1
    
    while True:
        # TODO: should also pass the predicate summary we are refining
        previous_bound_proof_obligation = check_transformability_to_violation(frames[previous_bound].get_summaries_by_symbol_dict(),
                                                                        summary_proof_obligation)
        if previous_bound_proof_obligation is None:
            break
        
        successfully_blocked = prove_goal(previous_bound, previous_bound_proof_obligation, check_transformability_to_violation)
        if not successfully_blocked:
            return False
        
    for i in xrange(1, current_bound):
        frames[i].strengthen(summary_proof_obligation)
        
    return True
        
def check_pdr_convergence(frames, current_bound):
    for i in xrange(0, current_bound):
        if are_frames_converged(frames[i], frames[i+1]):
            return frames[i].get_summaries_by_symbol_dict()
    return None

def backward_refine_frames_or_counterexample(frames, new_bound, check_summary_safety, check_transformability_to_violation):
    while True:
        new_frame_summaries = frames[new_bound].get_summaries_by_symbol_dict()
        
        counterexample_to_safety = check_summary_safety(new_frame_summaries)
        if counterexample_to_safety is None:
            return True
        
        successfully_blocked = prove_goal(frames, new_bound, counterexample_to_safety, check_transformability_to_violation)
        if not successfully_blocked:
            # TODO: collect counter-trace
            return False

def pdr(initial_summary, check_summary_safety, check_transformability_to_violation):
    frames = []
    
    frames[0] = PdrFrame(initial_summary)
    current_bound = 0
    
    while True:
        new_bound = current_bound + 1
        frames[new_bound] = PdrFrame()
        
        successfully_blocked = backward_refine_frames_or_counterexample(frames, new_bound, check_transformability_to_violation)
        if not successfully_blocked:
            return None
        
        current_bound = new_bound
        
        safe_summaries = check_pdr_convergence(frames, current_bound)
        if safe_summaries is not None:
            return safe_summaries
        
def check_summary_safety_inductive_invariants(summaries_dict):
    pass

def check_any_exported_action_transition(prestate_clauses, poststate_clauses):
    import ivy_ui
    import ivy_logic as il
    import logic as lg
    from ivy_interp import State,EvalContext,reverse,decompose_action_app
    import ivy_module as im
    import ivy_logic_utils as ilu
    import logic_util as lu
    import ivy_utils as iu
    import ivy_graph_ui
    import ivy_actions as ia

    
    import ivy_transrel
    from ivy_solver import get_small_model
    from proof import ProofGoal
    from ivy_logic_utils import Clauses, and_clauses, dual_clauses
    from random import randrange
    from ivy_art import AnalysisGraph
    from ivy_interp import State
    
    #with self.ui_parent.run_context():
    if True:
        ivy_isolate.create_isolate(None, **{'ext':'ext'}) # construct the nondeterministic choice between actions action
        
        ag = ivy_art.AnalysisGraph()

        pre = State()
        pre.clauses = and_clauses(*[prestate_clauses])

        action = im.module.actions['ext']
        with EvalContext(check=False): # don't check safety
            post = ag.execute(action, pre, None, 'ext')
        post.clauses = ilu.true_clauses()

        to_test =  [poststate_clauses]

        while len(to_test) > 0:            
            conj = to_test.pop(0)
            assert conj.is_universal_first_order()
            used_names = frozenset(x.name for x in il.sig.symbols.values())
            def witness(v):
                c = lg.Const('@' + v.name, v.sort)
                assert c.name not in used_names
                return c        
            
        
            clauses = dual_clauses(conj, witness)
            history = ag.get_history(post)            
                
            _get_model_clauses = lambda clauses, final_cond=False: get_small_model(
                clauses,
                sorted(il.sig.sorts.values()),
                [],
                final_cond = final_cond
            )
            
            #res = ag.bmc(post, clauses, None, None, _get_model_clauses)
            res = ag.bmc(post, clauses)

            if res is not None:                
                assert len(res.states) == 2
                return res.states                
            else:
                return None

# return None or a new proof obligation
def check_transformability_to_violation(summaries_by_symbol, proof_obligation):
    prestate_summary = summaries_by_symbol["inv"]
    countertransition = check_any_exported_action_transition(prestate_summary, proof_obligation)
    
    if countertransition is None:
        print "Valid!"
        return None
    
    
    print "Not valid!"
    prestate = countertransition[0]
    # TODO: ask Oded about it (correctness, efficiency)
    mod = ivy_solver.get_model_clauses(prestate.clauses)
    assert mod != None
    diagram = ivy_solver.clauses_model_to_diagram(prestate_summary, model=mod)
    print "Diagram:", diagram
    #return diagram
    
def check_not_error_safety():
    pass

def infer_safe_summaries():
    initial_summary = PredicateSummary("inv", ivy_logic_utils.true_clauses())
    res = pdr(initial_summary, check_not_error_safety, check_transformability_to_violation)
    print res

def main():
    ivy.read_params()
    iu.set_parameters({'mode':'induction'})
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        with utl.ErrorPrinter():
            ivy.source_file(sys.argv[1],ivy.open_read(sys.argv[1]),create_isolate=False)
            infer_safe_summaries()
    print "OK"


if __name__ == "__main__":
    main()