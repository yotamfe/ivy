#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
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

import ivy_logic_utils

import sys
import logging

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)

logger = logging.getLogger(__file__)

import ivy_infer
from ivy_infer import ClausesClauses
import ivy_infer_universal

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

def check_any_exported_action_transition(prestate_clauses, poststate_obligation):
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
   
    if True:
        ivy_isolate.create_isolate(None, **{'ext':'ext'}) # construct the nondeterministic choice between actions action
       
        ag = ivy_art.AnalysisGraph()

        pre = State()
        pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list())


        action = im.module.actions['ext']
        with EvalContext(check=False): # don't check safety
            post = ag.execute(action, pre, None, 'ext')
        post.clauses = ilu.true_clauses()

        to_test =  poststate_obligation.get_conjuncts_clauses_list()

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
   
class PdrCmeGlobalInvariant(ivy_infer_universal.UnivPdrElements):
    def initial_summary(self):
        return ivy_infer.PredicateSummary("inv", global_initial_state())
    
    def check_summary_safety(self, summaries):
        inv_summary = summaries["inv"].get_summary()
        bad_clauses = ivy_logic_utils.to_clauses('cme(I)')
       
        inv_but_bad_clauses = ClausesClauses(inv_summary.get_conjuncts_clauses_list() + [bad_clauses])
        bad_inv_model = inv_but_bad_clauses.get_model()
        if bad_inv_model is None:
            return None
       
        return self._bad_model_to_proof_obligation(inv_but_bad_clauses, bad_clauses, bad_inv_model)
    
    def check_transformability_to_violation(self, summaries_by_symbol, proof_obligation):
        prestate_summary = summaries_by_symbol["inv"].get_summary()
       
        logger.debug("Single invariant: checking if %s in prestate guarantees %s in poststate", prestate_summary, proof_obligation)
       
        countertransition = check_any_exported_action_transition(prestate_summary, ClausesClauses([proof_obligation]))
       
        if countertransition is None:
            logger.debug("check single invariant transformability: proof obligation guaranteed by prestate invariant")
            return None
       
        prestate = countertransition[0]
        return self._bad_model_to_proof_obligation(ClausesClauses([prestate.clauses]), 
                                                  ivy_logic_utils.dual_clauses(proof_obligation), 
                                                  None)
        
    def generalize_intransformability(self, prestate_summaries, poststate_clauses):
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
       
        prestate_clauses = prestate_summaries["inv"].get_summary()
     
        ivy_isolate.create_isolate(None, **{'ext':'ext'}) # construct the nondeterministic choice between actions action
            
        ag = ivy_art.AnalysisGraph()
     
        pre = State()
        pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list())
        
        action = im.module.actions['ext']
        
        post = ivy_logic_utils.dual_clauses(poststate_clauses)
        
        axioms = im.module.background_theory()
        NO_INTERPRETED = None
        res = ivy_transrel.forward_interpolant(pre.clauses, action.update(ag.domain,pre.in_scope),post,axioms,NO_INTERPRETED)
        assert res != None
        return res[1]
    
    
def infer_safe_summaries():
    res = ivy_infer.pdr(PdrCmeGlobalInvariant())
    if res is None:
        print "Not safe!"
    else:
        invariant = res["inv"].get_summary()
        print "Invariant:", invariant
        print "Invariant as a single formula:", invariant.to_single_clauses()
        assert check_any_exported_action_transition(invariant, invariant) is None
        
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