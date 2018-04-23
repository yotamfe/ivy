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

import ivy_init
import ivy_ast

import datetime

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)

logger = logging.getLogger(__file__)

import ivy_infer
from ivy_infer import ClausesClauses
import ivy_infer_universal
import ivy_solver

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
    # see ivy_check.summarize_isolate()
    with im.module.copy():
        with itp.EvalContext(check=False):
            ag = ivy_art.AnalysisGraph(initializer=lambda x: None)
            assert len(ag.states) == 1
            history = ag.get_history(ag.states[0])
            initial_state_clauses = history.post
            logger.debug("initial state clauses: %s", initial_state_clauses)
            return initial_state_clauses

def ivy_all_axioms():
    axioms_lst = [ivy_logic_utils.formula_to_clauses(lc.formula) for lc in im.module.labeled_axioms]
    if axioms_lst:
        return ivy_logic_utils.and_clauses(*axioms_lst)
    # and_clauses on an empty list causes problems, later fails in clauses_using_symbols
    return ivy_logic_utils.true_clauses()

def check_any_exported_action_transition(prestate_clauses, poststate_obligation):
    import ivy_logic as il
    import logic as lg
    from ivy_interp import EvalContext
    import ivy_module as im
    import ivy_logic_utils as ilu
    from ivy_solver import get_small_model
    from ivy_logic_utils import and_clauses, dual_clauses
    from ivy_interp import State

    if True:
        # relying on isolate context created earlier
        ag = ivy_art.AnalysisGraph()

        pre = State()
        pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list())
        pre.clauses = and_clauses(pre.clauses, ivy_all_axioms())

        # relies on the isolate being created with 'ext' action
        action = im.module.actions['ext']
        with EvalContext(check=False):
            post = ag.execute(action, pre, None, 'ext')

        post.clauses = ilu.true_clauses()

        to_test = poststate_obligation.get_conjuncts_clauses_list()


        while len(to_test) > 0:
            conj = to_test.pop(0)
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

            # attempt to mimic generalize_intransformability: (29/3/2018)
            # gap is to take only the prestate of the cti and pass it forwards (to the diagram)
            #
            # ag = ivy_art.AnalysisGraph()
            #
            # pre = State()
            # pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list())
            #
            # # relying on the isolate being created with 'ext' action
            # action = im.module.actions['ext']
            #
            # post = ivy_logic_utils.dual_clauses(conj)
            #
            # axioms = ivy_all_axioms()
            # import ivy_transrel
            # pre_and_tr = ivy_transrel.forward_image(pre.clauses, axioms,
            #                                         action.update(ag.domain, pre.in_scope))
            # vc = ClausesClauses([pre_and_tr, post])
            # cti = vc.get_model()
            # if cti is None:
            #     continue
            #
            # return (vc, cti)

            # return None

        # TODO: attempt to mimic the new ivy_check (26/3/2018)
        # while len(to_test) > 0:
        #     conj = to_test.pop(0)
        #     assert conj.is_universal_first_order(), conj
        #     # used_names = frozenset(x.name for x in il.sig.symbols.values())
        #     # def witness(v):
        #     #     c = lg.Const('@' + v.name, v.sort)
        #     #     assert c.name not in used_names
        #     #     return c
        #
        #     # clauses_to_check = dual_clauses(conj, witness)
        #     clauses_to_check = dual_clauses(conj)
        #
        #     # based on ivy_check.check_fcs_in_state()
        #     history = ag.get_history(post)
        #     clauses = history.post
        #     clauses = ivy_logic_utils.and_clauses(clauses, im.module.background_theory())
        #     model = ivy_transrel.small_model_clauses(clauses, final_cond=clauses_to_check, shrink=True)
        #     if model is None:
        #         continue
        #
        #     # based on ivy_check.MatchHandler.__init__
        #     prestate_model_clauses = ivy_solver.clauses_model_to_clauses(clauses, model=model, numerals=True)
        #     return prestate_model_clauses
        #
        # return None

class PdrGlobalInvariant(ivy_infer_universal.UnivPdrElements):
    def initial_summary(self):
        return {"inv": ivy_infer.PredicateSummary("inv", global_initial_state())}
    
    def top_summary(self):
        return {"inv": ivy_infer.PredicateSummary("inv", ivy_logic_utils.true_clauses())}
    
    def push_forward(self, prev_summaries, current_summaries):
        prev_clauses_lst = prev_summaries["inv"].get_summary().get_conjuncts_clauses_list()
        current_clauses_lst = current_summaries["inv"].get_summary().get_conjuncts_clauses_list()

        for clauses in prev_clauses_lst:
            if clauses in current_clauses_lst:
                continue

            transformability_cex = self.check_transformability_to_violation("inv", prev_summaries, clauses)
            if transformability_cex is not None:
                continue

            logging.debug("Pushing to next frame: %s", clauses)
            current_summaries["inv"].strengthen(clauses)

        return current_summaries
    
    def check_summary_safety(self, summaries):
        inv_summary = summaries["inv"].get_summary()
        conjectures_to_verify = [ivy_logic_utils.formula_to_clauses(lc.formula) for lc in im.module.labeled_conjs]

        for conjecture in conjectures_to_verify:
            bad_clauses = ivy_logic_utils.dual_clauses(conjecture)
            inv_but_bad_clauses = ClausesClauses(inv_summary.get_conjuncts_clauses_list() + [bad_clauses])
            bad_inv_model = inv_but_bad_clauses.get_model()
            if bad_inv_model is None:
                continue

            return ("inv",
                    [("inv", self._bad_model_to_proof_obligation(inv_but_bad_clauses, bad_clauses, bad_inv_model))])

        return (None, None)
    
    def check_transformability_to_violation(self, predicate, summaries_by_symbol, proof_obligation):
        assert predicate == "inv"
        prestate_summary = summaries_by_symbol["inv"].get_summary()
       
        logger.debug("Single invariant: checking if %s in prestate guarantees %s in poststate", prestate_summary, proof_obligation)
       
        countertransition = check_any_exported_action_transition(prestate_summary, ClausesClauses([proof_obligation]))
       
        if countertransition is None:
            logger.debug("check single invariant transformability: proof obligation guaranteed by prestate invariant")
            return None
       
        prestate = countertransition[0]
        return [("inv", self._bad_model_to_proof_obligation(ClausesClauses([prestate.clauses]), 
                                                            ivy_logic_utils.dual_clauses(proof_obligation), 
                                                            None))]
        
    def mark_reachable(self, predicate, summary_proof_obligation, 
                       summaries, cex_info):
        pass
    
    def is_known_to_be_reachable(self, predicate, summary_proof_obligation,
                                 summaries):
        return False, None
        
    def generalize_intransformability(self, predicate, prestate_summaries, poststate_clauses):
        import ivy_module as im
        import ivy_transrel
        from ivy_logic_utils import and_clauses
        from ivy_interp import State
        
        assert predicate == "inv"
       
        prestate_clauses = prestate_summaries["inv"].get_summary()

        # relying on isolate context created earlier
        ag = ivy_art.AnalysisGraph()
     
        pre = State()
        pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list())

        # relying on the isolate being created with 'ext' action
        action = im.module.actions['ext']
        
        post = ivy_logic_utils.dual_clauses(poststate_clauses)
        
        axioms = ivy_all_axioms()
        NO_INTERPRETED = None
        res = ivy_transrel.forward_interpolant(pre.clauses, action.update(ag.domain,pre.in_scope),post,axioms,NO_INTERPRETED)
        assert res != None
        return res[1]

    def check_inductive_invariant(self, candidate):
        candidate_summary = ivy_infer.PredicateSummary("inv", candidate)
        as_summaries_map = {"inv" : candidate_summary}
        is_init_contained = check_logical_implication(self.initial_summary()["inv"].get_summary().get_conjuncts_clauses_list(),
                                                      candidate)
        is_inductive = check_any_exported_action_transition(candidate_summary.get_summary(),
                                                            candidate_summary.get_summary())
        is_safe = self.check_summary_safety(as_summaries_map)
        return is_init_contained and is_inductive and is_safe

def check_logical_implication(clauses_lst1, clauses_lst2):
    is_implied_per_clause = ivy_solver.clauses_list_imply_list(clauses_lst1,
                                                               clauses_lst2)
    return all(is_implied_per_clause)

def minimize_invariant(invariant_clauses_iterable, redundancy_checker):
    invariant_clauses_simplified = set(ivy_logic_utils.simplify_clauses(cls)
                                       for cls in invariant_clauses_iterable)

    while True:
        clauses_to_check = set(invariant_clauses_simplified)
        clauses_retained = set()
        reduced_in_this_pass = False

        while clauses_to_check:
            current_clauses = clauses_to_check.pop()

            is_redundant = redundancy_checker(list(clauses_retained | clauses_to_check),
                                              current_clauses)
            if is_redundant:
                reduced_in_this_pass = True
            else:
                clauses_retained.add(current_clauses)

        if not reduced_in_this_pass:
            break

        invariant_clauses_simplified = clauses_retained | clauses_to_check

    return invariant_clauses_simplified


def infer_safe_summaries():
    pdr_elements_global_invariant = PdrGlobalInvariant()
    is_safe, frame_or_cex = ivy_infer.pdr(pdr_elements_global_invariant)
    if not is_safe:
        print "Possibly not safe! - bug or no universal invariant"
    else:
        safe_frame = frame_or_cex
        invariant = safe_frame["inv"].get_summary()
        logger.info("Invariant: %s. Time: %s", invariant, datetime.datetime.now())
        logger.info("Invariant as a single formula: %s", invariant.to_single_clauses())
        assert check_any_exported_action_transition(invariant, invariant) is None

        invariant_reduced_equiv = minimize_invariant(invariant.get_conjuncts_clauses_list(),
                                                     lambda candidate, omitted: check_logical_implication(candidate,
                                                                                                          [omitted]))
        assert ivy_solver.clauses_list_imply_list(invariant_reduced_equiv,
                                                  invariant.get_conjuncts_clauses_list())
        assert ivy_solver.clauses_list_imply_list(invariant.get_conjuncts_clauses_list(),
                                                  invariant_reduced_equiv)
        logger.info("Invariant reduced (logical equivalence): %s", invariant_reduced_equiv)

        invariant_reduced = minimize_invariant(invariant_reduced_equiv,
                                               lambda candidate, omitted:
                                                    pdr_elements_global_invariant.check_inductive_invariant(candidate))
        print "Invariant reduced:", invariant_reduced


def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)
        
def main():
    logging.basicConfig(level=logging.DEBUG)

    import signal
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    import ivy_alpha
    ivy_alpha.test_bottom = False  # this prevents a useless SAT check
    import tk_ui as ui
    iu.set_parameters({'mode': 'induction'})

    ivy_init.read_params()
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1], ivy_init.open_read(sys.argv[1]), create_isolate=False)

            # inspired by ivy_check.check_module()
            isolates = sorted(list(im.module.isolates))
            assert len(isolates) == 1
            isolate = isolates[0]
            with im.module.copy():
                ivy_isolate.create_isolate(isolate, ext='ext')
                infer_safe_summaries()

    print "OK"

if __name__ == "__main__":
    main()