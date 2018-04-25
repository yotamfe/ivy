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

diagnose = iu.BooleanParameter("diagnose", False)
coverage = iu.BooleanParameter("coverage", True)

logger = logging.getLogger(__file__)

import ivy_infer
from ivy_infer import ClausesClauses
import ivy_infer_universal
import ivy_solver
import ivy_transrel


def display_cex(msg, ag):
    print msg
    if diagnose.get():
        ui.ui_main_loop(ag)
    exit(1)


def check_properties():
    if itp.false_properties():
        if diagnose.get():
            print "Some properties failed."
            gui = ui.new_ui()
            gui.tk.update_idletasks()  # so that dialog is on top of main window
            gui.try_property()
            gui.mainloop()
            exit(1)
        raise iu.IvyError(None, "Some properties failed.")
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
                final_cond=final_cond
            )

            # res = ag.bmc(post, clauses, None, None, _get_model_clauses)
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

class Predicate(object):
    def __init__(self, name):
        self._name = name

    def __str__(self):
        return self._name

    def rhs_assigned(self, clauses):
        return ivy_transrel.new(clauses)

# TODO: currently just a wrapper to be used with diagram calls, refactor to extract the diagram from a model
# TODO: hold a model and clauses to be used with get_model_clauses e.g. to project on pre-state
class PdrCexModel(object):
    def __init__(self, clauses_clauses, core_wrt_clauses, bad_model):
        self.clauses_clauses = clauses_clauses
        self.core_wrt_clauses = core_wrt_clauses
        self.bad_model = bad_model

class LinearTransformabilityHornClause(object):
    """
    Transformability clauses = Predicate on lhs.
    """

    def __init__(self, lhs_pred, lhs_constraint):
        self._lhs_pred = lhs_pred
        self._lhs_constraint = lhs_constraint

    def lhs_pred(self):
        return self._lhs_pred

    # def check_transformability(self, summaries_by_pred, bad_clauses):
        # lhs = self.lhs_assigned(summaries_by_pred)
        # rhs = self._rhs_pred.rhs_assigned(bad_clauses)
        # vc = ClausesClauses(lhs, rhs)
        # cex = vc.get_model()
        # if cex is None:
        #     return None

        # return PdrCexModel(cex)

    def lhs_assigned(self, summaries_by_pred):
        lhs_summary = summaries_by_pred[self._lhs_pred]
        substitute_lhs_summary = ivy_logic_utils.and_clauses(*lhs_summary.get_summary().get_conjuncts_clauses_list())
        return ivy_transrel.conjoin(substitute_lhs_summary, self._lhs_constraint)

class LinearSafetyConstraint(LinearTransformabilityHornClause):
    def __init__(self, lhs_pred, lhs_constraint, rhs):
        super(LinearSafetyConstraint, self).__init__(lhs_pred, lhs_constraint)

    def check_satisfaction(self, summaries_by_pred):
        # return self.check_transformability(summaries_by_pred, summaries_by_pred)

        assert self._lhs_pred == "inv"

        inv_summary = summaries_by_pred["inv"].get_summary()
        conjectures_to_verify = [ivy_logic_utils.formula_to_clauses(lc.formula) for lc in im.module.labeled_conjs]

        for conjecture in conjectures_to_verify:
            bad_clauses = ivy_logic_utils.dual_clauses(conjecture)
            inv_but_bad_clauses = ClausesClauses(inv_summary.get_conjuncts_clauses_list() + [bad_clauses])
            bad_inv_model = inv_but_bad_clauses.get_model()
            if bad_inv_model is None:
                continue

            return PdrCexModel(inv_but_bad_clauses, bad_clauses, bad_inv_model)

        return None

class LinearMiddleConstraint(LinearTransformabilityHornClause):
    def __init__(self, lhs_pred, lhs_constraint, rhs_pred):
        super(LinearMiddleConstraint, self).__init__(lhs_pred, lhs_constraint)
        self._rhs_pred = rhs_pred

    def rhs_pred(self):
        return self._rhs_pred

    def check_transformability(self, summaries_by_pred, bad_clauses):
        assert self._rhs_pred == "inv"
        prestate_summary = summaries_by_pred["inv"].get_summary()

        proof_obligation = ivy_logic_utils.dual_clauses(bad_clauses)

        logger.debug("Single invariant: checking if %s in prestate guarantees %s in poststate", prestate_summary,
                     proof_obligation)

        countertransition = check_any_exported_action_transition(prestate_summary, ClausesClauses([proof_obligation]))

        if countertransition is None:
            logger.debug("check single invariant transformability: proof obligation guaranteed by prestate invariant")
            return None

        prestate = countertransition[0]
        return PdrCexModel(ClausesClauses([prestate.clauses]),
                           ivy_logic_utils.dual_clauses(proof_obligation),
                           None)

class LinearPdr(ivy_infer_universal.UnivPdrElements):
    def __init__(self, preds, init_chc_lst, mid_chc_lst, end_chc_lst):
        self._preds = preds

        self._init_chc = init_chc_lst
        self._mid_chc = mid_chc_lst
        self._end_chc = end_chc_lst

    def initial_summary(self):
        initial_summary = {pred: ivy_logic_utils.false_clauses() for pred in self._preds}

        for (pred, init_requirement) in self._init_chc:
            current_init = initial_summary[pred]
            strengthened_init = ivy_logic_utils.or_clauses(init_requirement, current_init)
            initial_summary[pred] = strengthened_init

        return {pred: ivy_infer.PredicateSummary(pred, initial_summary[pred]) for pred in self._preds}

    def top_summary(self):
        return {pred: ivy_infer.PredicateSummary(pred, ivy_logic_utils.true_clauses()) for pred in self._preds}

    def push_forward(self, prev_summaries, current_summaries):
        # for pred in prev_summaries:
        #     prev_clauses_lst = prev_summaries[pred].get_summary().get_conjuncts_clauses_list()
        #     current_clauses_lst = current_summaries[pred].get_summary().get_conjuncts_clauses_list()
        #
        #     for clauses in prev_clauses_lst:
        #         if clauses in current_clauses_lst:
        #             continue
        #
        #         transformability_cex = self.check_transformability_to_violation(pred, prev_summaries, clauses)
        #         if transformability_cex is not None:
        #             continue
        #
        #         logging.debug("Pushing to next frame for %s: %s", pred, clauses)
        #         current_summaries[pred].strengthen(clauses)

        # TODO: resurrect push forward

        return current_summaries

    def check_summary_safety(self, summaries):
        proof_obligations = []
        for safety_constraint in self._end_chc:
            bad_model = safety_constraint.check_satisfaction(summaries)
            if bad_model is None:
                continue

            proof_obligation = self._bad_model_to_proof_obligation(bad_model)
            proof_obligations.append((safety_constraint,
                                      [(safety_constraint.lhs_pred(), proof_obligation)]))

        return proof_obligations

    def check_transformability_to_violation(self, predicate, summaries_by_symbol, proof_obligation):
        proof_obligations = []

        for mid_constraint in self._mid_chc:
            if mid_constraint.rhs_pred() != predicate:
                continue

            bad_model_lhs = mid_constraint.check_transformability(summaries_by_symbol, ivy_logic_utils.dual_clauses(proof_obligation))
            if bad_model_lhs is None:
                continue

            proof_obligation = self._bad_model_to_proof_obligation(bad_model_lhs)
            pre_pred = mid_constraint.lhs_pred()
            proof_obligations.append((mid_constraint, [(pre_pred, proof_obligation)]))

        return proof_obligations

    def mark_reachable(self, predicate, summary_proof_obligation,
                       summaries, cex_info):
        pass

    def is_known_to_be_reachable(self, predicate, summary_proof_obligation,
                                 summaries):
        return False, None

    def generalize_intransformability(self, predicate, prestate_summaries, predicate_lemma):
        transforming_constraints = filter(lambda constraint: constraint.rhs_pred() == predicate,
                                          self._mid_chc)

        combined_lhs_clauses = ivy_logic_utils.or_clauses(*[constraint.lhs_assigned(prestate_summaries)
                                                                for constraint in transforming_constraints])

        poststate_lemma = predicate.rhs_assigned(predicate_lemma)
        poststate_bad = ivy_logic_utils.dual_clauses(poststate_lemma)

        NO_EXTRA_AXIOMS = ivy_logic_utils.true_clauses() # should be part of the constraints
        NO_INTERPRETED = None
        res = ivy_transrel.interpolant(combined_lhs_clauses, poststate_bad, NO_EXTRA_AXIOMS, NO_INTERPRETED)
        assert res is not None, "Failure generalizing blocked lemma: pred %s, %s" % (predicate, predicate_lemma)
        return res[1]

    def check_inductive_invariant(self, candidate):
        candidate_summary = ivy_infer.PredicateSummary("inv", candidate)
        as_summaries_map = {"inv": candidate_summary}
        is_init_contained = check_logical_implication(
            self.initial_summary()["inv"].get_summary().get_conjuncts_clauses_list(),
            candidate)
        is_inductive = check_any_exported_action_transition(candidate_summary.get_summary(),
                                                            candidate_summary.get_summary())
        is_safe = self.check_summary_safety(as_summaries_map) == []
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


# def tr_of_all_exported_actions():
#     from ivy_interp import State
#
#     ag = ivy_art.AnalysisGraph()
#
#     pre = State()
#
#     # relying on the isolate being created with 'ext' action
#     action = im.module.actions['ext']
#     action.update(ag.domain, pre.in_scope)


def infer_safe_summaries():
    init = [("inv", global_initial_state())]
    # TODO: currently hard coded in the predicate, add flexibility
    mid = [LinearMiddleConstraint("inv", None, "inv")]
    end = [LinearSafetyConstraint("inv", ivy_logic_utils.true_clauses(), None)]

    pdr_elements_global_invariant = LinearPdr(["inv"], init, mid, end)
    is_safe, frame_or_cex = ivy_infer.pdr(pdr_elements_global_invariant)
    if not is_safe:
        print "Possibly not safe! - bug or no universal invariant"
    else:
        safe_frame = frame_or_cex
        invariant = safe_frame["inv"].get_summary()
        logger.info("Invariant: %s", invariant)
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
        print "Invariant reduced:", invariant_reduced_equiv


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