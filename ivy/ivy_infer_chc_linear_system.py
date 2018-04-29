#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy_utils as utl
import ivy_utils as iu
import ivy_module as im
import ivy_art
import ivy_interp
import ivy_isolate

import ivy_logic_utils

import sys
import logging

import ivy_init

from ivy_infer import ClausesClauses
import ivy_infer
import ivy_linear_pdr
import ivy_interp as itp
import ivy_infer_universal

import datetime

logger = logging.getLogger(__file__)

# TODO: eliminate duplication with ivy_infer_global_invariant
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



def check_tr_implication(prestate_clauses, action1, action2):
    import ivy_transrel
    return ivy_transrel.check_tr_implication(prestate_clauses,
                                             action_update(action1), action_update(action2),
                                             get_domain())


    #####################################################################

    from ivy_interp import EvalContext
    import ivy_module as im
    from ivy_logic_utils import and_clauses, dual_clauses
    from ivy_interp import State

    ag = ivy_art.AnalysisGraph()
    pre = State()
    pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list())
    pre.clauses = and_clauses(pre.clauses, ivy_all_axioms())
    # relies on the isolate being created with 'ext' action
    with EvalContext(check=False):
        post = ag.execute(action2, pre, None, 'ext')

    res = ag.bmc(post, after_action2)

    return res is None

def get_domain():
    return ivy_art.AnalysisGraph().domain

def action_update(action):
    pre = ivy_interp.State()
    return action.update(get_domain(), pre.in_scope)

def test_tr_implication():
    import ivy_actions
    ivy_actions.set_determinize(False)
    # action_disjunction = ivy_actions.join_action(action_update(im.module.actions['ext:send']),
    #                                              action_update(im.module.actions['ext:receive']),
    #                                              get_domain())
    action_disjunction = ivy_actions.ChoiceAction(im.module.actions['ext:send'],
                                                  im.module.actions['ext:receive'])

    is_subsumed = check_tr_implication(ClausesClauses([ivy_logic_utils.true_clauses()]),
                                       im.module.actions['ext:send'],
                                       action_disjunction)
    assert is_subsumed

    is_subsumed = check_tr_implication(ClausesClauses([ivy_logic_utils.true_clauses()]),
                                       action_disjunction,
                                       im.module.actions['ext:send'])
    assert not is_subsumed

    is_subsumed = check_tr_implication(ClausesClauses([ivy_logic_utils.true_clauses()]),
                                       im.module.actions['ext:receive2'],
                                       im.module.actions['ext:receive'])
    assert is_subsumed

    assert False, "Success"


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


def check_action_transition(prestate_clauses, action_name, poststate_obligation):
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

        with EvalContext(check=False):
            post = ag.execute_action(action_name, pre, None)

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

class SafetyOfStateClause(ivy_linear_pdr.LinearSafetyConstraint):
    def __init__(self, pred):
        super(SafetyOfStateClause, self).__init__(pred, ivy_logic_utils.true_clauses())

    def check_satisfaction(self, summaries_by_pred):
        inv_summary = summaries_by_pred[self._lhs_pred].get_summary()
        conjectures_to_verify = [ivy_logic_utils.formula_to_clauses(lc.formula) for lc in im.module.labeled_conjs]

        for conjecture in conjectures_to_verify:
            bad_clauses = ivy_logic_utils.dual_clauses(conjecture)
            inv_but_bad_clauses = ClausesClauses(inv_summary.get_conjuncts_clauses_list() + [bad_clauses])
            bad_inv_model = inv_but_bad_clauses.get_model()
            if bad_inv_model is None:
                continue

            return ivy_infer.PdrCexModel(bad_inv_model, inv_but_bad_clauses.to_single_clauses())

        return None

class SummaryPostSummaryClause(ivy_linear_pdr.LinearMiddleConstraint):
    def __init__(self, lhs_pred, edge_action_name, rhs_pred):
        super(SummaryPostSummaryClause, self).__init__(lhs_pred, edge_action_name, rhs_pred)
        self._edge_action_name = edge_action_name

    def check_transformability(self, summaries_by_pred, bad_clauses):
        prestate_summary = summaries_by_pred[self._lhs_pred].get_summary()

        proof_obligation = ivy_logic_utils.dual_clauses(bad_clauses)

        logger.debug("Checking edge (%s, %s, %s): %s in prestate guarantees %s in poststate?",
                     self._lhs_pred, self._edge_action_name, self._rhs_pred,
                     prestate_summary, proof_obligation)

        countertransition = check_action_transition(prestate_summary,
                                                    self._edge_action_name,
                                                    ClausesClauses([proof_obligation]))

        if countertransition is None:
            logger.debug("Proof obligation guaranteed by prestate invariant")
            return None

        prestate = countertransition[0]
        return ivy_infer.PdrCexModel(None, prestate.clauses)

    def generalize_intransformability(self, prestate_summaries, lemma):
        import ivy_transrel
        from ivy_logic_utils import and_clauses
        from ivy_interp import State

        prestate_clauses = prestate_summaries[self._lhs_pred].get_summary()

        # relying on isolate context created earlier
        ag = ivy_art.AnalysisGraph()

        pre = State()
        pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list())

        action = im.module.actions[self._edge_action_name]

        post = ivy_logic_utils.dual_clauses(lemma)

        axioms = ivy_all_axioms()
        NO_INTERPRETED = None
        res = ivy_transrel.forward_interpolant(pre.clauses, action.update(ag.domain, pre.in_scope), post, axioms,
                                               NO_INTERPRETED)
        assert res != None
        return res[1]


def infer_safe_summaries():
    states = ["tag_server", "tag_grant", "tag_client", "tag_unlock"]
    init = [("tag_grant", global_initial_state())]
    edges = [
        ("tag_server", "tag_grant", 'ext:recv_lock'),
        ("tag_grant", "tag_client", 'ext:recv_grant'),
        ("tag_client", "tag_unlock", 'ext:unlock'),
        ("tag_unlock", "tag_server", 'ext:recv_unlock'),
        #
        ("tag_server", "tag_server", 'ext:lock'),
        ("tag_grant", "tag_grant", 'ext:lock'),
        ("tag_client", "tag_client", 'ext:lock'),
        ("tag_unlock", "tag_unlock", 'ext:lock')
    ]

    mid = [SummaryPostSummaryClause(s1, action, s2) for (s1, s2, action) in edges]
    end = [SafetyOfStateClause(s) for s in states]

    pdr_elements_global_invariant = ivy_linear_pdr.LinearPdr(states, init, mid, end,
                                                             ivy_infer_universal.UnivGeneralizer())
    is_safe, frame_or_cex = ivy_infer.pdr(pdr_elements_global_invariant)
    if not is_safe:
        print "Possibly not safe! - bug or no universal invariant"
    else:
        safe_frame = frame_or_cex
        for state, summary in safe_frame.iteritems():
            logging.info("Summary of %s: %s", state, summary.get_summary())

        # TODO: algorithm for minimization?
        # invariant = safe_frame["inv"].get_summary()
        # logger.info("Invariant: %s. Time: %s", invariant, datetime.datetime.now())
        # logger.info("Invariant as a single formula: %s", invariant.to_single_clauses())
        # assert check_any_exported_action_transition(invariant, invariant) is None
        #
        # invariant_reduced_equiv = minimize_invariant(invariant.get_conjuncts_clauses_list(),
        #                                              lambda candidate, omitted: check_logical_implication(candidate,
        #                                                                                                   [omitted]))
        # assert ivy_solver.clauses_list_imply_list(invariant_reduced_equiv,
        #                                           invariant.get_conjuncts_clauses_list())
        # assert ivy_solver.clauses_list_imply_list(invariant.get_conjuncts_clauses_list(),
        #                                           invariant_reduced_equiv)
        # logger.info("Invariant reduced (logical equivalence): %s", invariant_reduced_equiv)
        #
        # invariant_reduced = minimize_invariant(invariant_reduced_equiv,
        #                                        lambda candidate_lst, omitted: check_inductive_invariant(candidate_lst))
        # print "Invariant reduced:", invariant_reduced


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