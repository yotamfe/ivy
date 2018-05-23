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
import ivy_linear_pdr
import ivy_infer_chc_linear_system
import ivy_transrel


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


def global_consecution_clause():
    # relies on the isolate being created with 'ext' action
    return ivy_infer_chc_linear_system.SummaryPostSummaryClause("inv", ('ext', ivy_logic_utils.true_clauses()), "inv")

def global_safety_clauses_lst():
    return [ivy_logic_utils.formula_to_clauses(lc.formula) for lc in im.module.labeled_conjs]

def global_safety_clause():
    return ivy_infer_chc_linear_system.SafetyOfStateClause("inv", global_safety_clauses_lst())


def check_logical_implication(clauses_lst1, clauses_lst2):
    is_implied_per_clause = ivy_solver.clauses_list_imply_list(clauses_lst1,
                                                               clauses_lst2)
    return all(is_implied_per_clause)

def check_inductive_invariant(candidate_lst_clauses):
    candidate_summary = ivy_infer.PredicateSummary("inv", candidate_lst_clauses)
    as_summaries_map = {"inv" : candidate_summary}

    is_init_contained = check_logical_implication([global_initial_state()],
                                                  candidate_lst_clauses)

    is_inductive_per_clause = [global_consecution_clause().check_transformability(as_summaries_map,
                                                                                ivy_logic_utils.dual_clauses(clause_from_candidate)) is None
                                for clause_from_candidate in candidate_lst_clauses]
    is_inductive = all(is_inductive_per_clause)
    is_safe = (global_safety_clause().check_satisfaction(as_summaries_map) is None)
    return is_init_contained and is_inductive and is_safe

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

def tr_of_all_exported_actions():
    from ivy_interp import State

    ag = ivy_art.AnalysisGraph()

    pre = State()

    # relying on the isolate being created with 'ext' action
    action = im.module.actions['ext']
    update = action.update(ag.domain, pre.in_scope)

    axioms = ivy_all_axioms()

    return ivy_transrel.forward_image(ivy_logic_utils.true_clauses(),axioms,update)


def infer_safe_summaries():
    init = [("inv", global_initial_state())]
    mid = [global_consecution_clause()]
    end = [global_safety_clause()]

    pdr_elements_global_invariant = ivy_linear_pdr.LinearPdr(["inv"], init, mid, end,
                                                             ivy_infer_universal.UnivGeneralizer(),
                                                             ivy_all_axioms())
    is_safe, frame_or_cex = ivy_infer.pdr(pdr_elements_global_invariant)
    if not is_safe:
        print "Possibly not safe! - bug or no universal invariant"
    else:
        safe_frame = frame_or_cex
        invariant = safe_frame["inv"].get_summary()
        logger.info("Invariant: %s. Time: %s", invariant, datetime.datetime.now())
        logger.info("Invariant as a single formula: %s", invariant.to_single_clauses())
        assert global_safety_clause().check_satisfaction(safe_frame) is None

        invariant_reduced_equiv = minimize_invariant(invariant.get_conjuncts_clauses_list(),
                                                     lambda candidate, omitted: check_logical_implication(candidate,
                                                                                                          [omitted]))
        assert ivy_solver.clauses_list_imply_list(invariant_reduced_equiv,
                                                  invariant.get_conjuncts_clauses_list())
        assert ivy_solver.clauses_list_imply_list(invariant.get_conjuncts_clauses_list(),
                                                  invariant_reduced_equiv)
        logger.info("Invariant reduced (logical equivalence): %s", invariant_reduced_equiv)

        invariant_reduced = minimize_invariant(invariant_reduced_equiv,
                                               lambda candidate_lst, omitted: check_inductive_invariant(candidate_lst))
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