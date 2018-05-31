#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import abc

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

logger = logging.getLogger(__file__)

import ivy_infer
from ivy_infer import ClausesClauses
import ivy_infer_universal
import ivy_solver
import ivy_transrel

# TODO: remove from this module
def ivy_all_axioms():
    axioms_lst = [ivy_logic_utils.formula_to_clauses(lc.formula) for lc in im.module.labeled_axioms]
    if axioms_lst:
        return ivy_logic_utils.and_clauses(*axioms_lst)
    # and_clauses on an empty list causes problems, later fails in clauses_using_symbols
    return ivy_logic_utils.true_clauses()

# TODO: based on ivy_transrel.forward_image_map
def forward_clauses(clauses, updated):
    return ivy_transrel.rename_clauses(clauses, dict((x, ivy_transrel.new(x)) for x in updated))

def to_current_clauses(clauses, updated):
    return ivy_transrel.rename_clauses(clauses, dict((ivy_transrel.new(x), x) for x in updated))

class LinearTransformabilityHornClause(object):
    """
    Transformability clauses = Predicate on lhs.
    """

    __metaclass__ = abc.ABCMeta

    def __init__(self, lhs_pred):
        self._lhs_pred = lhs_pred
        # self._lhs_constraint = lhs_constraint

    def lhs_pred(self):
        return self._lhs_pred

    # def lhs_assigned(self, summaries_by_pred):
    #     lhs_summary = summaries_by_pred[self._lhs_pred]
    #     substitute_lhs_summary = ivy_logic_utils.and_clauses(*lhs_summary.get_summary().get_conjuncts_clauses_list())
    #     return ivy_transrel.conjoin(substitute_lhs_summary, self._lhs_constraint)

class LinearSafetyConstraint(LinearTransformabilityHornClause):
    __metaclass__ = abc.ABCMeta

    def __init__(self, lhs_pred, lhs_constraint):
        super(LinearSafetyConstraint, self).__init__(lhs_pred)

    @abc.abstractmethod
    def check_satisfaction(self, summaries_by_pred):
        pass

class LinearMiddleConstraint(LinearTransformabilityHornClause):
    __metaclass__ = abc.ABCMeta

    def __init__(self, lhs_pred, lhs_constraint, rhs_pred):
        super(LinearMiddleConstraint, self).__init__(lhs_pred)
        self._rhs_pred = rhs_pred
        self._lhs_constraint = lhs_constraint

    def rhs_pred(self):
        return self._rhs_pred

    @abc.abstractmethod
    def check_transformability(self, summaries_by_pred, bad_clauses):
        pass

    @abc.abstractmethod
    def generalize_intransformability(self, summaries_by_pred, lemma):
        pass

    @abc.abstractmethod
    def transformability_update(self, summaries_by_pred, rhs_vocab):
        pass

class LinearPdr(ivy_infer.PdrElements):
    def __init__(self, preds, init_chc_lst, mid_chc_lst, end_chc_lst, generalizer, axioms):
        super(LinearPdr, self).__init__(generalizer)
        self._preds = preds

        self._init_chc = init_chc_lst
        self._mid_chc = mid_chc_lst
        self._end_chc = end_chc_lst

        self._axioms = axioms

        self._failed_push_cache = set()

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
        for pred in prev_summaries:
            prev_clauses_lst = prev_summaries[pred].get_summary().get_conjuncts_clauses_list()
            current_clauses_lst = current_summaries[pred].get_summary().get_conjuncts_clauses_list()

            for clauses in prev_clauses_lst:
                if clauses in current_clauses_lst:
                    continue

                is_guaranteed_by_pre = self.check_intransformability_to_violation_bool_res(pred, prev_summaries, clauses)
                if not is_guaranteed_by_pre:
                    continue

                logging.debug("Pushing to next frame for %s: %s", pred, clauses)
                current_summaries[pred].strengthen(clauses)

        return current_summaries

    def _push_to_other_preds(self, pred, prev_summaries, current_summaries, current_bound):
        # if not PUSH_TO_OTHER_PREDS
        # return current_summaries # TODO: remove

        outgoing_edges_targets = set(midc.rhs_pred() for midc in self._mid_chc if midc.lhs_pred() == pred)
        for target_pred in outgoing_edges_targets:
            for lemma in current_summaries[pred].get_summary().get_conjuncts_clauses_list():
                if current_summaries[target_pred].get_summary().has_conjunct(lemma):
                    continue
                if (target_pred, current_bound, lemma) in self._failed_push_cache:
                    # heuristic not to check the same failed lemma many times
                    logger.debug("Pushing cache hit: %s => %s of %s in %d", pred, target_pred, lemma, current_bound)  # TODO: remove
                    continue
                logger.debug("Pushing cache miss: %s => %s of %s in %d", pred, target_pred, lemma, current_bound) # TODO: remove
                is_guaranteed_by_pre = self.check_intransformability_to_violation_bool_res(target_pred, prev_summaries, lemma)
                if not is_guaranteed_by_pre:
                    logger.debug("Could not push between predicates %s => %s: %s, frame %d", pred, target_pred, lemma, current_bound)
                    self._failed_push_cache.add((target_pred, current_bound, lemma))
                    continue

                logger.debug("Pushing between predicates %s => %s: %s", pred, target_pred, lemma)
                current_summaries[target_pred].strengthen(lemma)

        return current_summaries

    def check_summary_safety(self, summaries, prev_summaries=None, current_bound=None):
        proof_obligations = []
        for safety_constraint in self._end_chc:
            bad_model = safety_constraint.check_satisfaction(summaries)
            if bad_model is None:
                logger.debug("%s is satisfied" % str(safety_constraint))
                # TODO: does it make sense here, pushing might eliminate some cexs previously obtained..
                if prev_summaries is not None:
                    self._push_to_other_preds(safety_constraint.lhs_pred(), prev_summaries, summaries, current_bound)
                continue

            logger.debug("Counterexample to %s", str(safety_constraint))
            proof_obligation = self._generalizer.bad_model_to_proof_obligation(bad_model)
            proof_obligations.append((safety_constraint,
                                      [(safety_constraint.lhs_pred(), proof_obligation)]))

        return proof_obligations

    def check_intransformability_to_violation_bool_res(self, predicate, summaries_by_symbol, proof_obligation):
        # return not self.check_transformability_to_violation(predicate, summaries_by_symbol, proof_obligation)

        all_transformability_combined, all_updated_syms, _ = self._unified_transformability_update(predicate, summaries_by_symbol)

        rhs = ivy_logic_utils.dual_clauses(proof_obligation)
        rhs_in_new = forward_clauses(rhs, all_updated_syms)

        vc = ClausesClauses([all_transformability_combined, rhs_in_new, self._axioms])
        cex = vc.get_model()
        if cex is None:
            return True
        return False

    def check_transformability_to_violation(self, predicate, summaries_by_symbol, proof_obligation):
        # proof_obligations = []
        #
        # for mid_constraint in self._mid_chc:
        #     if mid_constraint.rhs_pred() != predicate:
        #         continue
        #
        #     logging.debug("Proof obligation: %s", proof_obligation)
        #     bad_model_lhs = mid_constraint.check_transformability(summaries_by_symbol,
        #                                                           ivy_logic_utils.dual_clauses(proof_obligation))
        #     if bad_model_lhs is None:
        #         continue
        #
        #     proof_obligation = self._generalizer.bad_model_to_proof_obligation(bad_model_lhs)
        #     pre_pred = mid_constraint.lhs_pred()
        #     proof_obligations.append((mid_constraint, [(pre_pred, proof_obligation)]))
        #
        # return proof_obligations

        all_transformability_combined, all_updated_syms, transformers = self._unified_transformability_update(predicate,
                                                                                                              summaries_by_symbol)

        rhs = ivy_logic_utils.dual_clauses(proof_obligation)
        rhs_in_new = forward_clauses(rhs, all_updated_syms)

        vc = ClausesClauses([all_transformability_combined, rhs_in_new, self._axioms])
        cex = vc.get_model()
        if cex is None:
            return []

        causing_constraint_idx = ivy_logic_utils.find_true_disjunct(all_transformability_combined,
                                                                    cex.eval)
        causing_constraint = transformers[causing_constraint_idx]
        pre_pred = causing_constraint.lhs_pred()
        ############# TODO: remove
        bad_model_lhs = causing_constraint.check_transformability(summaries_by_symbol, ivy_logic_utils.dual_clauses(proof_obligation)) # TODO: remove
        assert bad_model_lhs is not None
        #############

        # causing_updated_syms, causing_transform_clauses = causing_constraint.transformability_update(summaries_by_symbol,
        #                                                                                              ivy_transrel.new)
        # rhs_in_new_for_causing = forward_clauses(rhs, causing_updated_syms)
        # bad_model_lhs = ivy_infer.PdrCexModel(cex,
        #                                       ClausesClauses([causing_transform_clauses,
        #                                                      rhs_in_new_for_causing]).to_single_clauses(),
        #                                       project_pre=True)

        proof_obligation = self._generalizer.bad_model_to_proof_obligation(bad_model_lhs)
        logging.debug("Proof obligation: %s", proof_obligation)

        logger.debug("Check transformability returned proof obligation: %s", [(causing_constraint, [(pre_pred, proof_obligation)])])
        return [(causing_constraint, [(pre_pred, proof_obligation)])]

    def mark_reachable(self, predicate, summary_proof_obligation,
                       summaries, cex_info):
        pass

    def is_known_to_be_reachable(self, predicate, summary_proof_obligation,
                                 summaries):
        return False, None

    def generalize_intransformability(self, predicate, prestate_summaries, lemma):
        all_transformability_combined, all_updated_syms, _ = self._unified_transformability_update(predicate, prestate_summaries)

        rhs = ivy_logic_utils.dual_clauses(lemma)
        rhs_in_new = forward_clauses(rhs, all_updated_syms)

        logger.debug("GEN0: %s", all_updated_syms)
        logger.debug("GEN0.1: %s", rhs_in_new)
        logger.debug("Trans: %s, check lemma: %s" % (all_transformability_combined, rhs_in_new))
        # TODO: use forward_interpolant or forward_image_map instead?
        res = ivy_transrel.interpolant(all_transformability_combined,
                                       rhs_in_new,
                                       axioms=self._axioms, interpreted=None)
        # res = ivy_transrel.forward_interpolant(all_transformability_combined,
        #                                        rhs,
        #                                        axioms=self._axioms, interpreted=None)
        assert res is not None
        logger.debug("GEN1: %s", res[1])
        logger.debug("GEN2: %s", to_current_clauses(res[1], all_updated_syms))
        generalization = to_current_clauses(res[1], all_updated_syms)
        # generalization = res[1]

        # TODO: assert (in debug) that it is unreachable from previous frame, in any way
        # for transformer in transformers:
        #     is_transformable = transformer.check_transformability(prestate_summaries,
        #                                                           ivy_logic_utils.dual_clauses(generalization))
        #     if is_transformable is not None:
        #         logger.info(str(transformer))
        #         is_res_actually_unsat = ClausesClauses([all_transformability_combined, ivy_logic_utils.dual_clauses(res[1])]).get_model()
        #         logger.info("is res unsat: %s", is_res_actually_unsat is None)
        #         is_gen_actually_unsat = ClausesClauses([all_transformability_combined, forward_clauses(ivy_logic_utils.dual_clauses(generalization), all_updated_syms)]).get_model()
        #         logger.info("is gen unsat: %s", is_gen_actually_unsat is None)
        #         logger.debug("Trans vocab of this action: %s", transformer.transformability_update(prestate_summaries, ivy_transrel.new))
        #         assert False
        return generalization


        # # TODO: generalizing separately and then combining is potentially less efficient becauase of different local minima of the unsat core
        # lemma_generalization = ivy_logic_utils.false_clauses()
        #
        # for mid_constraint in self._mid_chc:
        #     if mid_constraint.rhs_pred() != predicate:
        #         continue
        #
        #     generalization_for_clause = mid_constraint.generalize_intransformability(prestate_summaries, lemma)
        #     # NOTE: taking care with the disjunction to rename implicitly universally quantified variables
        #     # to avoid capture between different disjuncts (each is quantified separately).
        #     # Inserting the quantifiers explicitly causes problems elsewhere, in ivy_solver.clauses_model_to_clauses
        #     lemma_generalization = ivy_logic_utils.or_clauses_avoid_clash2(lemma_generalization,
        #                                                                    generalization_for_clause)
        #
        # return lemma_generalization

    def _unified_transformability_update(self, predicate, prestate_summaries):
        transformers = filter(lambda midc: midc.rhs_pred() == predicate, self._mid_chc)
        transformability_clauses = map(lambda midc: midc.transformability_update(prestate_summaries, ivy_transrel.new),
                                       transformers)
        all_updated_syms = set.union(*(set(updated_syms) for (updated_syms, _) in transformability_clauses))
        transformability_clauses_unified = []
        for (updated_syms, clauses) in transformability_clauses:
            unchanged_equal = ivy_transrel.diff_frame(updated_syms, all_updated_syms,
                                                      im.module.relations, ivy_transrel.new)
            clauses = ivy_transrel.conjoin(clauses, unchanged_equal)
            transformability_clauses_unified.append(clauses)
        # all_transformability_combined = ivy_logic_utils.or_clauses_with_tseitins_avoid_clash(*transformability_clauses_unified)
        all_transformability_combined = ivy_logic_utils.tagged_or_clauses('__edge', *transformability_clauses_unified)
        # all_transformability_combined = ivy_logic_utils.or_clauses(*transformability_clauses_unified)
        return all_transformability_combined, all_updated_syms, transformers
