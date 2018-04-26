#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import logging

import ivy_infer
import ivy_logic_utils
import ivy_solver

logger = logging.getLogger(__file__)

class UnivPdrElements(ivy_infer.PdrElements):
    def __updr_generalize_bad_model(self, clauses_clauses, bad_model):
        logger.debug("clauses for diagram: %s", clauses_clauses)
        logger.debug("As a single clauses: %s", clauses_clauses.to_single_clauses())
        diagram = ivy_solver.clauses_model_to_diagram(clauses_clauses.to_single_clauses(), model=bad_model)
        logger.debug("calculated diagram of bad state: %s", diagram)
        return diagram
    
    # def _bad_model_to_proof_obligation(self, clauses_clauses, core_wrt_clauses, bad_model):
    def _bad_model_to_proof_obligation(self, bad_model):
        # block_model_clauses = ivy_logic_utils.dual_clauses(self.__updr_generalize_bad_model(clauses_clauses, bad_model))
        block_model_clauses = ivy_logic_utils.dual_clauses(self.__updr_generalize_bad_model(bad_model.clauses_clauses, bad_model.bad_model))
        return block_model_clauses