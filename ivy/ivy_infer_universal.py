#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import logging

import ivy_logic_utils

logger = logging.getLogger(__file__)

class UnivGeneralizer(object):
    def __init__(self):
        super(UnivGeneralizer, self).__init__()

    def bad_model_to_proof_obligation(self, bad_model):
        block_model_clauses = ivy_logic_utils.dual_clauses(bad_model.diagram_abstraction())
        logging.debug("block model clauses: %s", block_model_clauses)
        return block_model_clauses