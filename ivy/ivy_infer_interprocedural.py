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

import ivy_logic_utils

import sys
import logging

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)

logger = logging.getLogger(__file__)

import ivy_actions

class ProcedureSummary(object):
    def __init__(self):
        super(ProcedureSummary, self).__init__()
        
        self._update_clauses = ivy_logic_utils.true_clauses()
        
    def get_updated_vars(self):
        return None # everything might be changed by the action
    
    def get_update_clauses(self):
        return self._update_clauses
    
    def get_precondition(self):
        return ivy_logic_utils.false_clauses() # no precondition

class SummarizedAction(ivy_actions.Action):
    def __init__(self, name, original_action, procedure_summary):
        super(SummarizedAction, self).__init__()
        
        self._procedure_summary = procedure_summary
        
        self.name = name
        
        if hasattr(original_action,'formal_params'):
            self.formal_params = original_action.formal_params
        if hasattr(original_action,'formal_returns'):
            self.formal_returns = original_action.formal_returns
            
    # Override
    def action_update(self, domain, pvars):
        updated  = self._procedure_summary.get_updated_vars()
        clauses  = self._procedure_summary.get_update_clauses()
        pre      = self._procedure_summary.get_precondition()
        return (updated, clauses, pre)
    
class SummarizedActionsContext(ivy_actions.ActionContext):
    def __init__(self, procedure_summaries):
        super(SummarizedActionsContext, self).__init__()
        
        self._procedure_summaries = procedure_summaries
        
    # Override
    def get(self, symbol):
        original_action = ivy_module.find_action(symbol)
        return SummarizedAction(symbol, original_action, 
                                self._procedure_summaries[symbol])
        
def infer_safe_summaries():
    procedure_summaries = {}
    
    actions_dict = im.module.actions
    for name, ivy_action in actions_dict.iteritems():
        procedure_summaries[name] = ProcedureSummary()
        
    with SummarizedActionsContext(procedure_summaries):
        for name, ivy_action in actions_dict.iteritems():
            #print ivy_action.update(None, None)
            pass

        
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