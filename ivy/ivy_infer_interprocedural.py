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
import ivy_infer_universal

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)

logger = logging.getLogger(__file__)

import ivy_actions
import ivy_transrel

def get_signature_symbols():
    sig = ivy_module.module.sig
    sig_symbols = [sym[1] for sym in sig.symbols.items()]
    # including both constants and relations!
    return sig_symbols
    

class ProcedureSummary(object):
    def __init__(self):
        super(ProcedureSummary, self).__init__()
        
        self._update_clauses = ivy_logic_utils.true_clauses()
        
#         sig = ivy_module.module.sig
#         for sym in sig.symbols.items():
#             if sym[0] == 'errorush':
#                 errorush_sym = sym[1]
#                 break
#         no_error_clauses = ivy_logic_utils.dual_clauses(ivy_logic_utils.Clauses([ivy_transrel.new(errorush_sym)]))
#         self._update_clauses = no_error_clauses                                                             
        
    # TODO: override strengthen etc.
        
    def get_updated_vars(self):
        # including both constants and relations!
        return get_signature_symbols()
    
    def get_update_clauses(self):
        return self._update_clauses
    
    def get_precondition(self):
        return ivy_logic_utils.false_clauses() # no precondition

class SummarizedAction(ivy_actions.Action):
    def __init__(self, name, original_action, procedure_summary):
        super(SummarizedAction, self).__init__()
        
        self._procedure_summary = procedure_summary
        
        self._name = name
        
        self._original_action = original_action
        
        if hasattr(original_action,'formal_params'):
            self.formal_params = original_action.formal_params
        if hasattr(original_action,'formal_returns'):
            self.formal_returns = original_action.formal_returns
            
    def name(self):
        return self._name
            
    # Override AST.clone()
    def clone(self,args):
        return SummarizedAction(self._name, self._original_action, 
                                self._procedure_summary)
            
    # Override
    def action_update(self, domain, pvars):
        updated  = self._procedure_summary.get_updated_vars()
        clauses  = self._procedure_summary.get_update_clauses()
        pre      = self._procedure_summary.get_precondition()
        return (updated, clauses, pre)
    
# Used for interpreting the semantics of called procedures by their summary
# Affects ivy_actions.CallAction.get_callee()
class SummarizedActionsContext(ivy_actions.ActionContext):
    def __init__(self, procedure_summaries):
        super(SummarizedActionsContext, self).__init__()
        
        self._procedure_summaries = procedure_summaries
        
    # Override
    def get(self, symbol):
        original_action = ivy_module.find_action(symbol)
        return SummarizedAction(symbol, original_action, 
                                self._procedure_summaries[symbol])
        
def subprocedures_states_iter(ag, state_to_decompose):
    analysis_graph = ag.decompose_state_partially_repsect_context(state_to_decompose)
    
    subprocedures_states = []
    
    # Note: the first state is the initial state, and it is not associated with any action
    for i in xrange(1, len(analysis_graph.states)):
        state = analysis_graph.states[i]
        if state.expr is None:
            continue
        
        action = ivy_interp.eval_action(state.expr.rep)
        
        if isinstance(action, ivy_actions.AssignAction) or \
           isinstance(action, ivy_actions.AssumeAction) or \
           isinstance(action, ivy_actions.AssertAction) or \
           isinstance(action, ivy_actions.HavocAction) or \
           isinstance(action, SummarizedAction):
            continue
        
        if isinstance(action, ivy_actions.CallAction):
            previous_state = analysis_graph.states[i-1]
            subprocedures_states.append((action, previous_state, state))
        
        rec_res = subprocedures_states_iter(ag, state)
        subprocedures_states += rec_res
        
    return subprocedures_states

def clauses_to_new_vocabulary(clauses):
    """"Type of vocabulary used by actions, see ivy_transrel.state_to_action"""
#     ivy_transrel.state_to_action((callee_current_summary.get_updated_vars(), 
#                                         after_state.clauses, 
#                                         callee_current_summary.get_precondition()))[1]
    renaming = dict()
    # Note: not simply iterating over clauses.symbols() because then numerals
    # also get transformed (new_0), which doesn't make much sense
    # TODO: also need to transform the formal arguments? probably yes
    for s in get_signature_symbols():
        renaming[s] = ivy_transrel.new(s)
    return ivy_logic_utils.rename_clauses(clauses, renaming)


def hide_callers_local_variables(clauses, call_action):
    callee_action = call_action.get_callee()
    formals = callee_action.formal_params + callee_action.formal_returns
    symbols_can_be_modified = get_signature_symbols() + formals
    
    unrelated_syms = [s for s in clauses.symbols() 
                        if s not in symbols_can_be_modified and not s.is_numeral()]
    return ivy_transrel.hide_clauses(unrelated_syms, clauses)

    # TODO: MUST TEST this with global variables, local variables, and nested calls
     
def transition_states_to_summary(call_action, before_state, after_state, 
                                 procedure_summaries):
    # TODO: translate formal parameters back before this call
    # TODO: because get_updated_vars() uses them and not the uniquely renamed ones
    # TODO: perhaps rename the rest and keep the names of the formal params?...
    
#     print call_action, before_state, after_state

    callee = call_action.args[0].rep
    callee_current_summary = procedure_summaries[callee] 
    
    after_clauses_locals_hidden = hide_callers_local_variables(after_state.clauses, call_action)
    before_clauses_locals_hidden = hide_callers_local_variables(before_state.clauses, call_action)
    
    after_clauses_locals_hidden_new_vocab = clauses_to_new_vocabulary(after_clauses_locals_hidden) 
    
    return ivy_transrel.conjoin(before_clauses_locals_hidden,
                                after_clauses_locals_hidden_new_vocab) 
                                        
                
def infer_safe_summaries():
    procedure_summaries = {}
    
    actions_dict = ivy_module.module.actions
    for name, ivy_action in actions_dict.iteritems():
        procedure_summaries[name] = ProcedureSummary()
        
    with SummarizedActionsContext(procedure_summaries):
        for name, ivy_action in actions_dict.iteritems():
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
 
            ivy_isolate.create_isolate(None, **{'ext':'ext'}) # construct the nondeterministic choice between actions action
        
            ag = ivy_art.AnalysisGraph()
     
            pre = State()
            #pre.clauses = and_clauses(ivy_logic_utils.true_clauses())
            pre.clauses = ivy_logic_utils.to_clauses('~errorush()')
     
            with EvalContext(check=False): # don't check safety
                post = ag.execute(ivy_action, pre, None, name)
                #print "Po", name, ":", post.clauses 
                 
                to_test =  [ivy_logic_utils.to_clauses('~errorush()')]
 
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
                        subprocs_states = subprocedures_states_iter(ag, res.states[1])
                        for call_action, before_state, after_state in subprocs_states:
                            print transition_states_to_summary(call_action, before_state, after_state, 
                                                  procedure_summaries)

                        assert False              
                    else:
                        return None

        
        
class GUPDRElements(ivy_infer_universal.UnivPdrElements):
    def __init__(self, actions_dict):
        super(GUPDRElements, self).__init__()
        
        self._actions_dict = actions_dict
        
    def initial_summary(self):
        procedure_summaries = {}
    
        for name, ivy_action in self._actions_dict.iteritems():
            procedure_summaries[name] = ProcedureSummary()
            
        return procedure_summaries
    
    # Return None if safe or proof obligation otherwise
    def check_summary_safety(self, summaries):
        pass
    
    # Return None or a new proof obligation
    def check_transformability_to_violation(self, predicate, summaries_by_symbol, proof_obligation):
        procedure_name_to_check = predicate
        procedure_summaries = summaries_by_symbol
        
        with SummarizedActionsContext(procedure_summaries):
            pass
    
    def generalize_intransformability(self, predicate, prestate_summaries, poststate_clauses):
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