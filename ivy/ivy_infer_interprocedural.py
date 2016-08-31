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

import ivy_infer_universal
import ivy_logic_utils
import ivy_solver
import ivy_infer
import logic
import ivy_logic

import sys
import logging

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)

logger = logging.getLogger(__file__)

import ivy_actions
import ivy_transrel

def zzz_new_no_error_clauses():
    sig = ivy_module.module.sig
    for sym in sig.symbols.items():
        if sym[0] == 'errorush':
            errorush_sym = sym[1]
            break
    no_error_clauses = ivy_logic_utils.dual_clauses(ivy_logic_utils.Clauses([ivy_transrel.new(errorush_sym)]))
    return no_error_clauses

def get_signature_symbols():
    sig = ivy_module.module.sig
    sig_symbols = [sym[1] for sym in sig.symbols.items()]
    # including both constants and relations!
    return sig_symbols
    
def is_symbol_pre_in_vocab(sym, pre_vocab):
    if not ivy_transrel.is_new(sym):
        return sym in pre_vocab
    assert ivy_transrel.is_new(sym)
    return ivy_transrel.new_of(sym) in pre_vocab

def apply_dict_if_in_domain(s, subst):
    if s not in subst.keys():
        return s
    else:
        return subst[s]

class ProcedureSummary(object):
    def __init__(self, formal_params, update_clauses=None, updated_syms=None):
        super(ProcedureSummary, self).__init__()
        
        self._formal_params = formal_params
        
        if update_clauses is None:
            update_clauses = ivy_logic_utils.true_clauses()
        self._update_clauses = update_clauses
        
        # TODO: document meaning
        self._summary_vocab = formal_params + get_signature_symbols()
        
        if updated_syms is None:
            updated_syms = self._summary_vocab
        self._updated_syms = updated_syms
        
    def _update_strenghening_to_vocab_update(self, summary_strengthening):
        strenghening_clauses, updated_syms = summary_strengthening
        
        syms_to_hide = [s for s in set(updated_syms) | set(strenghening_clauses.symbols()) 
                            if not is_symbol_pre_in_vocab(s, self._summary_vocab)]
        
        update = (updated_syms, strenghening_clauses, self.get_precondition())
        
        update_in_vocab = ivy_transrel.hide(syms_to_hide, update)
        
        (updated_syms_in_vocab, 
         strengthening_clauses_in_vocab, 
         precondition_in_vocab) = update_in_vocab
         
        assert precondition_in_vocab == self.get_precondition()
        
        return (updated_syms_in_vocab, strengthening_clauses_in_vocab)
                                                                     
    
    def strengthen(self, summary_strengthening):
        strengthening_in_vocab = self._update_strenghening_to_vocab_update(summary_strengthening)
        updated_syms, strengthening_clauses = strengthening_in_vocab
        
        self._update_clauses = ivy_transrel.conjoin(self._update_clauses, 
                                                    strengthening_clauses)
        self._strengthen_updated_syms(updated_syms)
        
    def _strengthen_updated_syms(self, new_updated_syms): 
        assert all(s in self.get_updated_vars() for s in new_updated_syms)
        self._updated_syms = new_updated_syms
        
    # including both constants and relations!
    def get_updated_vars(self):
        return self._updated_syms
    
    def get_update_clauses(self):
        return self._update_clauses
    
    def get_precondition(self):
        return ivy_logic_utils.true_clauses() # no precondition
    
    def implies(self, other_summary):
        assert self.get_precondition() == other_summary.get_precondition()
        if any(s not in other_summary.get_updated_vars()
                    for s in self.get_updated_vars()):
            return False
        return ivy_solver.clauses_imply(self.get_update_clauses(),
                                        other_summary.get_update_clauses())
        
    def substitute(self, subst):
        renamed_formas = [apply_dict_if_in_domain(s, subst) for s in self._formal_params]
        renamed_update_clauses = ivy_transrel.rename_clauses(self._update_clauses,
                                                             subst)
        renamed_updated_syms = [apply_dict_if_in_domain(s, subst) for s in self._updated_syms]
        return ProcedureSummary(renamed_formas,
                                renamed_update_clauses,
                                renamed_updated_syms)

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
        
    def substitute(self, subst):
        return SummarizedAction(self._name, 
                                self._original_action.substitute(subst),
                                self._procedure_summary.substitute(subst))
            
    # Override
    def action_update(self, domain, pvars):
        updated  = self._procedure_summary.get_updated_vars()
        clauses  = self._procedure_summary.get_update_clauses()
        pre      = self._procedure_summary.get_precondition()
        return (updated, clauses, pre)

class CallsVarRenamer(object):
    def __init__(self):
        super(CallsVarRenamer, self).__init__()
        
        self._calls_to_ids = {}
        self._max_id = 0
        
        self._renaming = {}
        

    def _add_to_known_calls_if_necessary(self, call_action):
        if call_action not in self._calls_to_ids.keys():
            self._max_id += 1
            self._calls_to_ids[call_action] = self._max_id

    def unique_formals(self, call_action, formals):
        self._add_to_known_calls_if_necessary(call_action)
            
        res = {}
        for s in formals:
            call_id = self._calls_to_ids[call_action]
            globally_unique_renamer = lambda name: "fc%d_%s" % (call_id, name)
            unique_sym = ivy_transrel.rename(s, globally_unique_renamer)
            
            res[s] = unique_sym
            
            self._renaming[s] = unique_sym
            
        return res 
    
    def invert_formals_syms(self, clauses, call_action, formals):
        assert call_action in self._calls_to_ids.keys()
        
        inverse_formals_map = {}
        for s in formals:
            renamed_s = self._renaming[s]
            inverse_formals_map[renamed_s] = s
            inverse_formals_map[ivy_transrel.new(renamed_s)] = ivy_transrel.new(s)
            
        return ivy_transrel.rename_clauses(clauses, inverse_formals_map)
        
        
calls_vars_renamer = CallsVarRenamer()
    
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
        
    # Override
    def should_hide_applied_call_formals(self):
        return False
    
    # Override
    def generate_unique_formals_renaming(self, call_action, formals, vocab):
        global calls_vars_renamer
        return calls_vars_renamer.unique_formals(call_action, formals)
    
        
def subprocedures_states_iter(ag, state_to_decompose):
    analysis_graph = ag.decompose_state_partially_repsect_context(state_to_decompose)
    assert analysis_graph is not None
    
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
            # don't continue recursively - decomposing SummarizedAction fails due to
            # variable renaming
        else:
            rec_res = subprocedures_states_iter(ag, state)
            subprocedures_states += rec_res
        
    return subprocedures_states

def clauses_to_new_vocabulary(clauses):
    """"Type of vocabulary used by actions, see ivy_transrel.state_to_action"""
#     ivy_transrel.state_to_action((callee_current_summary.get_updated_vars(), 
#                                         after_state.clauses, 
#                                         callee_current_summary.get_precondition()))[1]
    renaming = dict()
    for s in clauses.symbols():
        if s.is_numeral():
            continue
        if ivy_transrel.is_skolem(s):
            continue
        renaming[s] = ivy_transrel.new(s)
    return ivy_logic_utils.rename_clauses(clauses, renaming)

def clauses_from_new_vocabulary_except_for(clauses, updated_syms):
    renaming = dict()
    for s in clauses.symbols():
        if s.is_numeral():
            continue
        if ivy_transrel.is_skolem(s):
            continue
        if s in updated_syms:
            continue
        if ivy_transrel.is_new(s):
            if ivy_transrel.new_of(s) not in updated_syms:
                renaming[s] = ivy_transrel.new_of(s)
    return ivy_logic_utils.rename_clauses(clauses, renaming)

def clauses_from_new_vocabulary(clauses):
    return clauses_from_new_vocabulary_except_for(clauses, set())

def hide_symbol_if(clauses, should_hide_pred):
    syms_to_hide = [s for s in clauses.symbols() if should_hide_pred(s)]
    return ivy_transrel.hide_clauses(syms_to_hide, clauses)

def transform_to_callee_summary_vocabulary(clauses, call_action):
    callee_action = call_action.get_callee()
    formals = callee_action.formal_params + callee_action.formal_returns
    
#     global calls_vars_renamer
#     formals_as_renamed = calls_vars_renamer.unique_formals(call_action, formals).values()
    
    global calls_vars_renamer
    clauses = calls_vars_renamer.invert_formals_syms(clauses, call_action, formals)
    
    symbols_can_be_modified = get_signature_symbols() + formals
    symbols_can_be_modified_two_vocab = symbols_can_be_modified + \
                                        [ivy_transrel.new(s) for s in symbols_can_be_modified]
    
    return hide_symbol_if(clauses, lambda s: s not in symbols_can_be_modified_two_vocab 
                                                and not s.is_numeral())
    # TODO: MUST TEST this with global variables, local variables, and nested calls
    
def concretize_symbol_pre_and_post(clauses, s, concretization_clauses):
    concretization_clauses_next = clauses_to_new_vocabulary(concretization_clauses)
    
    if s not in clauses.symbols():
            logging.debug("Concretizing %s in the transition pre", s)
            clauses = ivy_transrel.conjoin(clauses,
                                           concretization_clauses)
    if ivy_transrel.new(s) not in clauses.symbols():
        logging.debug("Concretizing %s in the transition post", s)
        clauses = ivy_transrel.conjoin(clauses,
                                       concretization_clauses_next)
        
    return clauses
    
def concretize(clauses):
    # make sure that the state is concrete on all relations, so we have
    # a completely concrete countertrace
    # Ivy hides some of the model facts if they deem irrelevant (probably on get_small_model), 
    # but on decomposition this may be a problem: for example, cme(I) might become true
    # either after the first or second call but because the call summary doesn't mention cme
    # (for example, it is simply True) and so the countertrace won't "decide" which call performed
    # the change, and possibly none of them will be blocked (because if cme(I) is still false then
    # the transition is indeed possible and can't be blocked).
    # TODO: handle function symbols?
    
    for s in get_signature_symbols():
        if not isinstance(s.sort, logic.FunctionSort):
            eq_to_num = logic.Eq(s, ivy_logic.Symbol("0", s.sort))
            clauses = concretize_symbol_pre_and_post(clauses, s, 
                                                 eq_to_num)
            continue
        
        if not isinstance(s.sort.range, logic.BooleanSort):
            continue
        
        arg_vars = [logic.Var('V_%s_%d' % (s.name.upper(), i), s.sort.domain[i])
                        for i in xrange(0, s.sort.arity)]
        
        relation_false = logic.Not(logic.Apply(s, *arg_vars))
        clauses = concretize_symbol_pre_and_post(clauses, s, 
                                                 relation_false)
        
        
     
    return clauses
     
def transition_states_to_concrete_transition_clauses(before_state, after_state):
    after_clauses_new_vocab = clauses_to_new_vocabulary(after_state.clauses) 
    
    transition_clauses = ivy_transrel.conjoin(before_state.clauses,
                                after_clauses_new_vocab)
    
    return concretize(transition_clauses)
    
def update_from_action(ivy_action):
    # TODO: int_update? update? rename our function name?
    return ivy_action.int_update(im.module, {})
    
def get_action_two_vocabulary_clauses(ivy_action, axioms):
    # based on ivy_transrel.forward_image_map, without existential quantification
    updated, clauses, _precond = update_from_action(ivy_action)
    pre_ax = ivy_logic_utils.clauses_using_symbols(updated, axioms)
    pre = pre_ax
    # no existential quantification on pre clauses, just convert to new
    clauses_new_vocab = ivy_logic_utils.rename_clauses(clauses, 
                                                        dict((ivy_transrel.new(x), x) 
                                                                 for x in clauses.symbols() 
                                                                 if x not in updated))
    res = ivy_transrel.conjoin(pre, clauses_new_vocab)
    logger.debug("two vocab for procedure: %s", res)
    return updated, res
    

def get_two_vocab_transition_clauses_wrt_summary(ivy_action, procedure_summaries, axioms):
    with SummarizedActionsContext(procedure_summaries):
        res = get_action_two_vocabulary_clauses(ivy_action, axioms)
        
    return res

def two_vocab_respecting_non_updated_syms(two_vocab_clauses, updated_syms):
    return clauses_from_new_vocabulary_except_for(two_vocab_clauses, updated_syms)

def prepare_update_with_axioms_and_obligation(updated_syms, two_vocab_update, 
                                              two_vocab_obligation):
    axioms = im.module.background_theory()
    
    obligation_wrt_sym_update = two_vocab_respecting_non_updated_syms(two_vocab_obligation,
                                                                      updated_syms)
    
    update_with_axioms = ivy_transrel.conjoin(two_vocab_update, axioms)
    
    return (update_with_axioms, obligation_wrt_sym_update)

# TODO: use prepare_update_with_axioms_and_obligation, also in transition checking
def get_transition_cex_to_obligation_two_vocab(ivy_action, proc_name, 
                                               procedure_summaries, two_vocab_obligation):    
    axioms = im.module.background_theory()
    
    updated_syms, two_vocab_update = get_two_vocab_transition_clauses_wrt_summary(ivy_action, 
                                                                                  procedure_summaries, 
                                                                                  axioms)
    logger.debug("syms updated by the procedure: %s", updated_syms)
    
    logger.debug("two vocab obligation: %s", two_vocab_obligation)
    obligation_wrt_sym_update = two_vocab_respecting_non_updated_syms(two_vocab_obligation,
                                                                      updated_syms)
    logger.debug("two vocab obligation respecting updated syms: %s", two_vocab_obligation)
    
    update_with_axioms = ivy_transrel.conjoin(two_vocab_update, axioms)
    # TODO: perhaps conjoin also the axioms in the post state?
    # TODO: currently the cex can violate the axioms in the post state
    # TODO: because functions are not known not to change symbols that appear in the axioms
    # TODO: (because we currently don't compute an overapproximation of the set of updated variables)
    
    clauses_to_check_sat = ivy_transrel.conjoin(update_with_axioms,
                                                ivy_logic_utils.dual_clauses(obligation_wrt_sym_update))
    
    cex_model = ivy_solver.get_model_clauses(clauses_to_check_sat)
    if cex_model is None:
        return None

    clauses_cex = ivy_solver.clauses_model_to_clauses(clauses_to_check_sat,
                                                      model=cex_model)
    assert clauses_cex != None    
    return clauses_cex

def separate_two_vocab_cex(ivy_action, two_vocab_cex_clauses):
    updated_syms, _, _ = update_from_action(ivy_action)

    hide_in_pre_syms = [s for s in two_vocab_cex_clauses.symbols() 
                            if ivy_transrel.is_new(s)]
    hide_in_post_syms   = [s for s in two_vocab_cex_clauses.symbols() 
                            if not ivy_transrel.is_new(s) and s in updated_syms]

    pre_clauses = ivy_transrel.hide_clauses(hide_in_pre_syms,
                                             two_vocab_cex_clauses)
    post_clauses_post_vocab = ivy_transrel.hide_clauses(hide_in_post_syms,
                                             two_vocab_cex_clauses)
    post_clauses = clauses_from_new_vocabulary(post_clauses_post_vocab)
    
    return (ivy_interp.State(value=ivy_transrel.pure_state(pre_clauses)),
            ivy_interp.State(value=ivy_transrel.pure_state(post_clauses)))
    
def ag_from_two_vocab_cex(action_name, ivy_action, two_vocab_cex_clauses):
    pre_state, post_state = separate_two_vocab_cex(ivy_action, two_vocab_cex_clauses)
    
    ag = ivy_art.AnalysisGraph()
    # based on AnalysisGraph.execute
    ag.add(pre_state)
    ag.add(post_state, ivy_interp.action_app(action_name, pre_state))
    return ag
    
def generate_summary_obligations_from_cex(procedure_summaries, ag):
    # TODO: this actually assumes that the action consists of at least something more than the
    # TODO: call, otherwise the result is still [] although we have what to refine
    # FIXME: make sure that such procedures are inlined or treated carefully
    summary_obligations = []
    
    with SummarizedActionsContext(procedure_summaries):
        assert len(ag.states) == 2
        subprocedures_transitions = subprocedures_states_iter(ag, ag.states[-1])
        
        for call_action, before_state, after_state in subprocedures_transitions:
            logging.debug("Transition states: before: %s", before_state)
            logging.debug("Transition states: after: %s", after_state)
            transition_summary = transition_states_to_concrete_transition_clauses(before_state, after_state)
            logging.debug("Transition summary: %s", transition_summary)
            # TODO: use utils from ivy_infer_universal
            universal_transition_summary = ivy_logic_utils.dual_clauses(ivy_solver.clauses_model_to_diagram(transition_summary, model=None))
            summary_locals_hidden = transform_to_callee_summary_vocabulary(universal_transition_summary, call_action)
            
            summary_obligations.append((call_action.callee_name(), summary_locals_hidden))
        
    return summary_obligations
    
def check_procedure_transition(ivy_action, proc_name,
                               procedure_summaries, two_vocab_obligation):
    with SummarizedActionsContext(procedure_summaries):
        two_vocab_cex = get_transition_cex_to_obligation_two_vocab(ivy_action, proc_name,
                                         procedure_summaries, two_vocab_obligation)
        if two_vocab_cex is None:
            return None
        logger.debug("Got cex: %s", two_vocab_cex)
    
        ag = ag_from_two_vocab_cex(proc_name, ivy_action, two_vocab_cex)
        summary_obligations = generate_summary_obligations_from_cex(procedure_summaries, ag)
        assert summary_obligations != None
        return summary_obligations

def generelize_summary_blocking(ivy_action, proc_name, 
                                procedure_summaries, proof_obligation):
    assert proof_obligation is not None
    axioms = im.module.background_theory()
    
    updated_syms, two_vocab_update = get_two_vocab_transition_clauses_wrt_summary(ivy_action, 
                                                                                  procedure_summaries, 
                                                                                  axioms)
    obligation_wrt_sym_update = two_vocab_respecting_non_updated_syms(proof_obligation,
                                                                            updated_syms)
    
    obligation_not = ivy_logic_utils.dual_clauses(obligation_wrt_sym_update)
    
    NO_INTERPRETED = None
    res = ivy_transrel.interpolant(two_vocab_update, obligation_not,
                                  axioms, NO_INTERPRETED)
    assert res != None
    two_vocab_inferred_fact = res[1]
    return two_vocab_inferred_fact, updated_syms
                                        
                
def infer_safe_summaries():
    exported_actions_names = [ed.exported() for ed in ivy_module.module.exports]
    gupdr_elements = GUPDRElements(ivy_module.module.actions, 
                                  exported_actions_names)
    
    is_safe, frame_or_cex = ivy_infer.pdr(gupdr_elements)
    if not is_safe:
        logger.info("Possibly not safe!")
        abstract_cex_tree = frame_or_cex
        cex = gupdr_elements.check_bounded_safety_by_cex(abstract_cex_tree)
        if cex is None:
            logger.info("Bounded model checking did not find a concrete cex; bug or no universal summary!")
        else:
            logger.info("Not safe! Found concrete cex")
    else:
        logger.info("Safe!")
        safe_frame = frame_or_cex
        for name, summary in safe_frame.iteritems():
            logger.debug("Summary of procedure %s:", name)
            logger.debug("%s" % summary.get_update_clauses())
            logger.debug("")
        

#     procedure_summaries = {}
#     actions_dict = ivy_module.module.actions
#     for name, ivy_action in actions_dict.iteritems():
#         procedure_summaries[name] = ProcedureSummary()
#         
#     #proof_goal = ivy_logic_utils.to_clauses('~errorush()')
#     proof_goal = zzz_new_no_error_clauses()    
#     
#     name, ivy_action = actions_dict.items()[0]
#     if True:
#         new_proof_goal = check_procedure_transition(ivy_action, name, 
#                                                 procedure_summaries, 
#                                                 proof_goal)
#         print new_proof_goal
#         procedure_summaries[name].strengthen(ivy_logic_utils.to_clauses('~errorush()'))
#         for subp in actions_dict.iterkeys():
#             if subp.strip() != "get_next":
#                 continue
#             else:
#                 print "found our action"
#             procedure_summaries[subp].strengthen(zzz_new_no_error_clauses())
#             
#         new_proof_goal = check_procedure_transition(ivy_action, name, 
#                                                 procedure_summaries, 
#                                                 proof_goal)
#         print new_proof_goal
#         assert new_proof_goal is None
#         
#         procedure_summaries[name].strengthen(zzz_new_no_error_clauses())
#         proc_strengthening = generelize_summary_blocking(procedure_summaries[name].get_update_clauses(),
#                                      ivy_logic_utils.dual_clauses(proof_goal))
#         assert proc_strengthening is not None
#         procedure_summaries[name].strengthen(proc_strengthening)
#         print procedure_summaries[name].get_update_clauses()
#         

# TODO: remove
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
        
def formal_params_of_action(ivy_action):
    return ivy_action.formal_params + ivy_action.formal_returns
        
class GUPDRElements(ivy_infer_universal.UnivPdrElements):
    def __init__(self, actions_dict, exported_actions_names):
        super(GUPDRElements, self).__init__()
        
        self._actions_dict = actions_dict
        self._exported_actions_names = exported_actions_names
        
    def initial_summary(self):
#         procedure_summaries = {}
#         
#         # TODO: hack?
#         global_initial_pre_vocab = global_initial_state()
#     
#         for name, _ in self._actions_dict.iteritems():
#             procedure_summaries[name] = ProcedureSummary()
#             procedure_summaries[name]._update_clauses = global_initial_pre_vocab
#             
#         return procedure_summaries
        procedure_summaries = {}
    
        for name, ivy_action in self._actions_dict.iteritems():
            procedure_summaries[name] = ProcedureSummary(formal_params_of_action(ivy_action))
            # TODO: hack, and explain
            procedure_summaries[name]._update_clauses = ivy_logic_utils.false_clauses()
            
        return procedure_summaries
    
    
    def top_summary(self):
        procedure_summaries = {}
    
        for name, ivy_action in self._actions_dict.iteritems():
            procedure_summaries[name] = ProcedureSummary(formal_params_of_action(ivy_action))
            
        return procedure_summaries
    
    # Return (None,None) if safe or (unsafe_predicate, proof obligation) otherwise
    def check_summary_safety(self, summaries):
        for name in self._exported_actions_names:
            logger.debug("Checking safety of proc %s", name)
            ivy_action = self._actions_dict[name]
            proof_goals = check_procedure_transition(ivy_action, name, 
                                                     summaries, self._get_safety_property())
            if proof_goals is not None:
                return (name, proof_goals)
        return (None, None)
    
    def _get_safety_property(self):
        no_cme = ivy_logic_utils.to_clauses('~cme(I)')
        no_cme_next = clauses_to_new_vocabulary(no_cme)
        return ivy_transrel.conjoin(no_cme, no_cme_next) 
    
    # Return None or a list of new proof obligations
    def check_transformability_to_violation(self, predicate, summaries_by_symbol, 
                                            proof_obligation):
        procedure_name_to_check = predicate
        procedure_summaries = summaries_by_symbol
        
        ivy_action = self._actions_dict[procedure_name_to_check]
        
        new_proof_goals = check_procedure_transition(ivy_action, procedure_name_to_check, 
                                                   procedure_summaries, 
                                                   proof_obligation)
        if new_proof_goals is None:
            return None
        
        return new_proof_goals
    
    def generalize_intransformability(self, predicate, summaries, proof_obligation):
        logger.debug("Generalizing intransformability for predicate %s with proof obligation %s",
                     predicate, proof_obligation)
        
        return generelize_summary_blocking(self._actions_dict[predicate], predicate,
                                           summaries,
                                           proof_obligation)
        
    def _get_call_tree_summary(self, cex_node):
        procedure_summaries = {}
        
        call_summary_by_name = {}
        for child in cex_node.children:
            call_summary_by_name[child.predicate] = self._get_call_tree_summary(child)
        
        for name, ivy_action in self._actions_dict.iteritems():
            update_clauses = None
            updated_vars = None
            if name not in call_summary_by_name.keys():
                update_clauses = ivy_logic_utils.false_clauses()
                updated_vars = []
            else:
                (update_clauses, updated_vars) = call_summary_by_name[name]
            
            procedure_summaries[name] = ProcedureSummary(formal_params_of_action(ivy_action),
                                                         update_clauses,
                                                         updated_vars)
            
        parent_action = self._actions_dict[cex_node.predicate]
        axioms = im.module.background_theory()
            
        with SummarizedActionsContext(procedure_summaries):
            (parent_updated_vars, parent_update_clauses) = get_action_two_vocabulary_clauses(parent_action, axioms)
            
        return (parent_update_clauses, parent_updated_vars)
        
    def check_bounded_safety_by_cex(self, abstract_cex_tree):
        update_two_vocab, updated_vars = self._get_call_tree_summary(abstract_cex_tree)
        update_with_axioms, obligation_wrt_sym_update = prepare_update_with_axioms_and_obligation(updated_vars, update_two_vocab,
                                                                                                  self._get_safety_property())
        
        clauses_to_check_sat = ivy_transrel.conjoin(update_with_axioms,
                                                ivy_logic_utils.dual_clauses(obligation_wrt_sym_update))
    
        two_vocab_cex = ivy_solver.get_model_clauses(clauses_to_check_sat)
        
        if two_vocab_cex is None:
            return None
        
        logger.debug("Got cex: %s", two_vocab_cex)
        return two_vocab_cex

        
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