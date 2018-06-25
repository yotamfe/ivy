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
import ivy_transrel
import ivy_actions
import ivy_solver
import ivy_logic
import json
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


def get_domain():
    return ivy_art.AnalysisGraph().domain

def action_update(action):
    pre = ivy_interp.State()
    return action.update(get_domain(), pre.in_scope)


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
        pre.clauses = and_clauses(*prestate_clauses)
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
                logging.debug("STATES1: %s", res.states)
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

def global_safety_clauses_lst():
    return [ivy_logic_utils.formula_to_clauses(lc.formula) for lc in im.module.labeled_conjs]

class SafetyOfStateClause(ivy_linear_pdr.LinearSafetyConstraint):
    def __init__(self, pred, safety_clauses_lst):
        super(SafetyOfStateClause, self).__init__(pred, ivy_logic_utils.true_clauses())
        self._safey_clauses_lst = safety_clauses_lst

    def check_satisfaction(self, summaries_by_pred):
        inv_summary = summaries_by_pred[self._lhs_pred].get_summary()

        for conjecture in self._safey_clauses_lst:
            bad_clauses = ivy_logic_utils.dual_clauses(conjecture)
            inv_but_bad_clauses = ClausesClauses(inv_summary.get_conjuncts_clauses_list() + [bad_clauses])
            bad_inv_model = inv_but_bad_clauses.get_model()
            if bad_inv_model is None:
                continue

            return ivy_infer.PdrCexModel(bad_inv_model, inv_but_bad_clauses.to_single_clauses())

        return None

    def __str__(self):
        return "Safety: %s => %s" % (self._lhs_pred, self._safey_clauses_lst)


class AutomatonEdge(object):
    def __init__(self, action_name, precondition=ivy_logic_utils.true_clauses()):
        self._action_name = action_name
        self._precondition = precondition

    def get_action_name(self):
        return self._action_name

    def get_precondition(self):
        return self._precondition

    def __repr__(self):
        return "%s assume %s" % (self._action_name, self._precondition)


class OutEdgesCoveringTrClause(ivy_linear_pdr.LinearSafetyConstraint):
    def __init__(self, pred, out_edges_actions):
        super(OutEdgesCoveringTrClause, self).__init__(pred, ivy_logic_utils.true_clauses())

        self._out_edges_actions = out_edges_actions
        checked_wrt_to_actions = self.full_tr_list_actions()
        for out_edge in self._out_edges_actions:
            assert out_edge.get_action_name() in checked_wrt_to_actions, "%s not known from %s" % (out_edge.get_action_name(), checked_wrt_to_actions)

    def full_tr_list_actions(self):
        # excluding the action representing the disjunction of all actions
        return filter(lambda action_name: action_name != 'ext', im.module.public_actions)

    def check_satisfaction(self, summaries_by_pred):
        logging.debug("Check edge covering: all exported %s, is covered by %s", self.full_tr_list_actions(), self._out_edges_actions)

        for action_check_covered in self.full_tr_list_actions():
            matching_edges = filter(lambda edge: edge.get_action_name() == action_check_covered, self._out_edges_actions)
            # accumulated_pre = ivy_logic_utils.or_clauses(*(edge.get_precondition() for edge in matching_edges)).epr_closed()

            # check: I_s /\ TR[action] => \/ accumulated_pre
            (_, tr_action, _) = action_update(im.module.actions[action_check_covered])
            vc = ClausesClauses(summaries_by_pred[self._lhs_pred].get_summary().get_conjuncts_clauses_list() +
                                [tr_action] +
                                [ivy_logic_utils.dual_clauses(edge.get_precondition()) for edge in matching_edges])

            cex = vc.get_model()
            if cex is None:
                continue

            logger.debug("Check covered failed: %s doesn't cover action %s",
                         [edge.get_precondition() for edge in matching_edges],
                         action_check_covered)

            return ivy_infer.PdrCexModel(cex, vc.to_single_clauses(), project_pre=True)

        return None

    def __str__(self):
        return "Edge covering of %s by %s" % (self.lhs_pred(), self._out_edges_actions)


class SummaryPostSummaryClause(ivy_linear_pdr.LinearMiddleConstraint):
    def __init__(self, lhs_pred, edge_action, rhs_pred):
        super(SummaryPostSummaryClause, self).__init__(lhs_pred, edge_action, rhs_pred)
        self._edge_action = edge_action

    def check_transformability(self, summaries_by_pred, bad_clauses):
        prestate_summary = summaries_by_pred[self._lhs_pred].get_summary()

        proof_obligation = ivy_logic_utils.dual_clauses(bad_clauses)

        logger.debug("Checking edge (%s, %s, %s): %s in prestate guarantees %s in poststate?",
                     self._lhs_pred, self._edge_action, self._rhs_pred,
                     prestate_summary.to_single_clauses(), proof_obligation)

        edge_action_name, edge_action_precond = self._edge_action
        countertransition = check_action_transition(prestate_summary.get_conjuncts_clauses_list() + [edge_action_precond],
                                                    edge_action_name,
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

        (edge_action_name, precond) = (self._edge_action)

        prestate_clauses = prestate_summaries[self._lhs_pred].get_summary()

        # relying on isolate context created earlier
        ag = ivy_art.AnalysisGraph()

        pre = State()
        pre.clauses = and_clauses(*prestate_clauses.get_conjuncts_clauses_list() + [precond])

        action = im.module.actions[edge_action_name]

        post = ivy_logic_utils.dual_clauses(lemma)

        axioms = ivy_all_axioms()
        NO_INTERPRETED = None
        res = ivy_transrel.forward_interpolant(pre.clauses, action.update(ag.domain, pre.in_scope), post, axioms,
                                               NO_INTERPRETED)
        assert res != None
        return res[1]

    def transformability_update(self, summaries_by_pred, rhs_vocab):
        assert rhs_vocab == ivy_transrel.new, "Caller expects vocabulary unexpected for the constraint"

        (edge_action_name, edge_precond) = self._edge_action

        action = im.module.actions[edge_action_name]
        (updated_syms, clauses, _) = action_update(action)

        lhs_clauses_clauses = ClausesClauses(summaries_by_pred[self._lhs_pred].get_summary().get_conjuncts_clauses_list() +
                                             [clauses] + [edge_precond])
        as_single_clauses = lhs_clauses_clauses.to_single_clauses()
        # as_single_clauses = ivy_logic_utils.and_clauses_avoid_clash(summaries_by_pred[self._lhs_pred].get_summary().to_single_clauses(),
        #                                                             clauses,
        #                                                             edge_precond)


        return (updated_syms, as_single_clauses)

    def __repr__(self):
        return "Edge %s: %s => %s" % (self._edge_action, self._lhs_pred, self._rhs_pred)


def out_edge_covering_tr_constraints(states, edges):
    constraints = []
    for state in states:
        out_actions = [AutomatonEdge(action, precondition=pre) for (s1, _, action, pre) in edges if s1 == state]
        constraints.append(OutEdgesCoveringTrClause(state, out_actions))

    return constraints

def load_quantifiers(quantifiers_dict):
    for name, sort in quantifiers_dict.iteritems():
        ivy_logic.add_symbol(name, im.module.sig.sorts[sort])

def load_axiom(axiom_str):
    import ivy_ast
    im.module.labeled_axioms.append(ivy_ast.LabeledFormula('use-defined', ivy_logic_utils.to_formula(axiom_str)))

# automaton object:
#   - name(string, optional) for documentation purposes, ignored by ivy
#   - states(array of state objects, required) lists the states of the automaton,
#     state objects described below
#   - init(string, required) names the initial state of the automaton
#   - safety(string or null, required) string representing the safety formula to prove,
#     or null to use top-level conjectures from the ivy file
#   - quantifiers(object, optional) key-value items (string-string) of the object specify
#     variable names to universally quantify and their sorts
#   - axiom(string, optional) formula to add to axioms from ivy file
#
# state object:
#   - name(string, required) the name of the state, used as a unique id
#   - edges(array of edge objects, required) lists the outgoing edges from this state
#   - characterization(string, output only) formula giving the inferred invariant annotation in this state
#
# edge object:
#   - target(string, required) name of the state that is the destination of this edge
#   - action(string, required) name of the action that triggers this edge
#   - precond(string, optional) formula that guards when this edge fires

class AutomatonFileRepresentation(object):
    def __init__(self, filename):
        with open(filename, 'rt') as f:
            file_contents = f.read()
        self.json_data = json.loads(file_contents)

        self.states = [s['name'] for s in self.json_data['states']]
        self.init = [(self.json_data['init'], global_initial_state())]

        assert self.json_data['init'] in self.states, "Initial state %s does not exist in list of states." % self.json_data['init']

        if 'quantifiers' in self.json_data:
            logger.debug("Loading quantifiers...")
            load_quantifiers(self.json_data['quantifiers'])

        if 'axiom' in self.json_data:
            logger.debug("Loading axiom...")
            load_axiom(self.json_data['axiom'])

        self.edges = []
        for s in self.json_data['states']:
            for e in s['edges']:
                target = e['target']
                action = e['action']
                if 'precond' in e:
                    logger.debug("Loading edge %s", e['precond'])
                    self.precondition = ivy_logic_utils.to_clauses(e['precond'])
                else:
                    self.precondition = ivy_logic_utils.true_clauses()
                self.edges.append((s['name'], target, action, self.precondition))
        safety_str = self.json_data['safety']
        if not safety_str:
            self.safety_clauses_lst = global_safety_clauses_lst()
        else:
            logger.debug("Loading safety %s", safety_str)
            self.safety_clauses_lst = [ivy_logic_utils.to_clauses(self._str_back_to_clauses(safety_str))]

        logger.debug("Done loading automaton")

    def dump_with_state_characterization(self, outfilename, characterization_per_state):
        new_data = self.json_data.copy()
        for state_data in new_data['states']:
            state_name = state_data['name']
            characterization = characterization_per_state[state_name]
            state_data['characterization'] = [str(c) for c in characterization]

        with open(outfilename, 'wt') as outfile:
            json.dump(new_data, outfile, sort_keys=True, indent=4)

    def _str_back_to_clauses(self, s):
        import re
        # eliminate unicode, raises parsing errors
        s = s.encode('ascii')
        # clauses generate equality with false & true but the parser doesn't accept them
        # FIXME: doesn't work right when there is more than one, changes only the last
        s = re.sub('(.+) = true', '\g<1>', s)
        s = re.sub('(.+) = false', '~\g<1>', s)
        s = re.sub('(.+) ~= true', '~\g<1>', s)
        s = re.sub('(.+) ~= false', '\g<1>', s)
        return s

    def characterization_by_state(self):
        res = {}
        for s in self.json_data['states']:
            name = s['name']
            characterization = s.get('characterization', ['true'])
            characterization_clauses_lst = [ivy_logic_utils.to_clauses(self._str_back_to_clauses(cf))
                                            for cf in characterization]
            res[name] = characterization_clauses_lst

        return res


def load_json_automaton(filename):
    return AutomatonFileRepresentation(filename)

def infer_safe_summaries(automaton_filename, output_filename=None, check_only=True):
    automaton = load_json_automaton(automaton_filename)
    logger.debug("States: %s", automaton.states)
    logger.debug("Init: %s", automaton.init)
    logger.debug("Edges: %s", automaton.edges)
    logger.debug("Safety: %s", automaton.safety_clauses_lst)

    mid = [SummaryPostSummaryClause(s1, (action_name, precond), s2) for (s1, s2, action_name, precond) in automaton.edges]
    end_state_safety = [SafetyOfStateClause(s, automaton.safety_clauses_lst) for s in automaton.states]
    end_state_cover_tr = out_edge_covering_tr_constraints(automaton.states, automaton.edges)
    end = end_state_safety + end_state_cover_tr

    if check_only:
        return check_automaton(automaton, end, mid, output_filename)

    infer_automaton(automaton, end, mid, output_filename)

def sort_mid_constraints_by_heuristic_precedence(mid):
    return sorted(mid, key=lambda midc: midc.lhs_pred() != midc.rhs_pred(), reverse=True)

def sort_safety_constraints_by_heuristic_precedence(init, mid, end):
    explored_states = [init_state for (init_state, _) in init]

    while True:
        exploratory_transformers = filter(lambda midc: midc.lhs_pred() in explored_states and midc.rhs_pred() not in explored_states,
                                          mid)
        new_states = set(map(lambda midc: midc.rhs_pred(), exploratory_transformers))
        if not new_states:
            break
        explored_states.extend(new_states)

    safety_forward_order = []
    for state in explored_states:
        safety_of_state = filter(lambda endc: endc.lhs_pred() == state, end)
        safety_forward_order.extend(safety_of_state)

    assert set(safety_forward_order) == set(end), "Not all states explored; is the graph not connected? Got %s" % safety_forward_order
    # return list(reversed(safety_forward_order))
    return safety_forward_order

def infer_automaton(automaton, end, mid, output_filename):
    mid = sort_mid_constraints_by_heuristic_precedence(mid)
    end = sort_safety_constraints_by_heuristic_precedence(automaton.init, mid, end)

    start_time = datetime.datetime.now()
    logger.info("Starting inference. Time: %s", start_time)

    pdr_elements_global_invariant = ivy_linear_pdr.LinearPdr(automaton.states, automaton.init, mid, end,
                                                             ivy_infer_universal.UnivGeneralizer(),
                                                             ivy_all_axioms())
    is_safe, frame_or_cex = ivy_infer.pdr(pdr_elements_global_invariant)
    if not is_safe:
        print "Possibly not safe! - bug or no universal invariant"
        cex = frame_or_cex
        while cex:
            logger.info("Cex node: %s, %s", cex.predicate, cex.obligation)
            assert len(cex.children) <= 1
            if not cex.children:
                break
            cex = cex.children[0]
    else:
        safe_frame = frame_or_cex
        end_time = datetime.datetime.now()
        logger.info("Proof found. Time: %s", end_time)
        logger.info("Inference time: %s", end_time - start_time)
        for state, summary in safe_frame.iteritems():
            logger.info("Summary of %s: %s", state, summary.get_summary())

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

        if output_filename:
            automaton.dump_with_state_characterization(output_filename, {state: summary.get_summary().get_conjuncts_clauses_list()
                                                                         for (state, summary) in safe_frame.iteritems()})

def check_automaton(automaton, end, mid, output_filename):
    is_inductive = True
    summaries_by_pred = {state: ivy_infer.PredicateSummary(state, characterization_clauses_lst)
                         for (state, characterization_clauses_lst) in automaton.characterization_by_state().iteritems()}

    init_check_lst = {init_state: (ivy_solver.clauses_list_imply_list([init_cond, ivy_all_axioms()],
                                                                      summaries_by_pred[init_state].get_summary().get_conjuncts_clauses_list()))
                      for (init_state, init_cond) in automaton.init}

    safety_checks = {endc: endc.check_satisfaction(summaries_by_pred) for endc in end}

    mid_checks = {midc: {lemma: midc.check_transformability(summaries_by_pred, ivy_logic_utils.dual_clauses(lemma))
                         for lemma in summaries_by_pred[midc.rhs_pred()].get_summary().get_conjuncts_clauses_list()}
                  for midc in mid}

    for init_state, res_lst in init_check_lst.iteritems():
        if not all(res_lst):
            logger.info("Init check failed: %s, %s", init_state, res_lst)
            is_inductive = False

    for safec, res in safety_checks.iteritems():
        if res is not None:
            logger.info("Safety failed: %s", str(safec))
            is_inductive = False

    for edgec, res_lst in mid_checks.iteritems():
        for lemma, res in res_lst.iteritems():
            if res is not None:
                logger.info("Edge check failed: %s not implied in constraint %s", lemma, str(edgec))
                is_inductive = False

    if is_inductive:
        logger.info("Automaton is inductive!")
    else:
        logger.info("Non inductive automaton!")


def infer_with_automaton():
    if len(sys.argv) not in [3, 4] or not sys.argv[1].endswith('ivy'):
        print "usage: \n  {} file.ivy automaton_in.json [automaton_out.json]".format(sys.argv[0])
        sys.exit(1)

    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1], ivy_init.open_read(sys.argv[1]), create_isolate=False)

            # inspired by ivy_check.check_module()
            isolates = sorted(list(im.module.isolates))
            assert len(isolates) == 1
            isolate = isolates[0]
            with im.module.copy():
                ivy_isolate.create_isolate(isolate, ext='ext')

                outfilename = None
                if len(sys.argv) >= 4:
                    outfilename = sys.argv[3]
                infer_safe_summaries(sys.argv[2], outfilename)


def main():
    logging.basicConfig(level=logging.DEBUG)

    import signal
    # signal.signal(signal.SIGINT, signal.SIG_DFL)
    import ivy_alpha
    ivy_alpha.test_bottom = False  # this prevents a useless SAT check
    import tk_ui as ui
    op_param = iu.Parameter('op', 'infer')
    iu.set_parameters({'mode': 'induction'})

    ivy_init.read_params()
    if len(sys.argv) not in [3, 4] or not sys.argv[1].endswith('ivy'):
        print "usage: \n  {} file.ivy automaton_in.json [automaton_out.json]".format(sys.argv[0])
        sys.exit(1)

    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1], ivy_init.open_read(sys.argv[1]), create_isolate=False)

            # inspired by ivy_check.check_module()
            isolates = sorted(list(im.module.isolates))

            if len(isolates) == 0:
                isolates = [None]
            assert len(isolates) == 1
            isolate = isolates[0]
            with im.module.copy():
                ivy_isolate.create_isolate(isolate, ext='ext')

                outfilename = None
                if len(sys.argv) >= 4:
                    outfilename = sys.argv[3]

                check_only = (op_param.get() == 'check')
                infer_safe_summaries(sys.argv[2], outfilename, check_only=check_only)


if __name__ == "__main__":
    main()
