#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import ivy
import ivy_interp as itp
import ivy_actions as act
import ivy_utils as utl
import ivy_logic_utils as lut
import tk_ui as ui
import ivy_logic as lg
import ivy_utils as iu
import ivy_module as im
import ivy_alpha
import ivy_art
import ivy_interp
import ivy_compiler
import ivy_isolate

import sys
from ivy import ivy_logic_utils, ivy_transrel

import ivy_solver

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)


def display_cex(msg,ag):
    print msg
    if diagnose.get():
        ui.ui_main_loop(ag)
    exit(1)
    
def check_properties():
    if itp.false_properties():
        if diagnose.get():
            print "Some properties failed."
            gui = ui.new_ui()
            gui.tk.update_idletasks() # so that dialog is on top of main window
            gui.try_property()
            gui.mainloop()
            exit(1)
        raise iu.IvyError(None,"Some properties failed.")
    im.module.labeled_axioms.extend(im.module.labeled_props)


def check_conjectures(kind,msg,ag,state):
    failed = itp.undecided_conjectures(state)
    if failed:
        if diagnose.get():
            print "{} failed.".format(kind)
            gui = ui.new_ui()
            agui = gui.add(ag)
            gui.tk.update_idletasks() # so that dialog is on top of main window
            agui.try_conjecture(state,msg="{}\nChoose one to see counterexample.".format(msg))
            gui.tk.mainloop()
            exit(1)
        raise iu.IvyError(None,"{} failed, {}".format(kind,msg))
    
def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)
                    
def infer_safe_summaries():
    ivy_isolate.create_isolate(None)
    check_properties()
    ag = ivy_art.AnalysisGraph(initializer=ivy_alpha.alpha)
    with ivy_interp.EvalContext(check=False):
        #check_conjectures('Initiation','These conjectures are false initially.',ag,ag.states[0])
        for a in sorted(im.module.public_actions):
            print "trying {}...".format(a)
            ag.execute_action(a,prestate=ag.states[0])
            cex = ag.check_bounded_safety(ag.states[-1])
            if cex is not None:
                display_cex("safety failed",cex)
            check_conjectures('Consecution','These conjectures are not inductive.',ag,ag.states[-1])
            
class PredicateSummary(object):
    def __init__(self, predicate_symbol):
        self._predicate_symbol
        
        self._summary = ivy_logic_utils.true_clauses()
        
    def get_summary(self):
        return self._summary
        
    def get_predicate_symbol(self):
        return self._predicate_symbol
    
    def strengthen(self, summary_strengthening):
        self._summary = ivy_transrel.conjoin(self._summary, summary_strengthening)

class PdrFrame(object):
    def __init__(self, predicate_summary=None):
        super(PdrFrame, self).__init__()
        
        self._inv_predicate = "inv"
        
        if predicate_summary is None:
            predicate_summaries_lst = [PredicateSummary(self._inv_predicate)]
        else:
            predicate_summaries_lst = [predicate_summary]
            
        self._summaries_by_symbol = dict((predicate_summary.get_predicate_symbol(), predicate_summary) 
                                                for predicate_summary in predicate_summaries_lst)
    
    def get_summaries_by_symbol_dict(self):
        return self._summaries_by_symbol
        
    def substitute_summaries(self, formula):
        # TODO:
        return formula
    
    def strengthen(self, summary_strengthening):
        self._summaries_by_symbol[self._inv_predicate].strengthen(summary_strengthening)

def are_frames_converged(frame1, frame2):
    summaries_dict_1 = frame1.get_summaries_by_symbol_dict()
    summaries_dict_2 = frame2.get_summaries_by_symbol_dict()
    
    for predicate_symbol in summaries_dict_2:
        summary1 = summaries_dict_1.get(predicate_symbol)
        summary2 = summaries_dict_2.get(predicate_symbol)
        if not ivy_solver.clauses_imply(summary2.get_summary(),
                                        summary1.get_summary()):
            return False

    return True

def prove_goal(frames, current_bound, current_bound_counterexample):
    if current_bound == 0:
        return False
    
    previous_bound = current_bound - 1
    previous_bound_counterexample = None
    
    # TODO: get the right transformer...
    while False: # have a counterexample in the previous frame that reaches current_counterexample
        previous_bound_counterexample = None
        prove_goal(previous_bound, previous_bound_counterexample)
        
    for i in xrange(1, current_bound):
        strengthening_summary = None # from previous_bound_counterexample
        frames[i].strengthen(strengthening_summary)
        
def check_pdr_convergence(frames, current_bound):
    for i in xrange(0, current_bound):
        if are_frames_converged(frames[i], frames[i+1]):
            return frames[i].get_summaries_by_symbol_dict()
    return None

def pdr(initial_frame, check_summary_safety):
    frames = []
    
    # init
    frames[0] = initial_frame
    current_bound = 0
    
    while True:
        # unroll
        new_bound = current_bound + 1
        frames[new_bound] = PdrFrame()
        while True:
            new_frame_summaries = frames[new_bound].get_summaries_by_symbol_dict()
            counterexample_to_safety = check_summary_safety(new_frame_summaries)
            if counterexample_to_safety is None:
                break
            
            successfully_blocked = prove_goal(frames, current_bound, counterexample_to_safety)
            if not successfully_blocked:
                # TODO: collect counter-trace
                return None

        current_bound = new_bound
        
        safe_summaries = check_pdr_convergence(frames, current_bound)
        if safe_summaries is not None:
            return safe_summaries

def main():
    ivy.read_params()
    iu.set_parameters({'mode':'induction'})
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        with utl.ErrorPrinter():
            ivy.source_file(sys.argv[1],ivy.open_read(sys.argv[1]),create_isolate=False)
            infer_safe_summaries()
    print "OK"


if __name__ == "__main__":
    main()