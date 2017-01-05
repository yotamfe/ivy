# See: http://stackoverflow.com/questions/15236450/substituting-function-symbols-in-z3-formulas

from z3 import *
import itertools

def update_term(t, args):
    # Update the children of term t with args. 
    # len(args) must be equal to the number of children in t.
    # If t is an application, then len(args) == t.num_args()
    # If t is a quantifier, then len(args) == 1
    n = len(args)
    _args = (Ast * n)()
    for i in range(n):
        _args[i] = args[i].as_ast()
    return z3._to_expr_ref(Z3_update_term(t.ctx_ref(), t.as_ast(), n, _args), t.ctx)

def rewrite(s, f, t):
    """
    Replace f-applications f(r_1, ..., r_n) with t[r_1, ..., r_n] in s.
    """
    todo = [] # to do list
    todo.append(s)
    cache = AstMap(ctx=s.ctx)
    while todo:
        n = todo[len(todo) - 1]
        if is_var(n):
            todo.pop()
            cache[n] = n
        elif is_app(n):
            visited  = True
            new_args = []
            for i in range(n.num_args()):
                arg = n.arg(i)
                if not arg in cache:
                    todo.append(arg)
                    visited = False
                else:
                    new_args.append(cache[arg])
            if visited:
                todo.pop()
                g = n.decl()
                if eq(g, f):
                    new_n = substitute_vars(t, *new_args)
                else:
                    new_n = update_term(n, new_args)
                cache[n] = new_n
        else:
            assert(is_quantifier(n))
            b = n.body()
            if b in cache:
                todo.pop()
                new_n = update_term(n, [ cache[b] ])
                cache[n] = new_n
            else:
                todo.append(b)
    return cache[s]

def max_num_of_quantified_forall_vars(s):
    if z3.is_quantifier(s) and s.is_forall():
        # not supporing nested foralls
        return s.num_vars()
    elif s.children():
        return max([max_num_of_quantified_forall_vars(child) for child in s.children()])
    else:
        return 0

def instantiate(s, constants_to_instantiate_lst):
    if z3.is_quantifier(s) and s.is_forall():
        num_vars = s.num_vars()
        try:
            return z3.substitute_vars(s.body(), *(constants_to_instantiate_lst[:num_vars]))
        except Z3Exception:
            return None # incorrect sort (hopefully)

    all_instantiated_if_correct_sort = [instantiate(child, constants_to_instantiate_lst) for child in s.children()]
    if None in all_instantiated_if_correct_sort:
        return None
    return update_term(s, all_instantiated_if_correct_sort)

def is_pure_universal(s):
    if z3.is_quantifier(s) and not s.is_forall():
        assert False, "%s is not skolemize" % s
    if is_function_symbol(s):
        return False

    if len(s.children()) == 0:
        return True

    return all(is_pure_universal(child) for child in s.children())

class SortMismatch(Exception):
    pass

def instantiate_bounded_horizon_all_not_pure_quantifiers(s, constants_to_instantiate_lst):
    def instantiate_all_not_pure_quantifiers_throw(s, constants_to_instantiate_lst):
        if z3.is_quantifier(s) and s.is_forall():
            s = instantiate_single_universal_quantifier_if_not_pure_throw_sort_mistmatch(s, constants_to_instantiate_lst)
    
        return update_term(s, [instantiate_all_not_pure_quantifiers_throw(child, constants_to_instantiate_lst) \
                                    for child in s.children()])
    try:
        return instantiate_all_not_pure_quantifiers_throw(s, constants_to_instantiate_lst)
    except SortMismatch:
        return None
    
def instantiate_single_universal_quantifier_if_not_pure_throw_sort_mistmatch(s, constants_to_instantiate_lst):
    res = instantiate_single_universal_quantifier_if_not_pure(s, constants_to_instantiate_lst)
    if res != None:
        return res
    raise SortMismatch()


def instantiate_single_universal_quantifier_if_not_pure(s, constants_to_instantiate_lst):
    if z3.is_quantifier(s) and s.is_forall():
        if is_pure_universal(s):
            return s
        num_vars = s.num_vars()
        try:
            return z3.substitute_vars(s.body(), *(constants_to_instantiate_lst[:num_vars]))
        except Z3Exception:
            return None # incorrect sort (hopefully)

    all_instantiated_if_correct_sort = [instantiate(child, constants_to_instantiate_lst) for child in s.children()]
    if None in all_instantiated_if_correct_sort:
        return None
    return update_term(s, all_instantiated_if_correct_sort)
    
def instantiate_all_foralls_with_all_constants(s, all_constants):
    # lots of redundancy between different permutations, but should be good enough
    print("Num constants:", len(all_constants))
    all_combination_of_constants_with_repetitions_order_important = []
    for combination in itertools.combinations_with_replacement(all_constants, max_num_of_quantified_forall_vars(s)):
        for instantiation in itertools.permutations(combination):
            all_combination_of_constants_with_repetitions_order_important.append(instantiation)
    print(len(all_combination_of_constants_with_repetitions_order_important))
            
    all_instantiated_if_correct_sort = [instantiate(s, constants_to_instantiate)
                                          for constants_to_instantiate in all_combination_of_constants_with_repetitions_order_important]
    all_instantiated = filter(lambda x: x != None, all_instantiated_if_correct_sort)
    return z3.And(all_instantiated)

def remove_dup(lst):
    unique_list = []
    for elem in lst:
        # HACK: I don't know how to check identity of Z3 constants,
        # so checking according to their string representation
        if str(elem) not in [str(existing_element) for existing_element in unique_list]:
            unique_list.append(elem)
    return unique_list

def constants(s): 
    if z3.is_const(s) and not z3.is_var(s):
        return [s]
    else:
        subconstants = []
        for child in s.children():
            subconstants += constants(child)
        return remove_dup(subconstants)
        #return subconstants
    
def skolemize(s):
    g = z3.Goal()
    g.add(s)
    t = z3.Tactic('snf') # use tactic to convert to SNF
    res = t(g)
    skolemized_formula = res.as_expr()
    
    #original_constants = constants(s)
    #new_constants = filter(lambda const: const not in original_constants, constants(skolemized_formula))
    
    #return skolemized_formula, new_constants
    return skolemized_formula

def is_function_symbol(s):
    if not z3.is_app(s):
        return False
    if z3.is_const(s):
        return False

    func = s.decl()
    if func.range() == z3.BoolSort():
        # func is a predicate symbol
        return False
      
    if func.name().lower() == 'if':
      return False

    return True

def function_symbols(s):
    func_symbols_lst = []
    if is_function_symbol(s):
        func_symbols_lst.append(s.decl())

    for child in s.children():
        func_symbols_lst += function_symbols(child)

    return func_symbols_lst

def num_syntactic_terms(s, selector, mapper=lambda s: 1):
    is_of_interest = 0 
    if selector(s):
        #if is_pure_universal(s)::
        is_of_interest = mapper(s)
        
    return is_of_interest + sum(num_syntactic_terms(child, selector, mapper) for child in s.children())

def bounded_horizon_closed_terms(func_symbols, const_symbols, bound):
    assert bound == 1

    for func_symbol in func_symbols:
        arity = func_symbol.arity()

        all_combination_of_constants_with_repetitions_order_important = []
        for combination in itertools.combinations_with_replacement(const_symbols, arity):
            for instantiation in itertools.permutations(combination):
                yield func_symbol(*instantiation)
                # TODO: has some repetitions, (c,c) and (c,c)

def eliminate_dup_funcs_by_name(funcs_lst):
    res = []
    for func in funcs_lst:
      if str(func) not in [str(f) for f in res]:
	res.append(func)
    return res

def bounded_horizon_instantiations(s):
    skolemized_with_funcs = skolemize(s)
    print skolemized_with_funcs
    funcs = function_symbols(skolemized_with_funcs)
    funcs = eliminate_dup_funcs_by_name(funcs)
    print funcs

    #terms_to_instantiate = list(bounded_horizon_closed_terms(funcs, constants(s), bound=1))
    terms_to_instantiate = constants(skolemized_with_funcs)
    print terms_to_instantiate
    instantiation = instantiate_foralls_with_terms_bounded_horizon(skolemized_with_funcs, terms_to_instantiate)
    print instantiation
    return instantiation

def bounded_horizon_restrict_universals(s, print_debug=False):
    skolemized_with_funcs = skolemize(s)
    if print_debug:
        print "Num constants:", len(constants(skolemized_with_funcs))
        print "Num universal quantifiers", num_syntactic_terms(skolemized_with_funcs, lambda s: z3.is_quantifier(s) and s.is_forall(), lambda s: s.num_vars())
        print "Num universal quantifiers to be reduced", num_syntactic_terms(skolemized_with_funcs, lambda s: z3.is_quantifier(s) and s.is_forall() and not is_pure_universal(s), lambda s: s.num_vars())
        print "Num skolem function", len(set(str(f) for f in function_symbols(skolemized_with_funcs)))
    #print skolemized_with_funcs
    #funcs = function_symbols(skolemized_with_funcs)
    #print funcs

    #terms_to_instantiate = list(bounded_horizon_closed_terms(funcs, constants(s), bound=1))
    terms_to_instantiate = constants(skolemized_with_funcs)
    #print terms_to_instantiate
    instantiation = restrict_universal_quantifiers_to_terms(skolemized_with_funcs, terms_to_instantiate)
    #print instantiation
    return instantiation


def instantiate_foralls_with_terms_bounded_horizon(s, closed_terms):
    # lots of redundancy between different permutations, but should be good enough
    print("Num constants:", len(closed_terms))
    all_combination_of_constants_with_repetitions_order_important = []
    for combination in itertools.combinations_with_replacement(closed_terms, max_num_of_quantified_forall_vars(s)):
        for instantiation in itertools.permutations(combination):
            all_combination_of_constants_with_repetitions_order_important.append(instantiation)
            
    all_instantiated_if_correct_sort = [instantiate_bounded_horizon_all_not_pure_quantifiers(s, constants_to_instantiate)
                                          for constants_to_instantiate in all_combination_of_constants_with_repetitions_order_important]
    all_instantiated = filter(lambda x: x != None, all_instantiated_if_correct_sort)
    print "Number of clauses instantiated:", len(all_instantiated)
    return z3.And(all_instantiated)

def restrict_var(s, var, closed_terms):
    return z3.Or(*[t == z3.Var(var, s.var_sort(var)) for t in closed_terms if s.var_sort(var) == t.sort()])

def restrict_universal_quantifiers_to_terms(s, closed_terms):
    if z3.is_quantifier(s) and s.is_forall():
        if is_pure_universal(s):
            return s
            
        assert s.num_vars() > 0
        restriction_guard = z3.And(*[restrict_var(s, var, closed_terms) for var in xrange(0, s.num_vars())])
        
        s = update_term(s, [z3.Implies(restriction_guard,
                                      s.body())])
        
    return update_term(s, [restrict_universal_quantifiers_to_terms(child, closed_terms) for child in s.children()])

def main():
    p = z3.Function("p", z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.BoolSort())
    x = z3.Int('x')
    y = z3.Int('y')
    z = z3.Int('z')
    c = z3.Const('c', z3.IntSort())
    d = z3.Const('d', z3.IntSort())
    s = z3.And(z3.ForAll([x,z], z3.Exists(y, p(x, y, z, d, c))),
               z3.ForAll(x, p(x, x, x, x, x)))
    bounded_horizon_instantiations(s)

if __name__ == "__main__":
    main()