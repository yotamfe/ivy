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

def restrict_var(s, var, var_sort, closed_terms):   
    return z3.Or(*[t == var for t in closed_terms if var_sort == t.sort()])

def restrict_universal_quantifiers_to_terms(s, closed_terms):
    if z3.is_quantifier(s):
        assert s.num_vars() > 0
        
        # We replace the internal representation, that uses z3.Var, by z3.Const, to be able to refer to the quantified
        # variables in the bound guard
        consts_quantify_over = [z3.Const(s.var_name(idx), s.var_sort(idx)) for idx in xrange(0, s.num_vars())]
        
        restriction_guard = z3.And(*[restrict_var(s, consts_quantify_over[var_idx], s.var_sort(var_idx), 
                                                  closed_terms) 
                                        for var_idx in xrange(0, s.num_vars())])
        
        # see https://github.com/Z3Prover/z3/issues/402
        body_with_consts = z3.substitute_vars(s.body(), *reversed(consts_quantify_over))

        if s.is_forall():
            s = z3.ForAll(consts_quantify_over,
                         z3.Implies(restriction_guard,
                                    body_with_consts))
        else: # Exists
            s = z3.Exists(consts_quantify_over,
                          z3.And(restriction_guard,
                                 body_with_consts))
        
    return update_term(s, [restrict_universal_quantifiers_to_terms(child, closed_terms) for child in s.children()])