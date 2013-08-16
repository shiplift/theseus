#!/usr/bin/env python
# -*- coding: utf-8 -*-


from rpython.rlib import jit
from rpython.rlib.nonconst import NonConstant

from lamb.startup import startup

from lamb.model import tag
from lamb.shape import CompoundShape
from lamb.expression import Variable
from lamb.util.construction_helper import (pattern as pp, expression as e,
                                           lamb, mu, cons,
                                           plist, conslist, rules,
                                           operand_stack, execution_stack,
                                           nil, is_nil)

def _setup_shapes():
    p_1 = tag("p", 1)

    p_0_shape = p_1.default_shape
    p_1_shape = CompoundShape(p_1, [p_0_shape])
    p_2_shape = CompoundShape(p_1, [p_1_shape])
    p_3_shape = CompoundShape(p_1, [p_2_shape])
    p_4_shape = CompoundShape(p_1, [p_3_shape])

    p_0_shape.transformation_rules[(0, p_0_shape)] = p_1_shape

    p_0_shape.transformation_rules[(0, p_1_shape)] = p_2_shape
    p_1_shape.transformation_rules[(0, p_1_shape)] = p_2_shape

    p_0_shape.transformation_rules[(0, p_2_shape)] = p_3_shape
    p_1_shape.transformation_rules[(0, p_2_shape)] = p_3_shape
    p_2_shape.transformation_rules[(0, p_2_shape)] = p_3_shape

    p_0_shape.transformation_rules[(0, p_3_shape)] = p_4_shape
    p_1_shape.transformation_rules[(0, p_3_shape)] = p_4_shape
    p_2_shape.transformation_rules[(0, p_3_shape)] = p_4_shape
    p_3_shape.transformation_rules[(0, p_3_shape)] = p_4_shape

# _setup_shapes()



# Value
def p(x):
    from lamb.model import w_constructor
    return w_constructor(tag("p", 1), x)

# Pattern
def _p(x):
    from lamb.pattern import ConstructorPattern
    return ConstructorPattern(tag("p", 1), [pp(x)])

# Expression
def p_(x):
    from lamb.model import w_constructor
    return w_constructor(tag("p", 1), [e(x)])


def make_succ():
    x = Variable("x")
    l = lamb()
    l._rules= rules( [([pp(x)], e(p_(x)) )] )
    l._name = "succ"
    return l

def make_pred():
    x = Variable("x")
    l = lamb()
    l._rules = rules([
        ([_p(_zero())], e(_zero())),
        ([pp(x)      ], e(x))])
    l._name = "pred"
    return l

def make_plus():
    x1 = Variable("x")
    x2 = Variable("x")
    x3 = Variable("x")
    y = Variable("y")

    l = lamb()
    l._rules = rules([
        ([pp(_zero()), pp(_zero())], e(_zero())),
        ([pp(x1)     , pp(_zero())], e(x1)),
        ([pp(_zero()), pp(x2)     ], e(x2)),
        ([pp(x3)     , _p(y)      ], e(p_(mu(l, [x3, y]))))])
    l._name = "plus"
    return l
def make_plus_acc():
    x1 = Variable("x")
    x2 = Variable("x")
    x3 = Variable("x")
    y = Variable("y")

    a1 = Variable("accumulator")
    a2 = Variable("accumulator")
    o1 = Variable("op")
    l_acc = lamb()
    l_acc._rules = rules([
        ([pp(a1), pp(_zero())], e(a1)),
        ([pp(a2), _p(o1)     ], e(mu(l_acc, [p_(a2), o1])))])
    l_acc._name = "plus/a"

    l = lamb()
    l._rules = rules([
        ([pp(_zero()), pp(_zero()) ], e(_zero())),
        ([pp(x1)     , pp(_zero()) ], e(x1)),
        ([pp(_zero()), pp(x2)      ], e(x2)),
        ([pp(x3)     , pp(y)       ], e(mu(l_acc, [x3, y])))])
    l._name = "plus"
    return l



def make_mult():
    _1 = Variable("_")
    _2 = Variable("_")
    x = Variable("x")
    y = Variable("y")

    l = lamb()
    l._rules = rules([
        ([pp(_1)     , pp(_zero()) ], e(_zero())),
        ([pp(_zero()), pp(_2)      ], e(_zero())),
        # ([pp(x)      , _p(y)       ], e(mu(_plus(),[]), mu(l, [x, y])), x)))
        ([pp(x)      , _p(y)       ], e(mu(_plus(),[x, mu(l, [x, y])])))
    ])
    l._name = "mult"
    return l


def make_mult_acc():

    _f1 = Variable("_")
    _f2 = Variable("_")
    a1 = Variable("accumulator")
    a2 = Variable("accumulator")
    a3 = Variable("accumulator")
    a4 = Variable("accumulator")

    f1 = Variable("factor1")
    f2 = Variable("factor2")
    l_acc = lamb()
    l_acc._rules = rules([
        ([pp(_zero()), pp(_zero()), pp(a1)], e(a1)),
        ([pp(_f1)    , pp(_zero()), pp(a2)], e(a2)),
        ([pp(_zero()), pp(_f2)    , pp(a3)], e(a3)),
        ([pp(f1)     , _p(f2)     , pp(a4)],
         e(mu(l_acc, [f1, f2, mu(_plus_acc(), [a4, f1])])))
    ])
    l_acc._name = "mult/a"

    _1 = Variable("_")
    _2 = Variable("_")
    x = Variable("x")
    y = Variable("y")

    l = lamb()
    l._rules = rules([
        ([pp(_1)     , pp(_zero())], e(_zero())),
        ([pp(_zero()), pp(_2)     ], e(_zero())),
        ([pp(x)      , pp(y)      ], e(mu(l_acc, [x, y, _zero()]))),
        # ([pp(x)      , _p(y)      ], e(mu(_plus(),[]), mu(l, [x, y])), x)))
        # ([pp(x)      , _p(y)      ], e(mu(_plus(),[]), x, mu(l, [x, y])))))
    ])
    l._name = "mult"
    return l


def ppeano(num, shape):
    return "%d: %s" % (num, shape.merge_point_string())

peano_jit = jit.JitDriver(
    greens=["num", "shape"],
    reds=["i", "res"],
    get_printable_location=ppeano,
)


def peano_num(pynum):
    i = 0
    res = nil()
    shape = None
    peano_jit.can_enter_jit(num=pynum, shape=shape, i=i, res=res)
    while i  < pynum:
        shape = res._shape
        peano_jit.jit_merge_point(num=pynum, shape=shape, i=i, res=res)
        res = cons("p", res)
        i += 1
    return res

def python_num(peano):
    from lamb.model import W_Constructor
    p = peano
    res = 0
    while not is_nil(p):
        assert isinstance(p, W_Constructor)
        res += 1
        p = p.get_child(0)
    return res


g = {'functions':{}}
functions = g['functions']
@startup
def startup_peano():
    # the Tag used in peano arithmetic lists
    functions['zero'] = nil()
    functions['succ'] = make_succ()
    functions['pred'] = make_pred()
    functions['plus'] = make_plus()
    functions['plus_acc'] = make_plus_acc()
    functions['mult'] = make_mult()
    functions['mult_acc'] = make_mult_acc()

def _zero():     return functions.get('zero', None)
def _succ():     return functions.get('succ', None)
def _pred():     return functions.get('pred', None)
def _plus():     return functions.get('plus', None)
def _plus_acc(): return functions.get('plus_acc', None)
def _mult():     return functions.get('mult', None)
def _mult_acc(): return functions.get('mult_acc', None)
