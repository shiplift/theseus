#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb.execution import Variable, tag
from lamb.shape import CompoundShape
from lamb.util.construction_helper import (pattern, lamb, ziprules, mu, cons,
                                           plist, conslist,
                                           operand_stack, execution_stack,
                                           w_nil, t_nil)

# the Tag used in peano arithmetic lists
def _setup_shapes():
    p_1 = tag("p", 1)

    p_0_shape = p_1.default_shape
    p_1_shape = CompoundShape(p_1, [p_0_shape])
    p_2_shape = CompoundShape(p_1, [p_1_shape])
    p_3_shape = CompoundShape(p_1, [p_2_shape])
    p_4_shape = CompoundShape(p_1, [p_3_shape])

    p_0_shape.known_transformations[(0, p_0_shape)] = p_1_shape

    p_0_shape.known_transformations[(0, p_1_shape)] = p_2_shape
    p_1_shape.known_transformations[(0, p_1_shape)] = p_2_shape

    p_0_shape.known_transformations[(0, p_2_shape)] = p_3_shape
    p_1_shape.known_transformations[(0, p_2_shape)] = p_3_shape
    p_2_shape.known_transformations[(0, p_2_shape)] = p_3_shape

    p_0_shape.known_transformations[(0, p_3_shape)] = p_4_shape
    p_1_shape.known_transformations[(0, p_3_shape)] = p_4_shape
    p_2_shape.known_transformations[(0, p_3_shape)] = p_4_shape
    p_3_shape.known_transformations[(0, p_3_shape)] = p_4_shape

# _setup_shapes()


def _p(x):
    return cons("p", x)

zero = w_nil

def make_succ():
    x = Variable("x")
    l = lamb( ([x], _p(x)) )
    l._name = "succ"
    return l

succ = make_succ()

def make_pred():
    x = Variable("x")
    l = lamb(
        ([_p(zero)], zero),
        ([_p(x)   ], x))
    l._name = "pred"
    return l

pred = make_pred()

def make_plus():
    x1 = Variable("x")
    x2 = Variable("x")
    x3 = Variable("x")
    y = Variable("y")

    l = lamb()
    l._rules = ziprules(
        ([zero, zero ], zero),
        ([x1  , zero ], x1),
        ([zero, x2   ], x2),
        ([x3  , _p(y)], _p(mu(l, x3, y))))
    l._name = "plus"
    return l

plus = make_plus()

def make_plus_acc():
    x1 = Variable("x")
    x2 = Variable("x")
    x3 = Variable("x")
    y = Variable("y")

    a1 = Variable("accumulator")
    a2 = Variable("accumulator")
    o1 = Variable("op")
    l_acc = lamb()
    l_acc._rules = ziprules(
        ([a1,   zero], a1),
        ([a2, _p(o1)], mu(l_acc, _p(a2), o1)))
    l_acc.name = "plus/a"

    l = lamb()
    l._rules = ziprules(
        ([zero, zero ], zero),
        ([x1  , zero ], x1),
        ([zero, x2   ], x2),
        ([x3  , y    ], mu(l_acc, x3, y)))
    l._name = "plus"
    return l

plus_acc = make_plus_acc()


def make_mult():
    _1 = Variable("_")
    _2 = Variable("_")
    x = Variable("x")
    y = Variable("y")

    l = lamb()
    l._rules = ziprules(
        ([_1  , zero ], zero),
        ([zero, _2   ], zero),
        ([x   , _p(y)], mu(plus, mu(l, x, y), x)))
        #([x   , _p(y)], mu(plus, x, mu(l, x, y))))
    l._name = "mult"
    return l

mult = make_mult()

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
    l_acc._rules = ziprules(
        ([zero, zero, a1], a1),
        ([_f1,  zero, a2], a2),
        ([zero,  _f2, a3], a3),
        ([f1, _p(f2), a4], mu(l_acc, f1, f2, mu(plus_acc, a4, f1))))
    l_acc.name = "mult/a"

    _1 = Variable("_")
    _2 = Variable("_")
    x = Variable("x")
    y = Variable("y")

    l = lamb()
    l._rules = ziprules(
        ([_1  , zero ], zero),
        ([zero, _2   ], zero),
        ([x   , y    ], mu(l_acc, x, y, zero)))
        # ([x   , _p(y)], mu(plus, mu(l, x, y), x)))
        #([x   , _p(y)], mu(plus, x, mu(l, x, y))))
    l._name = "mult"
    return l

mult_acc = make_mult_acc()



def peano_num(pynum):
    res = w_nil
    for i in range(pynum):
        res = cons("p", res)
    return res

def python_num(peano):
    p = peano
    res = 0
    while p.get_tag() is not t_nil:
        res += 1
        p = p.get_child(0)
    return res




__all__ = [
    'zero',
    'succ', 'pred',
    'plus', 'mult',
    'plus_acc', 'mult_acc',
    'peano_num', 'python_num',
]
