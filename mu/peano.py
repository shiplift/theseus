#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb.execution import Variable
from lamb.util.construction_helper import (pattern, lamb, ziprules, mu, cons,
                                           plist, conslist, peano_num, python_num,
                                           operand_stack, execution_stack, w_nil)


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
    l._name = "mult"
    return l

mult = make_mult()



__all__ = [
    zero,
    succ, pred,
    plus, mult
]
