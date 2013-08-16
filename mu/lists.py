#!/usr/bin/env python
# -*- coding: utf-8 -*-

from rpython.rlib.nonconst import NonConstant
from lamb.startup import startup

from lamb.expression import Variable
from lamb.model import tag
from lamb.shape import CompoundShape, in_storage_shape
from lamb.util.construction_helper import (pattern as p, expression as e,
                                           lamb, mu, cons,
                                           plist, conslist, rules,
                                           operand_stack, execution_stack, nil)


def _setup_shapes(t_cons):
    cons_2 = t_cons

    cons_0_shape = cons_2.default_shape
    cons_1_shape = CompoundShape(cons_2, [in_storage_shape, cons_0_shape])
    cons_2_shape = CompoundShape(cons_2, [in_storage_shape, cons_1_shape])
    cons_3_shape = CompoundShape(cons_2, [in_storage_shape, cons_2_shape])
    cons_4_shape = CompoundShape(cons_2, [in_storage_shape, cons_3_shape])
    cons_5_shape = CompoundShape(cons_2, [in_storage_shape, cons_4_shape])

    cons_0_shape.transformation_rules[(1, cons_0_shape)] = cons_1_shape
    cons_0_shape.transformation_rules[(1, cons_1_shape)] = cons_2_shape
    cons_0_shape.transformation_rules[(1, cons_2_shape)] = cons_3_shape
    cons_0_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
    cons_0_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

    cons_1_shape.transformation_rules[(1, cons_1_shape)] = cons_2_shape
    cons_1_shape.transformation_rules[(1, cons_2_shape)] = cons_3_shape
    cons_1_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
    cons_1_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

    cons_2_shape.transformation_rules[(1, cons_2_shape)] = cons_3_shape
    cons_2_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
    cons_2_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

    cons_3_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
    cons_3_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

    cons_4_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape



def make_append():
    x1 = Variable("x")
    x2 = Variable("x")
    h = Variable("head")
    t = Variable("tail")

    l = lamb()
    l._name = "append"
    l._rules = rules([
        ([p(nil()), p(x1)],
         e(x1)),
        ([p(cons("cons", h, t)), p(x2)],
         e(cons("cons", h, mu(l, [t, x2]))))])
    return l

def make_reverse():
    a1 = Variable("acc")
    a2 = Variable("acc")
    h = Variable("head")
    t = Variable("tail")
    reverse_acc = lamb()
    reverse_acc._name = "r_acc"

    reverse_acc._rules = rules([
        ([p(nil()),              p(a1)],
         e(a1)),
        ([p(cons("cons", h, t)), p(a2)],
         e(mu(reverse_acc, [t, cons("cons", h, a2)])))])

    l = Variable("list")
    reverse = lamb()
    reverse._rules = rules([
        ([p(l)], mu(reverse_acc, [l, nil()]))
    ])
    reverse._name = "reverse"
    return reverse


def make_map():
    """
    in scheme
     (define (map proc lis)
       (cond ((null? lis)
              '())
             ((pair? lis)
              (cons (proc (car lis))
                    (map proc (cdr lis))))))

    nil ≔ (nil)
    map ≔ λ:
        F, (cons X, Y) ↦ (cons μ(F, X), μ(map, F, Y))
        _, nil         ↦ nil
    """

    f = Variable("F")
    x = Variable("X")
    y = Variable("Y")
    _ = Variable("_")
    _2 = Variable("_")

    m = lamb()
    m._name = "map"
    m._rules = rules([
        ([p(f), p(cons("cons", x, y))],
         e(cons("cons", mu(f, [x]), mu(m, [f, y])))),
        ([p(_), p(nil())             ],
         e(nil()))])
    return m

g = {'functions':{}}
functions = g['functions']

@startup
def startup_list():
    if len(functions) != 0:
        return

    functions['append'] = make_append()
    functions['reverse'] = make_reverse()
    functions['map'] = make_map()

def _append():  return functions.get('append', None)
def _reverse(): return functions.get('reverse', None)
def _map():     return functions.get('map', None)
