#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb.expression import Variable
from lamb.model import tag
from lamb.shape import CompoundShape, in_storage_shape
from lamb.util.construction_helper import (pattern, lamb, ziprules, mu, cons,
                                           plist, conslist,
                                           operand_stack, execution_stack, w_nil)

t_cons = tag("cons", 2)

def _setup_shapes():
    cons_2 = t_cons

    cons_0_shape = cons_2.default_shape
    cons_1_shape = CompoundShape(cons_2, [in_storage_shape, cons_0_shape])
    cons_2_shape = CompoundShape(cons_2, [in_storage_shape, cons_1_shape])
    cons_3_shape = CompoundShape(cons_2, [in_storage_shape, cons_2_shape])
    cons_4_shape = CompoundShape(cons_2, [in_storage_shape, cons_3_shape])
    cons_5_shape = CompoundShape(cons_2, [in_storage_shape, cons_4_shape])

    cons_0_shape.known_transformations[(1, cons_0_shape)] = cons_1_shape
    cons_0_shape.known_transformations[(1, cons_1_shape)] = cons_2_shape
    cons_0_shape.known_transformations[(1, cons_2_shape)] = cons_3_shape
    cons_0_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
    cons_0_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

    cons_1_shape.known_transformations[(1, cons_1_shape)] = cons_2_shape
    cons_1_shape.known_transformations[(1, cons_2_shape)] = cons_3_shape
    cons_1_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
    cons_1_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

    cons_2_shape.known_transformations[(1, cons_2_shape)] = cons_3_shape
    cons_2_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
    cons_2_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

    cons_3_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
    cons_3_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

    cons_4_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape



def make_append():
    x1 = Variable("x")
    x2 = Variable("x")
    h = Variable("head")
    t = Variable("tail")

    l = lamb()
    l._name = "append"
    l._rules = ziprules(
        ([w_nil, x1], x1),
        ([cons("cons", h, t), x2], cons("cons", h, mu(l, t, x2))))
    return l
append = make_append()

def make_reverse():
    a1 = Variable("acc")
    a2 = Variable("acc")
    h = Variable("head")
    t = Variable("tail")
    reverse_acc = lamb()
    reverse_acc._name = "r_acc"

    reverse_acc._rules = ziprules(
        ([w_nil,              a1], a1),
        ([cons("cons", h, t), a2], mu(reverse_acc, t, cons("cons", h, a2))))

    l = Variable("list")
    reverse = lamb(([l], mu(reverse_acc, l, w_nil)))
    reverse._name = "reverse"
    return reverse
reverse = make_reverse()


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
    m._rules = ziprules(
        ([f, cons("cons", x, y)], cons("cons", mu(f, x), mu(m, f, y))),
        ([_, w_nil], w_nil))
    return m
map = make_map()

__all__ = [
    'reverse',
    'append',
    'map',
]
