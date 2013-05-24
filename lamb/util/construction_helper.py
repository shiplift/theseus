#!/usr/bin/env python
# -*- coding: utf-8 -*-
#

#
# Construction Helper
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from lamb.execution import *

t_nil = tag("nil", 0)
w_nil = w_constructor(t_nil, [])

@jit.elidable
def is_nil(constructor):
    return constructor.get_tag() is t_nil


def pattern(obj):
    if isinstance(obj, Pattern):
        return obj
    if isinstance(obj, Variable):
        return VariablePattern(obj)
    elif isinstance(obj, W_Integer):
        return pattern_from_integer(obj)
    elif isinstance(obj, W_Constructor):
        return pattern_from_constructor(obj)
    else:
        raise NotImplementedError("what pattern?")


def pattern_from_constructor(w_constructor):
    _tag = w_constructor.get_tag()
    _children = [pattern(w_constructor.get_child(i)) \
                 for i in range(w_constructor.get_number_of_children())]
    return ConstructorPattern(_tag, _children)

def pattern_from_integer(w_integer):
    return IntegerPattern(w_integer._value)

def cons(t, *children):
    ch = list(children)
    return w_constructor(tag(t, len(ch)), ch)


def integer(value):
    assert isinstance(value, int)
    return W_Integer(value)

def expression(obj):
    if isinstance(obj, Variable):
        return W_VariableExpression(obj)
    if isinstance(obj, W_Constructor):
        return w_constructor(obj.get_tag(),
                             [expression(x) for x in obj.get_children()])
    else:
        return obj

def ziprules(*tuples):
    return [Rule([pattern(p) for p in item[0]],
                 expression(item[1])) for item in tuples]

def lamb(*tuples):
    """ new lambda """
    return W_Lambda(ziprules(*tuples))

def mu(l, *args):
    return w_call(expression(l), [expression(i) for i in args])

def conslist(p_list):
    result = w_nil
    for element in reversed(p_list):
        result = cons("cons", element, result)
    return result

def plist(c_list):
    result = []
    conses = c_list
    while conses != w_nil:
        result.append(conses.get_child(0))
        conses = conses.get_child(1)
    return result

def operand_stack(*elems):
    stack = None
    for elem in reversed(elems):
        stack = OperandStackElement(elem, stack)
    return stack

def execution_stack(*elems):
    stack = None
    for elem in reversed(elems):
        stack = ExecutionStackElement(elem, stack)
    return stack

def run(lamb, args):
    ex = ExecutionStackElement(W_LambdaCursor(lamb))
    op = None
    l = len(args)
    for i in range(l - 1, -1, -1):
        op = OperandStackElement(args[i], op)
    return interpret(ex, op)

# EOF
