#!/usr/bin/env python
# -*- coding: utf-8 -*-
#

#
# Construction Helper
#
from rpython.rlib import jit
from rpython.rlib.objectmodel import we_are_translated, not_rpython
from rpython.rlib.unroll import unrolling_iterable
from theseus.expression import (Variable, Rule,
                                W_VariableExpression,
                                w_call)
from theseus.object import Object
from theseus.pattern import (Pattern,
                             VariablePattern, ConstructorPattern, IntegerPattern)
from theseus.model import (W_Object, W_Integer, W_Constructor, W_Lambda,
                           tag, w_constructor)
from theseus.execution import interpret, interpret_expression

def nil():
    return w_constructor(tag("nil", 0), [])


@jit.elidable
def is_nil(constructor):
    return isinstance(constructor, W_Constructor) and constructor.get_tag() is tag("nil", 0)


def pattern(obj):
    assert isinstance(obj, Object)
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

def rules(tuples):
    return [Rule(item[0], item[1]) for item in tuples]

@not_rpython
def ziprules(*tuples):
    return [Rule([pattern(p) for p in item[0]], expression(item[1])) \
            for item in tuples]

def lamb(*tuples):
    """ new lambda """
    if we_are_translated():
        return W_Lambda([])
    else:
        return W_Lambda(ziprules(*tuples))

def mu(l, args):
    return w_call(expression(l), [expression(i) for i in args])

def conslist(p_list):
    result = nil()
    for element in reversed(p_list):
        result = cons("cons", element, result)
    return result

def plist(c_list):
    result = []
    conses = c_list
    while not is_nil(conses):
        assert isinstance(conses, W_Constructor)
        result.append(conses.get_child(0))
        conses = conses.get_child(1)
    return result

def run(lamb, args):
    return interpret_expression(mu(lamb, args))

def convert_arguments(arguments):
    from theseus import model
    return conslist([model.w_string(arg) for arg in arguments])

# EOF
