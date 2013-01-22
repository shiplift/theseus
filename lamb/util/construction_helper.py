#!/usr/bin/env python
# -*- coding: utf-8 -*-
#

#
# Construction Helper
#
from lamb.execution import *


def pattern(obj):
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
    _children = [pattern(w_constructor.get_child(i)) for i in range(w_constructor.get_number_of_children())]
    return ConstructorPattern(_tag, _children)

def pattern_from_integer(w_integer):
    return IntegerPattern(w_integer._value)

def cons(tag, *children):
    return W_Constructor(symbol(tag), list(children))

def integer(value):
    assert isinstance(value, int)
    return W_Integer(value)

def expression(obj):
    if isinstance(obj, Variable):
        return VariableExpression(obj)
    elif isinstance(obj, W_Integer) or isinstance(obj, W_Lambda):
        return ValueExpression(obj)
    elif isinstance(obj, W_Constructor):
        return expression_from_constructor(obj)
    elif isinstance(obj, Expression):
        return obj
    else:
        raise NotImplementedError("what expression?")

def expression_from_constructor(w_constructor):
    _tag = w_constructor.get_tag()
    _children = [expression(w_constructor.get_child(i)) for i in range(w_constructor.get_number_of_children())]
    return ConstructorExpression(_tag, _children)

def ziprules(*tuples):
    return [Rule([pattern(p) for p in item[0]], expression(item[1])) for item in tuples]

def lamb(*tuples):
    """ new lambda """
    return W_Lambda(ziprules(*tuples))

def mu(l, *args):
    return CallExpression(expression(l), [expression(i) for i in args])

w_nil = cons("nil")

def conslist(p_list):
    result = cons("nil")
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


def peano_num(pynum):
    res = w_nil
    for i in range(pynum):
        res = cons("p", res)
    return res
        
def python_num(peano):
    p = peano
    res = 0
    while p != w_nil:
        res += 1
        p = p.get_child(0)
    return res

# Not used yet
#class ForwardReference(object):
#
#    def become(self, x):
#        self.__class__ = x.__class__
#        self.__dict__.update(x.__dict__)
