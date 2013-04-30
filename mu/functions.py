#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb.util.construction_helper import (integer, w_nil, conslist, run)
from lamb.execution import W_Integer, W_Object

from mu.lists import *
from mu.peano import *

def parse(fmt, arg):
    """
    fmt mapping
        i    W_Integer
        p    peano-number (from int)
        l    cons-list
        f    function name
        ...
    """
    if False: pass
    elif "i" == fmt:
        return integer(int(arg))
    elif "p" == fmt:
        return peano_num(int(arg))
    elif "l" == fmt:
        return parse_list(arg)
    elif "f" == fmt:
        try:
            return all_functions[arg].lamb
        except KeyError:
            raise ValueError("unknown function")
    else:
        raise ValueError("unknown argfmt")

def parse_list(arg):
    """
    [num;]fmt:elem,fmt:elem[,f:func]
    """
    num = -1
    num_elem = arg.split(";")
    if len(num_elem) > 1:
        num = int(num_elem[0])
    elements = num_elem[-1].split(",")
    elements_given = len(elements)
    max_index = num if num > -1 else elements_given

    fun = None
    l = [None] * max_index

    for index in range(max_index):
        if index >= elements_given:
            if fun is None:
                l[index] = l[index - 1]
            else:
                l[index] = fun.apply_to(l[index - 1])
        else:
            fmt, e = elements[index].split(":")
            if fmt == "f":
                fun = list_fun(e)
                l[index] = fun.apply_to(l[index - 1])
            else:
                l[index] = parse(fmt, e)
    return conslist(l)

def list_fun(arg):
    try:
        return all_functions[arg]
    except KeyError:
        try:
            return primitive_functions[arg]
        except KeyError:
            raise ValueError("unknown function")

def format(ret):
    from lamb.execution import W_Constructor, W_Lambda
    if isinstance(ret, W_Integer):
        return "%d" % ret._value
    elif isinstance(ret, W_Constructor):
        t = ret.get_tag().name
        if t == "p":
            return "%d" % python_num(ret)
        elif t == "cons":
            return "(" + ",".join(format_list(ret)) + ")"
        else:
            raise ValueError("unknown constr")
    elif isinstance(ret, W_Lambda):
        return ret._name
    else:
        raise ValueError("unknown retfmt")

def format_list(c_list):
    result = []
    conses = c_list
    while conses != w_nil:
        print conses.get_tag().name
        res = conses.get_child(0)
        result.append(format(res))
        conses = conses.get_child(1)
    return result

class CanApply(object):
    def apply_to(self, arg):
        raise NotImplementedError("abstract")


class Function(CanApply):
    """
    Lambda function wrapper.
    fmt is a string consisting of one char per argument.
    """
    def __init__(self, lamb, argfmt, doc):
        self.lamb = lamb
        assert len(argfmt) == lamb.arity()
        self.argfmt = argfmt
        self.doc = doc

    def parse_arg(self, position, arg):
        assert position < len(self.argfmt)
        argtype = self.argfmt[position]
        return parse(argtype, arg)

    def format_ret(self, ret):
        return format(ret)

    def arity(self):
        return self.lamb.arity()

    def apply_to(self, arg):
        return run(self.lamb, [arg])

class PrimitiveFunction(CanApply):
    def __init__(self, fun):
        self.fun = fun

    def apply_to(self, arg):
        return self.fun(arg)

def plus_one(arg):
    assert isinstance(arg, W_Integer)
    return integer(arg._value + 1)
def minus_one(arg):
    assert isinstance(arg, W_Integer)
    return integer(arg._value - 1)
def mult_two(arg):
    assert isinstance(arg, W_Integer)
    return integer(arg._value * 2)
# def rand_int(arg):
#     # no arg
#     import random
#     return integer(random.randint(0,1024))


primitive_functions = {
    "+": PrimitiveFunction(plus_one),
    "-": PrimitiveFunction(minus_one),
    "*": PrimitiveFunction(mult_two),
    # "r": PrimitiveFunction(rand_int),
}


all_functions = {
    # Peano arithmetics
    "succ": Function(succ, "p",
                     "Successor of a peano number"),
    "pred": Function(pred, "p",
                     "Predecessor of a peano number"),
    "plus": Function(plus, "pp",
                     "Add two peano numbers"),
    "mult": Function(mult, "pp",
                     "Multiply two peano numbers"),
    "plusa": Function(plus_acc, "pp",
                      "Add two peano nums, using accumulator"),
    "multa": Function(mult_acc, "pp",
                      "Multiply two peano nums, using accumulator"),
    # List processing
    "append": Function(append, "ll",
                       "Append a list to another"),
    "reverse": Function(reverse, "l",
                        "Reverse a list"),
    "map": Function(map, "fl",
                    "Apply a function to all elements of a list"),
}