#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#

import sys
from rpython import conftest
class o:
    view = False
    viewloops = True
conftest.option = o
from rpython.jit.metainterp.test.test_ajit import LLJitMixin


from lamb.execution import (interpret,
                            Variable, W_LambdaCursor, OperandStackElement)
from lamb.util.construction_helper import (lamb, ziprules, mu, cons, w_nil,
                                           conslist, integer, operand_stack,
                                           peano_num, execution_stack)
#
# Tests
#

class TestLLtype(LLJitMixin):
    
    def test_reverse(self):
        a1 = Variable("accumulator")
        a2 = Variable("accumulator")
        h = Variable("head")
        t = Variable("tail")
        reverse_acc = lamb()
        reverse_acc._name ="reverse_acc"
        reverse_acc._rules = ziprules(
            ([w_nil,              a1], a1),
            ([cons("cons", h, t), a2], mu(reverse_acc, t, cons("cons", h, a2))))

        l = Variable("l")
        reverse = lamb(([l], mu(reverse_acc, l, w_nil)))
        reverse._name = "reverse"


        nums = 5
        list1_w = [integer(x) for x in range(nums)]
        stack_w = operand_stack(conslist(list1_w))
        stack_e = execution_stack(W_LambdaCursor(reverse))
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_map(self):
        f = Variable("F")
        x = Variable("X")
        y = Variable("Y")
        _ = Variable("_")
        _2 = Variable("_")

        map = lamb()
        map._rules = ziprules(
            ([f, cons("cons", x, y)], cons("cons", mu(f, x), mu(map, f, y))),
            ([_, w_nil], w_nil))
        map._name = "map"
        
        x1 = Variable("x")
        
        list_w = [peano_num(x) for x in range(30)]
        clist_w = conslist(list_w)

        succ = lamb( ([x1], cons("p", x1)) )
        succ._name = "succ"
        stack_e = execution_stack(W_LambdaCursor(map))
        stack_w = operand_stack(succ, clist_w)
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_mult(self):
        from mu.peano import mult
        arg1 = peano_num(100)
        arg2 = peano_num(100)
        stack_e = execution_stack(W_LambdaCursor(mult))
        stack_w = operand_stack(arg1, arg2)
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)
        
