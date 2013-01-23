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


from lamb.execution import (l_interpret,
                            Variable, LambdaCursor, OperandStackElement)
from lamb.util.construction_helper import (lamb, ziprules, mu, cons, w_nil,
                                           conslist, integer)



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
        reverse_acc._rules = ziprules(
            ([w_nil,              a1], a1),
            ([cons("cons", h, t), a2], mu(reverse_acc, t, cons("cons", h, a2))))

        l = Variable("l")
        reverse = lamb(([l], mu(reverse_acc, l, w_nil)))


        nums = 5
        list1_w = [integer(x) for x in range(nums)]
        clist1_w = conslist(list1_w)
        def interp_w():
            return l_interpret(LambdaCursor(reverse), OperandStackElement(clist1_w))

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)
