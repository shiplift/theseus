#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
import py

from lamb.execution import *
from lamb.model import *
from lamb.expression import *
from lamb.pattern import *
from mu.peano import *
from lamb.util.construction_helper import (pattern, cons, integer,
                                           expression, ziprules,
                                           lamb,mu,
                                           w_nil,
                                           conslist, plist,
                                           execution_stack, operand_stack)
#
# Tests
#
class TestPattern(object):

    def test_int_pattern(self):
        w_int = integer(1)
        pat = pattern(w_int)
        w_obj = integer(1)

        binding = []
        pat.match(w_obj, binding)
        assert True # should not raise.

        w_obj = integer(2)
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)



    def test_catch_all(self):
        var = Variable("x")
        pat = pattern(var)
        w_obj = cons("barf")
        binding = [None]
        var.binding_index = 0
        pat.match(w_obj, binding)
        assert binding[var.binding_index] == w_obj


    def test_simple_constructor(self):
        w_cons = cons("barf")
        pat = pattern(w_cons)
        w_obj = cons("barf")

        binding = []
        pat.match(w_obj, binding)
        assert binding == []

        w_obj = cons("zork")
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)


    def test_constructor_with_int(self):
        w_cons = cons("zork", integer(1))
        pat = pattern(w_cons)
        w_obj = cons("zork", integer(1))

        binding = []
        pat.match(w_obj, binding)
        assert binding == []

        w_obj = cons("zork", integer(2))
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)


    def test_nested_constructor(self):
        pat = pattern(cons("barf", cons("zork")))
        w_obj = cons("barf", cons("zork"))

        binding = []
        pat.match(w_obj, binding)
        assert binding == []

        w_obj = cons("barf", cons("moep"))
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)


    def test_constructor_with_var(self):
        var = Variable("x")
        pat = pattern(cons("zork", var))
        w_int = integer(1)
        w_obj = cons("zork", w_int)

        binding = [None]
        var.binding_index = 0
        pat.match(w_obj, binding)
        assert binding[var.binding_index] == w_int

    def test_complex(self):

        var1 = Variable("x")
        var1.binding_index = 0
        var2 = Variable("y")
        var2.binding_index = 1
        var3 = Variable("z")
        var3.binding_index = 2
        var4 = Variable("a")
        var4.binding_index = 3
        var5 = Variable("b")
        var5.binding_index = 4
        var6 = Variable("c")
        var6.binding_index = 5

        w_int1 = integer(1)
        w_int2 = integer(2)
        w_int3 = integer(3)

        w_cons1 = cons("zork")
        w_cons2 = cons("barf", w_int1, w_int2)
        w_cons3 = cons("moep", w_cons1)
        w_cons4 = cons("universe", w_cons2, w_cons3)

        pat1 = pattern(cons("universe", var1, var2))
        pat2 = pattern(cons("moep", var3))
        pat3 = pattern(cons("universe", cons("barf", var4, var5), var6))

        binding = [None] * 6
        pat1.match(w_cons4, binding)
        assert binding[var1.binding_index] == w_cons2
        assert binding[var2.binding_index] == w_cons3

        binding = [None] * 6
        pat2.match(w_cons3, binding)
        assert binding[var3.binding_index] == w_cons1

        binding = [None] * 6
        pat3.match(w_cons4, binding)
        assert binding[var4.binding_index] == w_int1
        assert binding[var5.binding_index] == w_int2
        assert binding[var6.binding_index] == w_cons3

