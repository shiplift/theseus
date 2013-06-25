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
class TestVariable(object):

    def test_variable(self):
        res = Variable("x")
        assert isinstance(res, Variable)

        res2 = Variable("y")
        assert res2 is not res

        res3 = Variable("x")
        assert res3 is not res


class TestExpression(object):

    def test_simple_expression(self):
        w_int = integer(1)
        expr = expression(w_int)

        binding = []
        w_res = expr.evaluate_with_binding(binding)
        assert w_res is w_int

    def test_variable_expression(self):

        w_int = integer(42)
        var = Variable("x")
        var.binding_index = 0
        expr = expression(var)

        binding = [w_int]
        w_res = expr.evaluate_with_binding(binding)
        assert w_res is w_int

        with py.test.raises(VariableUnbound) as e:
            expr.evaluate_with_binding([None])

    def test_simple_constructor_expression(self):

        expr = w_constructor(tag("barf", 0), [])

        binding = []
        w_res = expr.evaluate_with_binding(binding)
        assert w_res.get_tag() is tag("barf", 0)
        assert w_res.get_number_of_children() is 0

    def test_constructor_with_int(self):
        for num in range(0, 12):
            w_int = integer(1)
            w_children = [w_int] * num
            w_cons = cons("zork", *w_children)
            expr = expression(w_cons)

            binding = []
            w_res = expr.evaluate_with_binding(binding)
            assert w_res == w_cons


    def test_constructor_with_var(self):
        var = Variable("x")
        var.binding_index = 0
        w_cons = cons("zork", var)
        w_int = integer(1)
        expr = expression(w_cons)

        binding = [w_int]
        w_res = expr.evaluate_with_binding(binding)
        assert w_res.get_child(0) == w_int

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

        expr1 = expression(cons("universe", var1, var2))
        expr2 = expression(cons("moep", var3))
        expr3 = expression(cons("universe", cons("barf", var4, var5), var6))

        binding = [w_cons2, w_cons3, w_cons1, w_cons2, w_cons3, w_cons1]

        w_res = expr1.evaluate_with_binding(binding)
        assert w_res.get_tag() is tag("universe", 2)
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is tag("barf", 2)
        assert w_child0.get_child(0) is w_int1
        assert w_child0.get_child(1) is w_int2
        w_child1 = w_res.get_child(1)
        assert w_child1.get_tag() is tag("moep", 1)
        assert w_child1.get_child(0).get_tag() is tag("zork", 0)

        w_res = expr2.evaluate_with_binding(binding)
        assert w_res.get_tag() is tag("moep", 1)
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is tag("zork", 0)

        w_res = expr3.evaluate_with_binding(binding)
        assert w_res.get_tag() is tag("universe", 2)
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is tag("barf", 2)
        w_child00 = w_child0.get_child(0)
        assert w_child00.get_tag() is tag("barf", 2)
        assert w_child00.get_child(0) is w_int1
        assert w_child00.get_child(1) is w_int2
        w_child01 = w_child0.get_child(1)
        assert w_child01.get_tag() is tag("moep", 1)
        assert w_child01.get_child(0).get_tag() is tag("zork", 0)
        w_child1 = w_res.get_child(1)
        assert w_child1.get_tag() is tag("zork", 0)



class TestRule(object):

    def test_catch_all(self):
        w_int = integer(1)

        rule = Rule([], expression(w_int))
        assert rule.arity == 0

        expr = rule.match_all([integer(2)], [])
        assert expr.evaluate_with_binding([]) is w_int

    def test_simple_rule(self):
        w_int = integer(1)
        expr = expression(w_int)
        rule = Rule([pattern(w_int)], expr)
        assert rule.arity == 1

        res = rule.match_all([w_int], [])
        assert res.evaluate_with_binding([]) is w_int

        with py.test.raises(NoMatch) as e:
            rule.match_all([integer(2)], [])

    def test_multi_rule(self):
        w_int0 = integer(0)
        w_int1 = integer(1)
        w_int2 = integer(2)

        expr = expression(w_int0)
        rule = Rule([pattern(w_int1), pattern(w_int2)], expr)
        assert rule.arity == 2

        res = rule.match_all([w_int1, w_int2], [])
        assert res.evaluate_with_binding([]) is w_int0

        with py.test.raises(NoMatch) as e:
            rule.match_all([w_int2, w_int1], [])

    def test_var_rule(self):
        w_int = integer(1)
        var = Variable("x")
        expr = expression(var)

        rule = Rule([pattern(var)], expr)
        binding = [None] * rule.maximal_number_of_variables
        res = rule.match_all([w_int], binding)
        result = res.evaluate_with_binding(binding)
        assert result is w_int
