#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
import py

from lamb.execution import *
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

class TestTag(object):

    def test_newtag(self):
        w_res = W_Tag("name", 0)
        assert isinstance(w_res, W_Tag)
        assert w_res.name == "name"
        assert w_res.arity == 0

    def test_interning(self):
        w_res1 = tag("name", 0)
        w_res2 = tag("name", 0)
        assert w_res1 is w_res2

        w_res1 = tag("name", 0)
        w_res2 = tag("name", 1)
        assert w_res1 is not w_res2

    def test_non_interning(self):
        w_res1 = W_Tag("name", 0)
        w_res2 = W_Tag("name", 0)
        assert w_res1 is not w_res2

class TestInteger(object):

    def test_futile(self):
        w_int = integer(1)
        assert isinstance(w_int, W_Integer)

class TestContstructor(object):

    def test_empty_constructor(self):
        w_res = cons("zork")
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is tag("zork", 0)
        assert w_res.get_number_of_children() is 0

    def test_simple_constructor(self):
        w_res = cons("zork", integer(1))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is tag("zork", 1)
        assert w_res.get_number_of_children() is 1

    def test_still_simple_constructor(self):
        w_res = cons("zork", integer(1), integer(2))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is tag("zork", 2)
        assert w_res.get_number_of_children() is 2

    def test_simple_nested_constructor(self):
        w_res = cons("zork", cons("barf"))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is tag("zork", 1)
        assert w_res.get_number_of_children() is 1

        w_subcons = w_res.get_child(0)
        assert isinstance(w_subcons, W_Constructor)
        assert w_subcons.get_tag() is tag("barf", 0)
        assert w_subcons.get_number_of_children() is 0

    def test_nary_constructors(self):
        for i in range(12):
            w_children = [integer(n) for n in range(i)]
            w_res = cons("zork", *w_children)

            assert isinstance(w_res, W_Constructor)
            assert w_res.get_tag() is tag("zork", len(w_children))
            assert w_res.get_number_of_children() is i
            if i > 0:
                assert w_res.get_child(i - 1) == integer(i - 1)

            with py.test.raises(IndexError) as e:
                w_res.get_child(i)


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

class TestLambda(object):

    def test_simple_lambda(self):
        w_int = integer(1)
        l = lamb( ([], w_int) )
        assert l.call([]) is w_int

    def test_fail_lambda(self):
        w_int1 = integer(1)
        w_int2 = integer(2)
        l = lamb( ([w_int1], w_int2) )

        with py.test.raises(NoMatch) as e:
            l.call([w_int2])

    def test_lambda_id(self):
        x = Variable("x")
        l = lamb( ([x], x) )
        w_int = integer(1)
        assert l.call([w_int]) is w_int

    def test_lambda_not(self):

        w_true = cons("true")
        w_false = cons("false")

        l = lamb(
            ([w_true], w_false),
            ([w_false], w_true))
        assert l.call([w_true]) == w_false
        assert l.call([w_false]) == w_true

    def test_append(self):

        x1 = Variable("x")
        x2 = Variable("x")
        h = Variable("head")
        t = Variable("tail")

        l = lamb()
        l._rules = ziprules(
            ([w_nil, x1], x1),
            ([cons("cons", h, t), x2], cons("cons", h, mu(l, t, x2))))

        list1_w = [integer(1),integer(2),integer(3)]
        list2_w = [integer(4),integer(5),integer(6)]
        assert plist(l.call([conslist(list1_w), conslist(list2_w)])) == list1_w + list2_w

    def test_shuffle(self):

        for i in range(20):
            vars = [Variable("x%s" % n) for n in range(i)]

            l = lamb(([cons("cons", *vars)], cons("cons", *(vars[1:] + vars[:1]))))
            l._name = "shuffle%s" % i

            list1 = [integer(n) for n in range(i)]
            w_cons1 = cons("cons", *list1)
            res = l.call([w_cons1])
            assert res == cons("cons", *(list1[1:] + list1[:1]))

    def test_muffle(self):

        for i in range(20):
            vars = [Variable("x%s" % n) for n in range(i)]

            vars2 = [Variable("x%s" % n) for n in range(i - 1)]

            m = lamb( (vars2, cons("cons", *vars2)) )
            m._name = "construct"

            l = lamb()
            l._name = "muffle%s" % i
            l._rules = ziprules(
                ([cons("cons", *vars)], mu(m, *vars[1:])))


            list1 = [integer(n) for n in range(i)]
            w_cons1 = cons("cons", *list1)
            res = l.call([w_cons1])
            assert res == cons("cons", *(list1[1:]))


    def test_map(self):
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

        map = lamb()
        map._rules = ziprules(
            ([f, cons("cons", x, y)], cons("cons", mu(f, x), mu(map, f, y))),
            ([_, w_nil], w_nil))

        x1 = Variable("x")

        list_w = [peano_num(1),peano_num(2),peano_num(3)]

        # succ = lamb( ([x1], cons("p", x1)) )

        res = map.call([succ, conslist(list_w)])
        assert plist(res) == [peano_num(2), peano_num(3), peano_num(4)]


class TestInterpret(object):

    def test_simple_lambda(self):
        w_int = integer(1)
        l = lamb( ([], w_int) )
        res = interpret(execution_stack(mu(l)))
        assert res is w_int

    def test_fail_lambda(self):
        w_int1 = integer(1)
        w_int2 = integer(2)
        l = lamb( ([w_int1], w_int2) )

        with py.test.raises(NoMatch) as e:
            res = interpret(execution_stack(mu(l, w_int2)))

    def test_lambda_id(self):
        x = Variable("x")
        l = lamb( ([x], x) )
        w_int = integer(1)
        res = interpret(execution_stack(mu(l, w_int)))
        assert res is w_int

    def test_lambda_not(self):

        w_true = cons("true")
        w_false = cons("false")

        l = lamb(
            ([w_true], w_false),
            ([w_false], w_true))

        res = interpret(execution_stack(mu(l, w_true)))
        assert res == w_false

        res = interpret(execution_stack(mu(l, w_false)))
        assert res == w_true

        res = interpret(execution_stack(W_LambdaCursor(l)), operand_stack(w_true))
        assert res == w_false

        res = interpret(execution_stack(W_LambdaCursor(l)), operand_stack(w_false))
        assert res == w_true

    def test_append(self):

        x1 = Variable("x")
        x2 = Variable("x")
        h = Variable("head")
        t = Variable("tail")

        l = lamb()
        l._name = "append"
        l._rules = ziprules(
            ([w_nil, x1], x1),
            ([cons("cons", h, t), x2], cons("cons", h, mu(l, t, x2))))


        list1_w = [integer(1),integer(2),integer(3)]
        list2_w = [integer(4),integer(5),integer(6)]

        res = interpret(execution_stack(W_LambdaCursor(l)), operand_stack(conslist(list1_w), conslist(list2_w)))
        assert plist(res) == list1_w + list2_w

    def test_map(self):
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

        x1 = Variable("x")

        list_w = [peano_num(1),peano_num(2),peano_num(3)]
        #list_w = [peano_num(1)]

        res = interpret(execution_stack(W_LambdaCursor(m)),
                        operand_stack(succ, conslist(list_w)))
        assert plist(res) == [peano_num(2), peano_num(3), peano_num(4)]
        #assert plist(res) == [peano_num(2)]

    def test_shuffle(self):

        for i in range(20):
            vars = [Variable("x%s" % n) for n in range(i)]

            l = lamb(([cons("cons", *vars)], cons("cons", *(vars[1:] + vars[:1]))))
            l._name = "shuffle%s" % i

            list1 = [integer(n) for n in range(i)]
            w_cons1 = cons("cons", *list1)
            res = interpret(execution_stack(W_LambdaCursor(l)), operand_stack(w_cons1))
            assert res == cons("cons", *(list1[1:] + list1[:1]))

    def test_muffle(self):

        for i in range(20):
            vars = [Variable("x%s" % n) for n in range(i)]

            vars2 = [Variable("x%s" % n) for n in range(i - 1)]

            m = lamb( (vars2, cons("cons", *vars2)) )
            m._name = "construct"

            l = lamb()
            l._name = "muffle%s" % i
            l._rules = ziprules(
                ([cons("cons", *vars)], mu(m, *vars[1:])))


            list1 = [integer(n) for n in range(i)]
            w_cons1 = cons("cons", *list1)
            res = interpret(execution_stack(W_LambdaCursor(l)), operand_stack(w_cons1))
            assert res == cons("cons", *(list1[1:]))


    def test_reverse(self):

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

        global op_stack_max
        global ex_stack_max

        op_stack_max = 0
        ex_stack_max = 0

        def maxdepth(d):
            op_stack = d['op_stack']
            ex_stack = d['ex_stack']

            global op_stack_max
            global ex_stack_max
            op_stack_list = op_stack.linearize() if op_stack is not None else []
            ex_stack_list = ex_stack.linearize() if ex_stack is not None else []

            op_stack_max = max(op_stack_max, len(op_stack_list))
            ex_stack_max = max(ex_stack_max, len(ex_stack_list))

        nums = 10
        list1_w = [integer(x) for x in range(nums)]
        res = interpret(execution_stack(W_LambdaCursor(reverse)), operand_stack(conslist(list1_w)), True, maxdepth)
        list1_w.reverse()
        assert plist(res) == list1_w

        ex_stack_max1 = ex_stack_max

        op_stack_max = 0
        ex_stack_max = 0

        nums = 100
        list1_w = [integer(x) for x in range(nums)]
        interpret(execution_stack(W_LambdaCursor(reverse)), operand_stack(conslist(list1_w)), True, maxdepth)
        ex_stack_max2 = ex_stack_max

        assert ex_stack_max2  == ex_stack_max1

        op_stack_max = 0
        ex_stack_max = 0

        nums = 1000
        list1_w = [integer(x) for x in range(nums)]
        interpret(execution_stack(W_LambdaCursor(reverse)), operand_stack(conslist(list1_w)), True, maxdepth)
        ex_stack_max3 = ex_stack_max

        assert ex_stack_max3 == ex_stack_max2

    def test_plus(self):

        a_w = peano_num(4)
        b_w = peano_num(5)

        ex_stack = execution_stack(W_LambdaCursor(plus))
        op_stack = operand_stack(a_w, b_w)

        res = interpret(ex_stack, op_stack)
        assert python_num(res) == 9

    def test_plus_acc(self):

        a_w = peano_num(4)
        b_w = peano_num(5)

        ex_stack = execution_stack(W_LambdaCursor(plus_acc))
        op_stack = operand_stack(a_w, b_w)

        res = interpret(ex_stack, op_stack)
        assert python_num(res) == 9

    def test_mult(self):

        a_w = peano_num(2)
        b_w = peano_num(3)

        ex_stack = execution_stack(W_LambdaCursor(mult))
        op_stack = operand_stack(a_w, b_w)

        res = interpret(ex_stack, op_stack)
        assert python_num(res) == 6
