#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
import py

from lamb.execution import *
from lamb.util.construction_helper import (pattern, cons, integer, expression,
                                           ziprules, lamb, mu,
                                           w_nil,
                                           conslist, plist, peano_num, python_num,
                                           execution_stack, operand_stack)

#
# Tests
#

class TestSymbol(object):

    def test_newsymbol(self):
        w_res = W_Symbol("name")
        assert isinstance(w_res, W_Symbol)
        assert w_res.name == "name"

    def test_interning(self):
        w_res1 = symbol("name")
        w_res2 = symbol("name")
        assert w_res1 is w_res2

    def test_non_interning(self):
        w_res1 = W_Symbol("name")
        w_res2 = W_Symbol("name")
        assert w_res1 is not w_res2

class TestInteger(object):
    
    def test_futile(self):
        w_int = integer(1)
        assert isinstance(w_int, W_Integer)

class TestContstructor(object):

    def test_empty_constructor(self):
        w_res = cons("zork")
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 0

    def test_simple_constructor(self):
        w_res = cons("zork", integer(1))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 1

    def test_still_simple_constructor(self):
        w_res = cons("zork", integer(1), integer(2))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 2

    def test_simple_nested_constructor(self):
        w_res = cons("zork", cons("barf"))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 1

        w_subcons = w_res.get_child(0)
        assert isinstance(w_subcons, W_Constructor)
        assert w_subcons.get_tag() is symbol("barf")
        assert w_subcons.get_number_of_children() is 0

class TestVariable(object):

    def test_variable(self):
        res = Variable("x")
        assert isinstance(res, Variable)

        res2 = Variable("y")
        assert res2 is not res

        res3 = Variable("x")
        assert res3 is not res

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

        expr = W_Constructor(symbol("barf"), [])

        binding = []
        w_res = expr.evaluate_with_binding(binding)
        assert w_res.get_tag() is symbol("barf")
        assert w_res.get_number_of_children() is 0

    def test_constructor_with_int(self):
        w_int = integer(1)
        w_cons = cons("zork", w_int)
        expr = expression(w_cons)

        binding = []
        w_res = expr.evaluate_with_binding(binding)
        assert w_res.get_tag() == w_cons.get_tag()
        assert w_res.get_number_of_children() == w_cons.get_number_of_children()
        assert w_res.get_child(0) == w_int
        

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
        assert w_res.get_tag() is symbol("universe")
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is symbol("barf")
        assert w_child0.get_child(0) is w_int1
        assert w_child0.get_child(1) is w_int2
        w_child1 = w_res.get_child(1)
        assert w_child1.get_tag() is symbol("moep")
        assert w_child1.get_child(0).get_tag() is symbol("zork")

        w_res = expr2.evaluate_with_binding(binding)
        assert w_res.get_tag() is symbol("moep")
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is symbol("zork")

        w_res = expr3.evaluate_with_binding(binding)
        assert w_res.get_tag() is symbol("universe")
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is symbol("barf")
        w_child00 = w_child0.get_child(0)
        assert w_child00.get_tag() is symbol("barf")
        assert w_child00.get_child(0) is w_int1
        assert w_child00.get_child(1) is w_int2
        w_child01 = w_child0.get_child(1)
        assert w_child01.get_tag() is symbol("moep")
        assert w_child01.get_child(0).get_tag() is symbol("zork")
        w_child1 = w_res.get_child(1)
        assert w_child1.get_tag() is symbol("zork")

        
        
class TestRule(object):

    def test_catch_all(self):
        w_int = integer(1)
    
        rule = Rule([], expression(w_int))
        assert rule.arity() == 0

        expr = rule.match_all([integer(2)], [])
        assert expr.evaluate_with_binding([]) is w_int

    def test_simple_rule(self):
        w_int = integer(1)
        expr = expression(w_int)
        rule = Rule([pattern(w_int)], expr)
        assert rule.arity() == 1

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
        assert rule.arity() == 2

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
        
        succ = lamb( ([x1], cons("p", x1)) )

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
        
        expr = mu(l, conslist(list1_w), conslist(list2_w))
        res = interpret(execution_stack(expr))
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

        map = lamb()
        map._rules = ziprules(
            ([f, cons("cons", x, y)], cons("cons", mu(f, x), mu(map, f, y))),
            ([_, w_nil], w_nil))

        x1 = Variable("x")
        
        list_w = [peano_num(1),peano_num(2),peano_num(3)]
        # list_w = [peano_num(1)]
        
        succ = lamb( ([x1], cons("p", x1)) )

        res = interpret(execution_stack(mu(succ, peano_num(12))))
        assert python_num(res) == 13

        res = interpret(execution_stack(W_LambdaCursor(map)), operand_stack(succ, conslist(list_w)))
        assert plist(res) == [peano_num(2), peano_num(3), peano_num(4)]
        # assert plist(res) == [peano_num(2)]

    def test_reverse(self):

        a1 = Variable("accumulator")
        a2 = Variable("accumulator")
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

        global w_stack_max
        global e_stack_max

        w_stack_max = 0
        e_stack_max = 0

        def maxdepth(d):
            w_stack = d['w_stack']
            e_stack = d['e_stack']
            
            global w_stack_max
            global e_stack_max
            w_stack_list = w_stack.linearize() if w_stack is not None else []
            e_stack_list = e_stack.linearize() if e_stack is not None else []
            
            w_stack_max = max(w_stack_max, len(w_stack_list))
            e_stack_max = max(e_stack_max, len(e_stack_list))

        nums = 10
        list1_w = [integer(x) for x in range(nums)]
        res = interpret(execution_stack(W_LambdaCursor(reverse)), operand_stack(conslist(list1_w)), True, maxdepth)
        list1_w.reverse()
        assert plist(res) == list1_w

        e_stack_max1 = e_stack_max

        w_stack_max = 0
        e_stack_max = 0

        nums = 100
        list1_w = [integer(x) for x in range(nums)]
        interpret(execution_stack(W_LambdaCursor(reverse)), operand_stack(conslist(list1_w)), True, maxdepth)
        e_stack_max2 = e_stack_max

        assert e_stack_max2  == e_stack_max1

        w_stack_max = 0
        e_stack_max = 0

        nums = 1000
        list1_w = [integer(x) for x in range(nums)]
        interpret(execution_stack(W_LambdaCursor(reverse)), operand_stack(conslist(list1_w)), True, maxdepth)
        e_stack_max3 = e_stack_max

        assert e_stack_max3 == e_stack_max2
