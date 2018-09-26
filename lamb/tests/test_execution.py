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
from mu.peano import peano_num, python_num
from lamb.util.construction_helper import (pattern, cons, integer,
                                           expression, ziprules,
                                           lamb,mu,
                                           nil,
                                           conslist, plist)
#
# Tests
#


class __extend__(W_Lambda):
    def call(self, args_w):
        return interpret_expression(w_call(self, args_w))

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
            ([nil(), x1], x1),
            ([cons("cons", h, t), x2], cons("cons", h, mu(l, [t, x2]))))

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
                ([cons("cons", *vars)], mu(m, vars[1:])))


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
        from mu.peano import startup_peano, _succ
        startup_peano()

        f = Variable("F")
        x = Variable("X")
        y = Variable("Y")
        _ = Variable("_")
        _2 = Variable("_")

        map = lamb()
        map._rules = ziprules(
            ([f, cons("cons", x, y)], cons("cons", mu(f, [x]), mu(map, [f, y]))),
            ([_, nil()], nil()))

        x1 = Variable("x")

        list_w = [peano_num(1),peano_num(2),peano_num(3)]

        # succ = lamb( ([x1], cons("p", x1)) )

        res = map.call([_succ(), conslist(list_w)])
        assert plist(res) == [peano_num(2), peano_num(3), peano_num(4)]


class TestInterpret(object):

    def test_simple_lambda(self):
        w_int = integer(1)
        l = lamb( ([], w_int) )
        res = interpret_expression(mu(l, []))
        assert res is w_int

    def test_fail_lambda(self):
        w_int1 = integer(1)
        w_int2 = integer(2)
        l = lamb( ([w_int1], w_int2) )

        with py.test.raises(NoMatch) as e:
            res = interpret_expression(mu(l, [w_int2]))

    def test_lambda_id(self):
        x = Variable("x")
        l = lamb( ([x], x) )
        w_int = integer(1)
        res = interpret_expression(mu(l, [w_int]))
        assert res is w_int

    def test_lambda_not(self):

        w_true = cons("true")
        w_false = cons("false")

        l = lamb(
            ([w_true], w_false),
            ([w_false], w_true))

        res = interpret_expression(mu(l, [w_true]))
        assert res == w_false

        res = interpret_expression(mu(l, [w_false]))
        assert res == w_true


    def test_append(self):

        x1 = Variable("x")
        x2 = Variable("x")
        h = Variable("head")
        t = Variable("tail")

        l = lamb()
        l._name = "append"
        l._rules = ziprules(
            ([nil(), x1], x1),
            ([cons("cons", h, t), x2], cons("cons", h, mu(l, [t, x2]))))


        list1_w = [integer(1),integer(2),integer(3)]
        list2_w = [integer(4),integer(5),integer(6)]

        res = interpret_expression(mu(l, [conslist(list1_w), conslist(list2_w)]))
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
        from mu.peano import startup_peano, _succ
        startup_peano()

        f = Variable("F")
        x = Variable("X")
        y = Variable("Y")
        _ = Variable("_")
        _2 = Variable("_")

        m = lamb()
        m._name = "map"
        m._rules = ziprules(
            ([f, cons("cons", x, y)], cons("cons", mu(f, [x]), mu(m, [f, y]))),
            ([_, nil()], nil()))

        x1 = Variable("x")

        list_w = [peano_num(1),peano_num(2),peano_num(3)]
        #list_w = [peano_num(1)]

        res = interpret_expression(mu(m, [_succ(), conslist(list_w)]))
        assert plist(res) == [peano_num(2), peano_num(3), peano_num(4)]
        #assert plist(res) == [peano_num(2)]

    def test_shuffle(self):

        for i in range(20):
            vars = [Variable("x%s" % n) for n in range(i)]

            l = lamb(([cons("cons", *vars)],
                      cons("cons", *(vars[1:] + vars[:1]))))
            l._name = "shuffle%s" % i

            list1 = [integer(n) for n in range(i)]
            w_cons1 = cons("cons", *list1)
            res = interpret_expression(mu(l, [w_cons1]))
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
                ([cons("cons", *vars)], mu(m, vars[1:])))


            list1 = [integer(n) for n in range(i)]
            w_cons1 = cons("cons", *list1)
            res = interpret_expression(mu(l, [w_cons1]))
            assert res == cons("cons", *(list1[1:]))


    def test_plus(self):
        from mu.peano import startup_peano, _plus
        startup_peano()

        a_w = peano_num(4)
        b_w = peano_num(5)

        res = interpret_expression(mu(_plus(), [a_w, b_w]))
        assert python_num(res) == 9

    def test_plus_acc(self):
        from mu.peano import startup_peano, _plus_acc
        startup_peano()

        a_w = peano_num(4)
        b_w = peano_num(5)

        res = interpret_expression(mu(_plus_acc(), [a_w, b_w]))
        assert python_num(res) == 9

    def test_mult(self):
        from mu.peano import startup_peano, _mult
        startup_peano()

        a_w = peano_num(2)
        b_w = peano_num(3)

        res = interpret_expression(mu(_mult(), [a_w, b_w]))
        assert python_num(res) == 6

# EOF
