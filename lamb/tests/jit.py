#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#

import sys
import py
from rpython import conftest
class o:
    view = False
    viewloops = True
#    viewloops = False
conftest.option = o
from rpython.jit.metainterp.test.test_ajit import LLJitMixin

from lamb.model import tag
from lamb.execution import interpret, W_LambdaCursor
from lamb.expression import Variable
from lamb.stack import OperandStackElement
from lamb.shape import in_storage_shape, CompoundShape

from lamb.util.construction_helper import (pattern as p, expression as e,
                                           lamb, ziprules, mu, cons, nil,
                                           conslist, integer, operand_stack,
                                           execution_stack, rules)
from mu.peano import (peano_num, python_num,
                      _plus, _plus_acc, _mult, _mult_acc,
                  )
from mu.gcbench import (_gc_bench)

#
# Tests
#

def setup_module(module):
    from lamb.startup import boot
    boot()

class TestLLtype(LLJitMixin):


    def test_simplyverse(self):
        """ simpleverse without anything """
        CompoundShape._config._inhibit_all = True
        return self.test_reverse()

    def test_simpleverse(self):
        # name chosen to not conflict with pytest.py -kreverse
        from mu.lists import make_reverse
        reverse = make_reverse()

        nums = 149
        # XXX >= 150 does not work oO
        list1_w = [integer(x) for x in range(nums)]
        clist1_w = conslist(list1_w)
        stack_w = operand_stack(clist1_w)
        stack_e = execution_stack(W_LambdaCursor(reverse))
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)
        clist1_w.get_tag().default_shape.print_transforms()


    def test_iverse(self):
        """ reverse without anything """
        CompoundShape._config._inhibit_all = True
        return self.test_reverse()

    def test_reverse(self):
        a1 = Variable("accumulator")
        a2 = Variable("accumulator")
        h = Variable("head")
        t = Variable("tail")

        # nil()_shape = nil().shape()

        c = tag("cons", 2)
        cons_shape = c.default_shape
        # cons_1_shape = CompoundShape(c, [in_storage_shape, w_nil_shape ])
        cons_1_shape = CompoundShape(c, [in_storage_shape, cons_shape])
        cons_2_shape = CompoundShape(c, [in_storage_shape, cons_1_shape])
        cons_3_shape = CompoundShape(c, [in_storage_shape, cons_2_shape])
        cons_4_shape = CompoundShape(c, [in_storage_shape, cons_3_shape])
        # cons_5_shape = CompoundShape(c, [in_storage_shape, cons_4_shape])

        # cons_shape.transformation_rules[(1, w_nil_shape )] = cons_1_shape
        cons_shape.transformation_rules[(1, cons_shape )] = cons_1_shape
        cons_shape.transformation_rules[(1, cons_1_shape)] = cons_2_shape
        cons_shape.transformation_rules[(1, cons_2_shape)] = cons_3_shape
        cons_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
        # cons_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

        cons_1_shape.transformation_rules[(1, cons_1_shape)] = cons_2_shape
        cons_1_shape.transformation_rules[(1, cons_2_shape)] = cons_3_shape
        cons_1_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
        # cons_1_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

        cons_2_shape.transformation_rules[(1, cons_2_shape)] = cons_3_shape
        cons_2_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
        # cons_2_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

        cons_3_shape.transformation_rules[(1, cons_3_shape)] = cons_4_shape
        # cons_3_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

        # cons_4_shape.transformation_rules[(1, cons_4_shape)] = cons_5_shape

        reverse_acc = lamb()
        reverse_acc._name ="reverse_acc"
        reverse_acc._rules = ziprules(
            ([nil(),              a1], a1),
            ([cons("cons", h, t), a2], mu(reverse_acc, [t, cons("cons", h, a2)])))

        l = Variable("l")
        reverse = lamb(([l], mu(reverse_acc, [l, nil()])))
        reverse._name = "reverse"


        nums = 149
        # XXX >= 150 does not work oO
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
            ([f, cons("cons", x, y)], cons("cons", mu(f, [x]), mu(map, [f, y]))),
            ([_, nil()], nil()))
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

        #interp_w() # fill the transition maps
        CompoundShape._config._inhibit_recognition = True
        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

        import pdb; pdb.set_trace()
        list_w = [peano_num(x) for x in range(30)]
        clist_w = conslist(list_w)
        stack_e = execution_stack(W_LambdaCursor(map))
        stack_w = operand_stack(succ, clist_w)
        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_mult(self):
        arg1 = peano_num(50)
        arg2 = peano_num(50)
        stack_e = execution_stack(W_LambdaCursor(_mult()))
        stack_w = operand_stack(arg1, arg2)
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_mulacc(self):
        arg1 = peano_num(50)
        arg2 = peano_num(50)
        stack_e = execution_stack(W_LambdaCursor(_mult_acc()))
        stack_w = operand_stack(arg1, arg2)
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_plus(self):
        arg1 = peano_num(50)
        arg2 = peano_num(50)
        stack_e = execution_stack(W_LambdaCursor(_plus()))
        stack_w = operand_stack(arg1, arg2)
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_pluacc(self):
        arg1 = peano_num(100)
        arg2 = peano_num(100)
        stack_e = execution_stack(W_LambdaCursor(_plus_acc()))
        stack_w = operand_stack(arg1, arg2)
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_pgcbench(self):
        arg1 = peano_num(100)
        arg2 = peano_num(100)
        stack_e = execution_stack(W_LambdaCursor(_gc_bench()))
        stack_w = operand_stack()
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_gc_bench(self):
        from lamb.util.construction_helper import interpret, nil
        from lamb.parser import parse_file
        from lamb.execution import toplevel_bindings

        filename = str(py.path.local(__file__).dirpath().dirpath().dirpath("gc_bench.lamb"))
        expressions, bindings = parse_file(filename)
        toplevel_bindings.set_bindings(bindings)

        stack_e = execution_stack(expressions[-1])
        stack_w = operand_stack(nil())
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)

    def test_arbitraty_precision_ints(self):
        from lamb.util.construction_helper import interpret, nil
        from lamb.parser import parse_file
        from lamb.execution import toplevel_bindings

        filename = str(py.path.local(__file__).dirpath().dirpath().dirpath("arbitraty_precision_ints.lamb"))
        expressions, bindings = parse_file(filename)
        toplevel_bindings.set_bindings(bindings)

        stack_e = execution_stack(expressions[-1])
        stack_w = operand_stack(nil())
        def interp_w():
            return interpret(stack_e, stack_w)

        self.meta_interp(interp_w, [], listcomp=True, listops=True, backendopt=True)
