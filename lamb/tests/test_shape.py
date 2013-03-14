#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
import py

from lamb.execution import *
from lamb.shape import *
from lamb.util.construction_helper import (pattern, cons, integer, expression,
                                           ziprules, lamb, mu,
                                           w_nil,
                                           conslist, plist,
                                           execution_stack, operand_stack)


class TestShapeAccess(object):

    def test_simple_predefined_shape(self):

        w_1 = integer(1)

        barf_0 = tag("barf", 0)
        shape = CompoundShape(barf_0, [])
        c = W_NAryConstructor(shape)
        c._init_storage([])
        assert c.get_number_of_children() == 0

        barf_1 = tag("barf", 1)
        shape = CompoundShape(barf_1, [InStorageShape()])
        c = W_NAryConstructor(shape)
        c._init_storage([w_1])
        assert c.get_number_of_children() == 1
        assert c.get_child(0) == w_1

        barf_2 = tag("barf", 2)
        shape = CompoundShape(barf_2, [InStorageShape()] * 2)
        c = W_NAryConstructor(shape)
        c._init_storage([w_1, w_1])
        assert c.get_number_of_children() == 2
        assert c.get_child(0) == w_1
        assert c.get_child(1) == w_1

    def test_recursive_predefined_shape(self):

        w_1 = integer(1)

        barf_1 = tag("barf", 1)
        shape_1 = CompoundShape(barf_1, [InStorageShape()])
        c_1 = W_NAryConstructor(shape_1)
        c_1._init_storage([w_1])
        assert c_1.get_number_of_children() == 1
        assert c_1.get_child(0) == w_1

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [shape_1, shape_1])
        c_1_1 = W_NAryConstructor(shape_1)
        c_1_1._init_storage([w_1])
        c_2 = W_NAryConstructor(shape_2)
        c_2._init_storage([w_1, w_1])
        assert c_2.get_number_of_children() == 2
        assert c_2.get_child(0) == c_1
        assert c_2.get_child(0).get_child(0) == w_1
        assert c_2.get_child(1).get_child(0) == w_1

        foo_2 = tag("foo", 2)
        shape_3 = CompoundShape(foo_2, [shape_2, shape_2])
        c_1_3 = W_NAryConstructor(shape_1)
        c_1_3._init_storage([w_1])
        c_1_4 = W_NAryConstructor(shape_1)
        c_1_4._init_storage([w_1])
        c_2_1 = W_NAryConstructor(shape_2)
        c_2_1._init_storage([c_1_3, c_1_4])
        # foo(zork(barf(1),barf(1)),zork(barf(1),barf(1)))
        c_3 = W_NAryConstructor(shape_3)
        c_3._init_storage([w_1,w_1,w_1,w_1])
        assert c_3.get_number_of_children() == 2

        assert c_3.get_child(0) == c_2
        assert c_3.get_child(0).get_child(0) == c_1
        assert c_3.get_child(0).get_child(0).get_child(0) == w_1
        assert c_3.get_child(0).get_child(1) == c_1
        assert c_3.get_child(0).get_child(1).get_child(0) == w_1
        assert c_3.get_child(1).get_child(0).get_child(0) == w_1
        assert c_3.get_child(1).get_child(1).get_child(0) == w_1

    def test_recursive_mixed_predefined_shape(self):

        w_1 = integer(1)

        barf_1 = tag("barf", 1)
        shape_1 = CompoundShape(barf_1, [InStorageShape()])
        c_1 = W_NAryConstructor(shape_1)
        c_1._init_storage([w_1])
        assert c_1.get_number_of_children() == 1
        assert c_1.get_child(0) == w_1

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [shape_1, shape_1])
        c_1_1 = W_NAryConstructor(shape_1)
        c_1_1._init_storage([w_1])
        c_2 = W_NAryConstructor(shape_2)
        c_2._init_storage([w_1, w_1])
        assert c_2.get_number_of_children() == 2
        assert c_2.get_child(0) == c_1
        assert c_2.get_child(0).get_child(0) == w_1
        assert c_2.get_child(1).get_child(0) == w_1


        foo_2 = tag("foo", 2)
        # foo(zork(barf(1),barf(1)),zork(barf(1),barf(1)))
        shape_3 = CompoundShape(foo_2, [
                        CompoundShape(zork_2, [
                            shape_1,
                            InStorageShape()]),
                        InStorageShape()])
        c_1_3 = W_NAryConstructor(shape_1)
        c_1_3._init_storage([w_1])
        c_1_4 = W_NAryConstructor(shape_1)
        c_1_4._init_storage([w_1])
        s_2_1 = CompoundShape(zork_2, [InStorageShape(), InStorageShape()])
        c_2_1 = W_NAryConstructor(s_2_1)
        c_2_1._init_storage([c_1_3, c_1_4])

        # DIFFERENCE TO other test: not everything is flattened
        c_3 = W_NAryConstructor(shape_3)
        c_3._init_storage([
            # zork
            w_1,c_1_1,
            # zork
            c_2_1])
        assert c_3.get_number_of_children() == 2
        assert c_3.get_child(0) == c_2
        assert c_3.get_child(0).get_child(0) == c_1
        assert c_3.get_child(0).get_child(0).get_child(0) == w_1
        assert c_3.get_child(0).get_child(1) == c_1
        assert c_3.get_child(0).get_child(1).get_child(0) == w_1
        assert c_3.get_child(1).get_child(0).get_child(0) == w_1
        assert c_3.get_child(1).get_child(1).get_child(0) == w_1


class TestShapeMerger(object):
    u"""
    A Shape Merger takes the tag and new children of a to-be built
    constructor and tries to match wether the emerging shape and the
    existing shape have some form of transformation to a new shape.
    This shape is then used for building the constructor
    """

    def test_splice(self):
        from lamb.shape import _splice

        a = [1, 2, 3]
        len_a = len(a)
        b = [4, 5]
        len_b = len(b)
        c = []
        len_c = len(c)
        d = [6]
        len_d = len(d)
        x = _splice(a, len_a, 1, b, len_b)
        assert x == [1, 4 ,5, 3]

        y = _splice(a, len_a, 1, c, len_c)
        assert y == [1, 3]

        z = _splice(a, len_a, 1, d, len_d)
        assert z == [1, 6, 3]

        u = _splice(a, len_a, 0, d, len_d)
        assert u == [6, 2, 3]

        v = _splice(a,len_a,  0, b, len_b)
        assert v == [4, 5, 2, 3]

        w = _splice(a, len_a, 2, b, len_b)
        assert w == [1, 2, 4, 5]


    def test_simple_shape_non_merge(self):
        w_1 = integer(1)
        barf_0 = tag("barf", 0)
        shape_0 = CompoundShape(barf_0, [])
        storage = []
        (new_shape, new_storage) = shape_0.fusion(storage)
        assert new_shape == shape_0
        assert new_storage == storage

        w_1 = integer(1)
        barf_1 = tag("barf", 1)
        shape_1 = CompoundShape(barf_1, [InStorageShape()])
        storage = [w_1]
        (new_shape, new_storage) = shape_1.fusion(storage)
        assert new_shape == shape_1
        assert new_storage == storage

    def test_compound_shape_non_merge(self):
        w_1 = integer(1)

        barf_1 = tag("barf", 1)
        shape_1 = CompoundShape(barf_1, [InStorageShape()])
        c_1 = W_NAryConstructor(shape_1)
        c_1._init_storage([w_1])

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [InStorageShape(), InStorageShape()])
        c_1_1 = W_NAryConstructor(shape_1)
        c_1_1._init_storage([w_1])
        c_2 = W_NAryConstructor(shape_2)
        c_2._init_storage([c_1, c_1_1])

        foo_2 = tag("foo", 2)
        shape_3 = CompoundShape(foo_2, [shape_2, shape_2])
        c_1_3 = W_NAryConstructor(shape_1)
        c_1_3._init_storage([w_1])
        c_1_4 = W_NAryConstructor(shape_1)
        c_1_4._init_storage([w_1])
        c_2_1 = W_NAryConstructor(shape_2)
        c_2_1._init_storage([c_1_3, c_1_4])

        storage = [w_1, w_1, w_1, w_1]
        (new_shape, new_storage) = shape_3.fusion(storage)
        assert new_shape == shape_3
        assert new_storage == storage


    def test_compound_shape_merge_1(self):
        """
           (zork (barf 1) (barf 1))
        """
        w_1 = integer(1)

        barf_1 = tag("barf", 1)
        shape_1 = CompoundShape(barf_1, [InStorageShape()])
        c_1 = W_NAryConstructor(shape_1)
        c_1._init_storage([w_1])
        c_1_1 = W_NAryConstructor(shape_1)
        c_1_1._init_storage([w_1])

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [InStorageShape(), InStorageShape()])

        shape_2_1 = CompoundShape(zork_2, [shape_1, InStorageShape()])
        shape_2_2 = CompoundShape(zork_2, [InStorageShape(), shape_1])
        shape_2_3 = CompoundShape(zork_2, [shape_1, shape_1])

        shape_2.known_transformations[(0, shape_1)] = shape_2_1
        shape_2.known_transformations[(1, shape_1)] = shape_2_2

        shape_2_1.known_transformations[(1, shape_1)] = shape_2_3

        shape_2_2.known_transformations[(0, shape_1)] = shape_2_3

        storage = [c_1, c_1_1]

        (new_shape, new_storage) = shape_2.fusion(storage)

        assert new_shape == CompoundShape(zork_2, [shape_1, shape_1])
        assert new_storage == [w_1, w_1]

    def test_compound_shape_merge_2(self):
        """
           (foo (zork (barf 1) (barf 1)) (zork (barf 1) (barf 1)))
        """
        w_1 = integer(1)

        barf_1 = tag("barf", 1)
        shape_1 = CompoundShape(barf_1, [InStorageShape()])
        c_1 = W_NAryConstructor(shape_1)
        c_1._init_storage([w_1])
        c_1_1 = W_NAryConstructor(shape_1)
        c_1_1._init_storage([w_1])

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [InStorageShape(), InStorageShape()])

        shape_2_1 = CompoundShape(zork_2, [shape_1, InStorageShape()])
        shape_2_2 = CompoundShape(zork_2, [InStorageShape(), shape_1])
        shape_2_3 = CompoundShape(zork_2, [shape_1, shape_1])

        shape_2.known_transformations[(0, shape_1)] = shape_2_1
        shape_2.known_transformations[(1, shape_1)] = shape_2_2

        shape_2_1.known_transformations[(1, shape_1)] = shape_2_3

        shape_2_2.known_transformations[(0, shape_1)] = shape_2_3

        storage = [c_1, c_1_1]

        (new_shape, new_storage) = shape_2.fusion(storage)

        c_2 = W_NAryConstructor(new_shape)
        c_2._init_storage(new_storage)

        foo_2 = tag("foo", 2)
        shape_3 = CompoundShape(foo_2, [shape_2_3, InStorageShape()])

        shape_3_1 = CompoundShape(foo_2, [shape_2_3, shape_2_3])

        shape_3.known_transformations[(2, new_shape)] = shape_3_1
        storage = new_storage + [c_2]
        (new_shape, new_storage) = shape_3.fusion(storage)
        assert new_storage == [w_1, w_1, w_1, w_1]
        assert new_shape == CompoundShape(foo_2, [shape_2_3, shape_2_3])

    def test_cons_list(self):

        w_1 = integer(1)

        cons_ = tag("cons", 2)

        nil_ = tag("nil", 0)
        nil_shape = CompoundShape(nil_, [])
        w_nil_ = W_NAryConstructor(nil_shape)
        w_nil_._init_storage([])

        list_default_shape = CompoundShape(cons_, [InStorageShape(), InStorageShape()])

        list_1_shape = CompoundShape(cons_, [InStorageShape(), nil_shape])
        list_2_shape = CompoundShape(cons_, [InStorageShape(), list_1_shape])

        list_default_shape.known_transformations[(1,nil_shape)] = list_1_shape
        list_default_shape.known_transformations[(1,list_1_shape)] = list_2_shape

        w_list_0 = w_nil_

        (shape, storage) = list_default_shape.fusion([w_1, w_nil_])

        w_list_1 = W_NAryConstructor(shape)
        w_list_1._init_storage(storage)

        list_1_shape.known_transformations[(1, list_1_shape)] = list_2_shape

        (shape, storage) = list_default_shape.fusion([w_1, w_list_1])

        w_list_2 = W_NAryConstructor(shape)
        w_list_2._init_storage(storage)

        assert w_list_2._storage == [w_1, w_1]

    def test_default_shape(self):

        w_1 = integer(1)

        barf = tag("barf", 3)
        w_barf = w_constructor(barf, [w_1, w_1, w_1])

        assert w_barf._shape == CompoundShape(barf, [InStorageShape(), InStorageShape(), InStorageShape()])

        w_barf_1 = w_constructor(barf, [w_1, w_1, w_1])

        assert w_barf_1._shape is w_barf._shape

    def test_reverse(self):

        debug = True

        if debug:
            print ""

        a1 = Variable("accumulator")
        a2 = Variable("accumulator")
        h = Variable("head")
        t = Variable("tail")

        w_nil_shape = w_nil.shape()

        c = tag("cons", 2)
        cons_shape = c.default_shape
        cons_1_shape = CompoundShape(c, [InStorageShape(), cons_shape ])
        cons_2_shape = CompoundShape(c, [InStorageShape(), cons_1_shape])
        cons_3_shape = CompoundShape(c, [InStorageShape(), cons_2_shape])
        cons_4_shape = CompoundShape(c, [InStorageShape(), cons_3_shape])
        cons_5_shape = CompoundShape(c, [InStorageShape(), cons_4_shape])
        cons_shape.known_transformations[(1, cons_shape )] = cons_1_shape
        cons_shape.known_transformations[(1, cons_1_shape)] = cons_2_shape
        cons_shape.known_transformations[(1, cons_2_shape)] = cons_3_shape
        # cons_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
        # cons_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

        cons_1_shape.known_transformations[(1, cons_1_shape)] = cons_2_shape
        cons_1_shape.known_transformations[(1, cons_2_shape)] = cons_3_shape
        # cons_1_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
        # cons_1_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

        cons_2_shape.known_transformations[(1, cons_2_shape)] = cons_3_shape
        # cons_2_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
        # cons_2_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

        # cons_3_shape.known_transformations[(1, cons_3_shape)] = cons_4_shape
        # cons_3_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

        # cons_4_shape.known_transformations[(1, cons_4_shape)] = cons_5_shape

        reverse_acc = lamb()
        reverse_acc._name ="reverse_acc"
        reverse_acc._rules = ziprules(
            ([w_nil,              a1], a1),
            ([cons("cons", h, t), a2], mu(reverse_acc, t, cons("cons", h, a2))))

        l = Variable("l")
        reverse = lamb(([l], mu(reverse_acc, l, w_nil)))
        reverse._name = "reverse"

        def stackinspect(d):

            from lamb.util.debug import storagewalker

            op_stack = d['op_stack']
            ex_stack = d['ex_stack']

            if op_stack:
                if isinstance(op_stack._data, W_Constructor):
                    print "[W]", op_stack._data._shape, " storage: ", storagewalker(op_stack._data.get_storage())
                else:
                    print "[W]", op_stack._data
            else:
                print "[w] none"


        nums = 50
        list1_w = [integer(x) for x in range(nums)]
        clist1_w = conslist(list1_w)
        assert clist1_w.get_tag() is c

        debug_callback = stackinspect if debug else None
        res = interpret(execution_stack(W_LambdaCursor(reverse)), operand_stack(clist1_w), debug, debug_callback)
        list1_w.reverse()
        assert plist(res) == list1_w

    def test_mult(self):
        import mu.peano
        from mu.peano import peano_num, python_num, mult

        n = 10
        # n = 100
        arg1 = peano_num(n)
        arg2 = peano_num(n)
        stack_e = execution_stack(W_LambdaCursor(mult))
        stack_w = operand_stack(arg1, arg2)
        res = interpret(stack_e, stack_w, True)
        assert python_num(res) == n * n



class TestShapeRecorder(object):

    def test_simple_record(self):
        w_1 = integer(1)
        ferb_1 = tag("ferb_0", 1)
        s = ferb_1.default_shape

        children = [w_1]
        new_shape, new_storage = s.merge(children)
        s.record_shapes(new_shape, new_storage)

        assert hasattr(s, "_count_for")
        assert s._count_for( (w_1, 0) ) == 0

        children = [w_nil]
        new_shape, new_storage = s.merge(children)
        s.record_shapes(new_shape, new_storage)

        assert hasattr(s, "_count_for")
        assert s._count_for( (w_nil, 0) ) == 1

    def test_simple_autosubsititution(self):
        CompoundShape._subsititution_threshold = 1

        ferb_1 = tag("ferb_1", 1)
        shape = ferb_1.default_shape

        children = [w_nil]
        new_shape, new_storage = shape.merge(children)
        shape.record_shapes(new_shape, new_storage)

        assert hasattr(shape, "_hist")
        assert len(shape._hist) > 0
        assert new_shape is shape

        c = W_NAryConstructor(new_shape)
        c._init_storage(new_storage)

        children_1 = [c]
        new_shape_1, new_storage_1 = shape.merge(children_1)
        shape.record_shapes(new_shape_1, new_storage_1)

        assert len(shape._hist) > 1
        assert new_shape_1 is shape

        children_2 = [c]
        new_shape_2, new_storage_2 = shape.merge(children_2)
        # shape.record_shapes(new_shape_1, new_storage_1)

        # assert len(shape._hist) > 1
        assert new_shape_2 is not shape
