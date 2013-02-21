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
        c = W_Constructor(shape, [])
        assert c.get_number_of_children() == 0

        barf_1 = tag("barf", 1)
        shape = CompoundShape(barf_1, [InStorageShape()])
        c = W_Constructor(shape, [w_1])
        assert c.get_number_of_children() == 1
        assert c.get_child(0)  == w_1

        barf_2 = tag("barf", 2)
        shape = CompoundShape(barf_2, [InStorageShape()] * 2)
        c = W_Constructor(shape, [w_1, w_1])
        assert c.get_number_of_children() == 2
        assert c.get_child(0)  == w_1
        assert c.get_child(1)  == w_1

    def test_recursive_predefined_shape(self):

        w_1 = integer(1)

        barf_1 = tag("barf", 1)
        shape_1 = CompoundShape(barf_1, [InStorageShape()])
        c_1 = W_Constructor(shape_1, [w_1])
        assert c_1.get_number_of_children() == 1
        assert c_1.get_child(0)  == w_1

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [shape_1, shape_1])
        c_1_1 = W_Constructor(shape_1, [w_1])
        c_2 = W_Constructor(shape_2, [w_1, w_1])
        assert c_2.get_number_of_children() == 2
        assert c_2.get_child(0)  == c_1
        assert c_2.get_child(0).get_child(0) == w_1
        assert c_2.get_child(1).get_child(0) == w_1


        foo_2 = tag("foo", 2)
        shape_3 = CompoundShape(foo_2, [shape_2, shape_2])
        c_1_3 = W_Constructor(shape_1, [w_1])
        c_1_4 = W_Constructor(shape_1, [w_1])
        c_2_1 = W_Constructor(shape_2, [c_1_3, c_1_4])
        # foo(zork(barf(1),barf(1)),zork(barf(1),barf(1)))
        c_3 = W_Constructor(shape_3, [w_1,w_1,w_1,w_1])
        assert c_3.get_number_of_children() == 2
        assert c_3.get_child(0)  == c_2
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
        c_1 = W_Constructor(shape_1, [w_1])
        assert c_1.get_number_of_children() == 1
        assert c_1.get_child(0)  == w_1

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [shape_1, shape_1])
        c_1_1 = W_Constructor(shape_1, [w_1])
        c_2 = W_Constructor(shape_2, [w_1, w_1])
        assert c_2.get_number_of_children() == 2
        assert c_2.get_child(0)  == c_1
        assert c_2.get_child(0).get_child(0) == w_1
        assert c_2.get_child(1).get_child(0) == w_1


        foo_2 = tag("foo", 2)
        # foo(zork(barf(1),barf(1)),zork(barf(1),barf(1)))
        shape_3 = CompoundShape(foo_2, [
                        CompoundShape(zork_2, [
                            shape_1,
                            InStorageShape()]),
                        InStorageShape()])
        c_1_3 = W_Constructor(shape_1, [w_1])
        c_1_4 = W_Constructor(shape_1, [w_1])
        c_2_1 = W_Constructor(CompoundShape(zork_2, [InStorageShape(), InStorageShape()]), [c_1_3, c_1_4])

        # DIFFERENCE TO other test: not everything is flattened
        c_3 = W_Constructor(shape_3, [
            # zork
            w_1,c_1_1,
            # zork
            c_2_1])
        assert c_3.get_number_of_children() == 2
        assert c_3.get_child(0)  == c_2
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
        b = [4, 5]
        c = []
        d = [6]
        x = _splice(a, 1, b)
        assert x == [1, 4 ,5, 3]

        y = _splice(a, 1, c)
        assert y == [1, 3]

        z = _splice(a, 1, d)
        assert z == [1, 6, 3]

        u = _splice(a, 0, d)
        assert u == [6, 2, 3]

        v = _splice(a, 0, b)
        assert v == [4, 5, 2, 3]

        w = _splice(a, 2, b)
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
        c_1 = W_Constructor(shape_1, [w_1])

        zork_2 = tag("zork", 2)
        shape_2 = CompoundShape(zork_2, [InStorageShape(), InStorageShape()])
        c_1_1 = W_Constructor(shape_1, [w_1])
        c_2 = W_Constructor(shape_2, [c_1, c_1_1])

        foo_2 = tag("foo", 2)
        shape_3 = CompoundShape(foo_2, [shape_2, shape_2])
        c_1_3 = W_Constructor(shape_1, [w_1])
        c_1_4 = W_Constructor(shape_1, [w_1])
        c_2_1 = W_Constructor(shape_2, [c_1_3, c_1_4])

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
        c_1 = W_Constructor(shape_1, [w_1])
        c_1_1 = W_Constructor(shape_1, [w_1])

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
        c_1 = W_Constructor(shape_1, [w_1])
        c_1_1 = W_Constructor(shape_1, [w_1])

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

        c_2 = W_Constructor(new_shape, new_storage)

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
        w_nil_ = W_Constructor(nil_shape, [])

        list_default_shape = CompoundShape(cons_, [InStorageShape(), InStorageShape()])

        list_1_shape = CompoundShape(cons_, [InStorageShape(), nil_shape])
        list_2_shape = CompoundShape(cons_, [InStorageShape(), list_1_shape])

        list_default_shape.known_transformations[(1,nil_shape)] = list_1_shape
        list_default_shape.known_transformations[(1,list_1_shape)] = list_2_shape

        w_list_0 = w_nil_

        (shape, storage) = list_default_shape.fusion([w_1, w_nil_])

        w_list_1 = W_Constructor(shape, storage)

        list_1_shape.known_transformations[(1, list_1_shape)] = list_2_shape

        (shape, storage) = list_default_shape.fusion([w_1, w_list_1])

        w_list_2 = W_Constructor(shape, storage)

        assert w_list_2._storage == [w_1, w_1]

