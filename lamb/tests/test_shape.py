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

class TestConstructorShapes(object):

    def test_simple_predefined_shape(self):

        w_1 = integer(1)
        
        shape = ConstructorShape([])
        c = cons("barf")
        c._shape = shape
        assert c.get_number_of_children() == 0

        shape = ConstructorShape([InStorageShape()])
        c = cons("barf", w_1)
        c._shape = shape
        assert c.get_number_of_children() == 1
        assert c.get_child(0)  == w_1

        shape = ConstructorShape([InStorageShape()] * 2)
        c = cons("barf", w_1, w_1)
        c._shape = shape
        assert c.get_number_of_children() == 2
        assert c.get_child(0)  == w_1
        assert c.get_child(1)  == w_1

    def test_recursive_predefined_shape(self):

        w_1 = integer(1)

        shape_1 = ConstructorShape([InStorageShape()])
        c_1 = cons("barf", w_1)
        c_1._shape = shape_1
        assert c_1.get_number_of_children() == 1
        assert c_1.get_child(0)  == w_1

        shape_2 = ConstructorShape([shape_1, shape_1])
        c_2 = cons("zork", c_1, c_1)
        c_2._shape = shape_2
        assert c_2.get_number_of_children() == 2
        assert c_2.get_child(0)  == c_1
        assert c_2.get_child(0).get_child(0) == w_1
        assert c_2.get_child(1).get_child(0) == w_1

