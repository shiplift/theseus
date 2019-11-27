#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
import py

from theseus.execution import *
from theseus.model import *
from theseus.expression import *
from theseus.pattern import *
from mu.peano import *
from theseus.util.construction_helper import (pattern, cons, integer,
                                           expression, ziprules,
                                           lamb,mu,
                                           nil,
                                           conslist, plist)
#
# Tests
#
class TestTag(object):

    def test_newtag(self):
        w_res = W_Tag("name", 0)
        assert isinstance(w_res, W_Tag)
        assert w_res.name == "name"
        assert w_res.arity() == 0

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
        w_int = w_integer(1)
        assert isinstance(w_int, W_Integer)
        assert w_int.value() == 1


class TestString(object):

    def test_futile(self):
        w_str = w_string("foo")
        assert isinstance(w_str, W_String)
        assert w_str.value() == "foo"

class TestFloat(object):

    def test_futile(self):
        w_flt = w_float(1.0)
        assert isinstance(w_flt, W_Float)
        assert w_flt.value() == 1.0

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
