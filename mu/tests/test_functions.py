#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
import sys
import py

from mu.functions import *
from mu.peano import *
from lamb.util.construction_helper import (cons, integer, w_nil,
                                           conslist, plist,
                                           execution_stack, operand_stack)

class TestParsing(object):
    def test_parse_int(self):
        assert parse("i", "10") == integer(10)

    def test_parse_peano(self):
        assert parse("p", "10") == peano_num(10)

    def test_parse_fun(self):
        assert parse("f", "succ") == all_functions["succ"].lamb

    def test_parse_list_simple(self):
        assert parse_list("i:1") == conslist([integer(1)])
        assert parse_list("i:1,i:1") == conslist([integer(1), integer(1)])

        assert parse_list("p:10") == conslist([peano_num(10)])
        assert parse_list("p:10,p:20") == conslist([peano_num(10),
                                                    peano_num(20)])

    def test_parse_list_len(self):
        assert parse_list("1;i:1") == conslist([integer(1)])
        assert parse_list("2;i:1,i:1") == conslist([integer(1), integer(1)])

        assert parse_list("1;p:10") == conslist([peano_num(10)])
        assert parse_list("2;p:10,p:20") == conslist([peano_num(10),
                                                    peano_num(20)])

        l = [peano_num(10), peano_num(10), peano_num(10)]
        assert parse_list("3;p:10") == conslist(l)

        l = [peano_num(2), peano_num(10), peano_num(10)]
        assert parse_list("3;p:2,p:10") == conslist(l)

    def test_parse_list_fun_fun(self):

        l = [peano_num(10), peano_num(11), peano_num(12)]
        assert parse_list("3;p:10,f:succ") == conslist(l)

        l = [peano_num(2), peano_num(10), peano_num(11)]
        assert parse_list("3;p:2,p:10,f:succ") == conslist(l)

    def test_parse_list_fun_prim(self):

        l = [integer(10), integer(11), integer(12)]
        assert parse_list("3;i:10,f:+") == conslist(l)

        l = [integer(2), integer(10), integer(11)]
        assert parse_list("3;i:2,i:10,f:+") == conslist(l)

    def test_parse_list(self):
        l = [integer(2), integer(10), integer(11)]
        assert parse("l", "3;i:2,i:10,f:+") == conslist(l)

class TestFormatting(object):

    def test_format_int(self):
        assert format(integer(42)) == "42"

    def test_format_peano_num(self):
        assert format(peano_num(42)) == "42"

    def test_format_fun(self):
        assert format(all_functions["succ"].lamb) == "succ"

    def test_format_list_simple(self):
        l = conslist([integer(42)])
        assert format_list(l) == ["42"]
        assert format(l) == "(42)"

        l = conslist([peano_num(42)])
        assert format_list(l) == ["42"]
        assert format(l) == "(42)"

        l = conslist([integer(42), integer(43)])
        assert format_list(l) == ["42", "43"]
        assert format(l) == "(42,43)"

        l = conslist([peano_num(42), peano_num(43)])
        assert format_list(l) == ["42", "43"]
        assert format(l) == "(42,43)"

    def test_format_list_nest(self):
        l = conslist([integer(42), conslist([integer(42)])])
        assert format_list(l) == ["42", "(42)"]
        assert format(l) == "(42,(42))"

        l = conslist([peano_num(42), conslist([peano_num(42)])])
        assert format_list(l) == ["42", "(42)"]
        assert format(l) == "(42,(42))"

class TestFunctions(object):

    def test_simple_append_processing(self):
        fun = all_functions["append"]
        ops = [fun.parse_arg(i, a) for i, a in enumerate(["1;i:1", "1;i:1"])]
        assert ops == [conslist([integer(1)]), conslist([integer(1)])]

        ret = run(fun.lamb, ops)
        assert plist(ret) == [integer(1), integer(1)]
        assert fun.format_ret(ret) == "(1,1)"