#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
import sys
import py

import mu.lists
import mu.peano
import mu.functions
from mu.peano import python_num, peano_num
from mu.functions import *
from theseus.util.construction_helper import (cons, integer,
                                           conslist, plist)
                                           

def setup_module(module):
    from theseus.startup import boot
    boot()


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
        args = ["1;i:1", "1;i:1"]
        ops = [fun.parse_arg(i, a) for i, a in enumerate(args)]
        assert ops == [conslist([integer(1)]), conslist([integer(1)])]

        ret = run(fun.lamb, ops)
        assert plist(ret) == [integer(1), integer(1)]
        assert fun.format_ret(ret) == "(1,1)"

    def test_mapping(self):
        fun = all_functions["map"]
        args = ["succ", "5;p:1,f:succ"]
        l = 5
        ops = [fun.parse_arg(i, a) for i, a in enumerate(args)]
        assert ops[0] == all_functions["succ"].lamb
        assert ops[1] == conslist([peano_num(i + 1) for i in range(l)])

        ret = run(fun.lamb, ops)
        assert plist(ret) == [peano_num(i + 2) for i in range(l)]

    def test_mapping_cliissue(self):
        from theseus.shape import CompoundShape
        from theseus.tests.test_shape import SConf
        with SConf(substitution_threshold=1):
            fun = all_functions["map"]
            args = ["succ", "10;p:1,f:succ"]
            l = 10
            ops = [fun.parse_arg(i, a) for i, a in enumerate(args)]
            assert ops[0] == all_functions["succ"].lamb
            assert ops[1] == conslist([peano_num(i + 1) for i in range(l)])

            ret = run(fun.lamb, ops)
            assert plist(ret) == [peano_num(i + 2) for i in range(l)]
# EOF
