#!/usr/bin/env python
# -*- coding: utf-8 -*-


from lamb.parser import Parser, ParseError
from lamb.util.construction_helper import *
from lamb.util.construction_helper import expression as e, pattern as p
from lamb import model, expression, pattern

from rpython.rlib.parsing.parsing import PackratParser, ParseError as PyParseError
from rpython.rlib.parsing.lexer import SourcePos, Lexer, Token
from rpython.rlib.parsing.tree import Nonterminal, Symbol, Node

import py

# For our joy
import lamb.util.debug
import lamb.parser
lamb.parser.use_dynamic_parser = True

def pytest_funcarg__parser(request):
    import copy
    """
    Returns a Lamb parser
    """
    def build_parser():
        return Parser()

    parser = request.cached_setup(
            setup=build_parser,
            scope="session",
    )

    #return copy.deepcopy(parser)
    return parser


class TestParser(object):

    def test_primary(self, parser):
        t = parser.parse("")
        assert t == []

        t = parser.parse("1")
        assert t == [model.w_integer(1)]

        t = parser.parse("‘’")
        assert t == [model.w_string("")]
        t = parser.parse("“”")
        assert t == [model.w_string("")]

        t = parser.parse("‘1’")
        assert t == [model.w_string("1")]
        t = parser.parse("“1”")
        assert t == [model.w_string("1")]

    def test_primitive(self, parser):
        from lamb.primitive import lookup, UnsupportedPrimitive
        t = parser.parse("⟪-⟫")
        assert t == [lookup("-")]

        with py.test.raises(PyParseError) as e:
            t = parser.parse("⟪⟫")
        assert e.value.source_pos == SourcePos(len("⟪"), 0, len("⟪"))
        assert e.value.errorinformation.failure_reasons == ["NAME"]

        with py.test.raises(UnsupportedPrimitive) as e:
            t = parser.parse("⟪____fooobar___unknown____⟫")

    def test_variable(self, parser):
        with py.test.raises(ParseError) as e:
            t = parser.parse("foo")
        assert e.value.source_pos == SourcePos(0, 0, 0)
        assert e.value.errorinformation == 'Unbound variable foo'

        t = parser.parse("""
        foo ≔ 1
        foo
        """)
        assert t == [model.W_Object(), model.w_integer(1)]

    def test_lambda_patternless(self, parser):
        t = parser.parse("""λ. 1. ↦ 1""")
        # lambdas cannot compare equal meaningfully
        assert t[0]._rules == [
            expression.Rule(patterns=[], expression=model.w_integer(1))]

        # should work, but meaningless
        t = parser.parse("""λ.
        1. ↦ 1
        2. ↦ 2
        """)
        assert t[0]._rules == [
            expression.Rule(patterns=[], expression=model.w_integer(1)),
            expression.Rule(patterns=[], expression=model.w_integer(2))]

    def test_lambda_simple_pattern(self, parser):
        t = parser.parse("""λ. 1. 1 ↦ 5""")
        # lambdas cannot compare equal meaningfully
        assert t[0]._rules == [
            expression.Rule(
                patterns=[p(model.w_integer(1))],
                expression=e(model.w_integer(5)))]

        # should work, but meaningless
        t = parser.parse("""λ.
        1. 1 ↦ 4
        2. 2 ↦ 12345
        """)
        assert t[0]._rules == [
            expression.Rule(
                patterns=[p(model.w_integer(1))],
                expression=e(model.w_integer(4))),
            expression.Rule(
                patterns=[p(model.w_integer(2))],
                expression=e(model.w_integer(12345)))]

        t = parser.parse("""λ. 1. x ↦ x""")
        # lambdas cannot compare equal meaningfully
        x = Variable("x")
        assert t[0]._rules == [
            expression.Rule(
                patterns=[p(x)],
                expression=e(x))]
        assert t[0]._rules[0]._patterns[0].variable is \
               t[0]._rules[0]._expression.variable

        # should work, but meaningless
        t = parser.parse("""λ.
        1. x ↦ x
        2. x ↦ 4
        """)
        x1 = Variable("x")
        x2 = Variable("x")
        assert t[0]._rules == [
            expression.Rule(
                patterns=[p(x1)],
                expression=e(x1)),
            expression.Rule(
                patterns=[p(x2)],
                expression=e(model.w_integer(4)))]
        assert t[0]._rules[0]._patterns[0].variable.name == \
               t[0]._rules[1]._patterns[0].variable.name
        assert t[0]._rules[0]._patterns[0].variable is not \
               t[0]._rules[1]._patterns[0].variable

# EOF
