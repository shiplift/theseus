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

    def test_bound_variable_in_pattern(self, parser):
        with py.test.raises(ParseError) as e:
            t = parser.parse("""
            foo ≔ 1
            λ. 1. foo ↦ 1
            """)
        assert e.value.source_pos == SourcePos(42, 2, 19)
        assert e.value.errorinformation == 'Value bound to foo in pattern'

    def test_lambda_solo(self, parser):
        t = parser.parse("""λ. ↦ 1""")
        # lambdas cannot compare equal meaningfully
        assert t[0]._rules == [
            expression.Rule(patterns=[], expression=model.w_integer(1))]

        t = parser.parse("""λ. x ↦ x""")
        # lambdas cannot compare equal meaningfully
        x = Variable("x")
        assert t[0]._rules == [
            expression.Rule(
                patterns=[p(x)],
                expression=e(x))]
        assert t[0]._rules[0]._patterns[0].variable is \
               t[0]._rules[0]._expression.variable
    
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

    def test_corecursion_string(self, parser):
        t = parser.parse("""
        g ≔ Λ.
        f ≔ λ.
            1. 0 ↦ 1
            2. X ↦ μ(g, X)
        g ≔ λ.
            1. X ↦ μ(f, μ(⟪-⟫, X, 1))
        μ(f, 10)""")

    def test_corecursion_file(self, parser, tmpdir):
        f = tmpdir.join('corec.lamb')
        f.write_text(u"""
        g ≔ Λ.
        f ≔ λ.
            1. 0 ↦ 1
            2. X ↦ μ(g, X)
        g ≔ λ.
            1. X ↦ μ(f, μ(⟪-⟫, X, 1))
        μ(f, 10)""",encoding='utf-8')
        t = parser.parse(str(f), is_file=True)

    # def test_continuation_passing_simple(self, parser):
    #     py.test.skip("not implemented")
    #     # lamb.parser.print_tokens = True
    #     short = """
    #     f ≔ λ. a, b ↦ 1 ⇒
    #            c    ↦ X(a, b, c)
    #     """
    #     exploded = """
    #     f» ≔ λ. a, b, c ↦ X(a, b, c)
    #     f  ≔ λ. a, b    ↦ μ(f», a, b, 1)
    #     """
    #     #e = parser.parse(exploded)
    #     s = parser.parse(short)


    # def test_continuation_passing(self, parser):
    #     py.test.skip("not implemented")
    #     # lamb.parser.print_tokens = True
    #     short = """
    #     time ≔ λ. fun, arg ↦ μ(⟪clock⟫) ⇒
    #               start    ↦ μ(fun, arg) ⇒
    #               res      ↦ μ(⟪clock⟫) ⇒
    #               stop     ↦ μ(⟪minus_float⟫, stop, start) ⇒
    #               diff     ↦ μ(⟪print_result_string⟫, diff) ⇒
    #               _        ↦ res
    #     """
    #     exploded = """
    #     time$cont4 ≔ λ. fun, arg, start, res, stop, diff, _ ↦ res
    #     time$cont3 ≔ λ. fun, arg, start, res, stop, diff    ↦ μ(time$cont4, fun, arg, start, res, stop, diff, μ(⟪print_result_string⟫, diff))
    #     time$cont2 ≔ λ. fun, arg, start, res, stop          ↦ μ(time$cont3, fun, arg, start, res, stop, μ(⟪minus_float⟫, stop, start))
    #     time$cont1 ≔ λ. fun, arg, start, res                ↦ μ(time$cont2, fun, arg, start, res, μ(⟪clock⟫))
    #     time$cont0 ≔ λ. fun, arg, start                     ↦ μ(time$cont1, fun, arg, start, μ(fun, arg))
    #     time       ≔ λ. fun, arg                            ↦ μ(time$cont0, fun, arg, μ(⟪clock⟫))
    #     """
    #     # e = parser.parse(exploded)
    #     s = parser.parse(short)
        
    # def test_continuation_passing_rules(self, parser):
    #     py.test.skip("not implemented")
    #     short = """
    #     """
    #     exploded = """
    #     """

# EOF
