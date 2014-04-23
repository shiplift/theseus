#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
    Parser for lamb.
"""
from __future__ import absolute_import

from rpython.rlib.parsing.deterministic import DFA
from rpython.rlib.parsing.lexer import Lexer, DummyLexer
from rpython.rlib.parsing.parsing import (Rule, PackratParser,
                                          ParseError as PyParseError)
from rpython.rlib.parsing.tree import RPythonVisitor, Symbol, Nonterminal, Node
from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.streamio import open_file_as_stream
from rpython.rlib.debug import debug_start, debug_stop, debug_print

from lamb import model, pattern, expression, primitive

import py
import sys
import os

sys.setrecursionlimit(10000)
set = py.builtin.set

print_tokens = False

use_dynamic_parser = False
#
# Helper for source access
#

class Source(object):
    def __init__(self, string, filename="<None>"):
        self.filename = filename
        self.fullsource = string

    def contents(self):
        return self.fullsource
#
# Error
#

class ParseError(Exception):
    def __init__(self, source_pos, errorinformation=None):
        self.source_pos = source_pos
        self.errorinformation = errorinformation
        self.args = (source_pos, errorinformation)

    def nice_error_message(self, filename="<unknown>", source=""):
        result = ["  File %s, line %s" % (filename, self.source_pos.lineno)]
        if source:
            result.append(source.split("\n")[self.source_pos.lineno])
            result.append(" " * self.source_pos.columnno + "^")
        else:
            result.append("<couldn't get source>")
        if self.errorinformation:
            result.append("ParseError: %s" % self.errorinformation)
        else:
            result.append("ParseError")
        return "\n".join(result)

#
# Parser helper contexts
#
class Scope(object):
    def __init__(self, parser):
        self.parser = parser
        self.bindings = {}
    def __enter__(self):
        self.parser.bindings_stack.append(self.bindings)
    def __exit__(self, type, value, traceback):
        self.parser.bindings_stack.pop()

class RulePatterns(object):
    def __init__(self, parser):
        self.parser = parser
    def __enter__(self):
        self.parser.rule_pattern_tracker += 1
    def __exit__(self, type, value, traceback):
        self.parser.rule_pattern_tracker -= 1

class RuleEffects(object):
    def __init__(self, parser):
        self.parser = parser
    def __enter__(self):
        self.parser.rule_effect_tracker += 1
    def __exit__(self, type, value, traceback):
        self.parser.rule_effect_tracker -= 1

# A small token
no_result = model.W_Object()

# #
# Parser/Transformator to Lamb
#

class Parser(RPythonVisitor):
    """Lamb Parser"""
    def __init__(self):
        RPythonVisitor.__init__(self)
        self.parser, self.lexer, self.transformer = make_lamb_parser()
        self._reset()

    def _reset(self):
        self.bindings_stack = [{}]
        self.lamb_stack = []
        self.rule_effect_tracker = 0
        self.rule_pattern_tracker = 0

    def parse(self, source, is_file=False):
        self._reset
        self.is_file = is_file
        if self.is_file:
            try:
                f = open_file_as_stream(source, buffering=0)
            except OSError as e:
                os.write(2, "Error [%s] %s\n" % (source, os.strerror(e.errno)))
                return
            try:
                self.source = Source(f.readall(), source)
            finally:
                f.close()
        else:
            self.source = Source(source)
        return self._parse()

    def _parse(self):
        try:
            tokens = self.lexer.tokenize(self.source.contents(),
                                         eof=True)
            if not we_are_translated() and print_tokens:
                from pprint import pprint
                pprint(tokens)
            parsed = self.parser.parse(tokens)
            pre_ast = self.transformer().transform(parsed)
            actual_ast = self.dispatch(pre_ast)
        except ParseError, e:
            print e.nice_error_message(filename=self.source.filename,
                                       source=self.source.contents())
            raise
        except PyParseError, e:
            print e.nice_error_message(filename=self.source.filename,
                                       source=self.source.contents())
            raise
        if not we_are_translated():
            try:
                if py.test.config.option.view:
                    actual_ast.view()
            except AttributeError:
                pass
        return actual_ast

    def toplevel_bindings(self):
        return self.bindings_stack[0]

    # helper

    def handle_all(self, nodes):
        """ Dispatches on all nodes in list """
        processed_nodes = [self.dispatch(child)[0] for child in nodes]
        return processed_nodes

    def lookup(self, key):
        for scope in reversed(self.bindings_stack):
            val = scope.get(key, None)
            if val is not None:
                return val
        raise KeyError(key)

    def define(self, key, value):
        innermost_scope = self.bindings_stack[-1]
        innermost_scope[key] = value

    def to_pattern(self, w_object):
        if isinstance(w_object, model.W_Integer):
            ret = pattern.IntegerPattern(w_object.value())
        elif isinstance(w_object, model.W_String):
            ret = pattern.StringPattern(w_object.value())
        elif isinstance(w_object, model.W_Constructor):
            ret = self.pattern_from_constructor(w_object)
        else:
            ret = w_object
        return ret

    def pattern_from_constructor(self, w_constructor):
        _tag = w_constructor.get_tag()
        _children = [self.to_pattern(w_constructor.get_child(i)) \
                    for i in range(w_constructor.get_number_of_children())]
        return pattern.ConstructorPattern(_tag, _children)


    def make_string(self, node, strip=True):
        string = node.additional_info
        if strip:
            start = len("“")
            stop = len(string) - len("”")
            assert stop > 0
            s = model.w_string(string[start:stop])
        else:
            s = model.w_string(string)
        return s

    def make_lambda(self, node, name=""):
        l = model.W_Lambda(rules=[], name=name)
        with Scope(self):
            if name != "":
                self.define(name, l)
            rules = self.handle_all(node.children)
            assert isinstance(rules, list)
            # lets show the annotator that these all are indeed rules
            l._rules = [None] * len(rules)
            for i, r in enumerate(rules):
                assert isinstance(r, expression.Rule)
                l._rules[i] = r
            return l

    def get_name(self, node):
        assert len(node.children) >= 1
        w_name = (self.dispatch(node.children[0]))[0]
        assert isinstance(w_name, model.W_String)
        name = w_name.value()
        return name

    def pos(self, node):
        try:
            return node.getsourcepos()
        except IndexError, e:
            return None

    # detokenization
    def visit_NAME(self, node):
        return [self.make_string(node, strip=False)]

    def visit_QSTRING(self, node):
        return [self.make_string(node)]
    def visit_QQSTRING(self, node):
        return [self.make_string(node)]

    def visit_INTEGER(self, node):
        return [model.W_Integer(int(node.additional_info))]

    # def visit_FLOAT(self, node):
    #     f = model.W_Float(float(node.additional_info))
    #     return f


    # productions

    def visit_definition(self, node):
        assert len(node.children) == 2
        name = self.get_name(node)
        if node.children[1].symbol == "lambda":
            definee = self.make_lambda(node.children[1], name)
        else:
            definee = self.dispatch(node.children[1])[0]
        self.define(name, definee)
        return [no_result]

    def visit_lambda(self, node):
        return [self.make_lambda(node)]

    def visit_rule(self, node):
        if len(node.children) == 1:
            patterns_ = None
            effect_   = node.children[0]
        else:
            patterns_ = node.children[0]
            effect_   = node.children[1]

        with Scope(self):
            with RulePatterns(self):
                patterns = self.dispatch(patterns_) if patterns_ else []
            with RuleEffects(self):
                effect = self.dispatch(effect_)[0]

        return [expression.Rule(patterns, effect)]

    # def visit_patterns(self, node):
    #     return self.handle_all(node.children)

    def visit_primary_pattern(self, node):
        assert len(node.children) == 1
        primary = self.dispatch(node.children[0])[0]
        if isinstance(primary, model.W_Integer):
            return [pattern.IntegerPattern(primary.value())]
        elif isinstance(primary, model.W_String):
            return [pattern.StringPattern(primary.value())]
        else:
            reason = "Unknown pattern %s " % primary
            raise ParseError(node.getsourcepos(), reason)

    def visit_variable_pattern(self, node):
        name = self.get_name(node)

        if name.startswith("_"):
            return [pattern.VariablePattern(expression.Variable(name))]

        try:
            w_found = self.lookup(name)
            found = self.to_pattern(w_found)
            if isinstance(found, expression.Variable):
                reason = "Variable already defined: %s " % name
                raise ParseError(node.getsourcepos(), reason)
            else:
                reason = "Unknown value bound to %s" % name
                raise ParseError(node.getsourcepos(), reason)
            ret = found
        except KeyError:
            var = expression.Variable(name)
            self.define(name, var)
            ret = pattern.VariablePattern(var)
        return [ret]

    def visit_constructor_pattern(self, node):
        name = self.get_name(node)
        if len(node.children) == 1:
            ret = pattern.ConstructorPattern(model.tag(name, 0), [])
        else:
            ch = self.dispatch(node.children[1])
            tag = model.tag(name, len(ch))
            ret = pattern.ConstructorPattern(tag, ch)
        return [ret]

    # def visit_constructor_pattern_args(self, node):
    #     children = self.handle_all(node.children)
    #     return children

    def visit_constructor(self, node):
        assert len(node.children) == 2
        name = self.get_name(node)
        ch = self.dispatch(node.children[1])
        return [model.w_constructor(model.tag(name, len(ch)), ch)]

    # def visit_constructor_args(self, node):
    #     return self.handle_all(node.children)

    def visit_variable(self, node):
        name = self.get_name(node)
        try:
            var = self.lookup(name)
        except KeyError:
            reason = "Unbound variable %s" % name
            raise ParseError(node.getsourcepos(), reason)
        else:
            if isinstance(var, expression.Variable) and \
               self.rule_effect_tracker > 0:
                return [expression.W_VariableExpression(var)]
            else:
                return [var]


    def visit_application(self, node):
        num = len(node.children)
        args = self.dispatch(node.children[1]) if num > 1 else []
        callee = self.dispatch(node.children[0])[0]
        return [expression.w_call(callee, args)]

    # def visit_application_args(self, node):
    #     return self.handle_all(node.children)

    def visit_primitive(self, node):
        name = self.get_name(node)
        return [primitive.lookup(name)]

    # top level production
    def visit_lamb_source(self, node):
        return self.handle_all(node.children)

    # general visiting
    # catching all unimplemented with same behavior
    def general_nonterminal_visit(self, node):
        return self.handle_all(node.children)

    # def general_symbol_visit(self, node):
    #     """NOT_RPYTHON"""
    #     print "g_s_v:\t", type(node), node
    #     assert False, node.additional_info
    #     return self.make_string(node, strip=False)

    # def general_visit(self, node):
    #     """NOT_RPYTHON"""
    #     assert False, node.symbol
    #     return node


def parse_file(filename):
     p = Parser()
     elements = p.parse(filename, is_file=True)
     result = [element for element in elements if element is not no_result]
     bindings = p.toplevel_bindings()
     return (result, bindings)

############################################################################

# generated code between this line and its other occurence
class LambToAST(object):
    def visit_lamb_source(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            expr = self.visit___lamb_source_rest_0_0(node.children[0])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__star_symbol0(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit___lamb_source_rest_0_0(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol1(self, node):
        #auto-generated code, don't edit
        children = []
        expr = self.visit_toplevel_expressions(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__star_symbol0(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__plus_symbol0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__plus_symbol0(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol2(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit__plus_symbol0(node.children[0])
            assert len(expr) == 1
            children.extend(expr[0].children)
            expr = self.visit_toplevel_expressions(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__plus_symbol0(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit_toplevel_expressions(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit__star_symbol2(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol3(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__star_symbol3(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_toplevel_expressions(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            children.extend(self.visit_toplevel_expression(node.children[0]))
            expr = self.visit___toplevel_expressions_rest_0_0(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_toplevel_expression(node.children[0]))
        expr = self.visit__star_symbol2(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit___toplevel_expressions_rest_0_0(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_toplevel_expression(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if node.children[0].symbol == 'definition':
            return self.visit_definition(node.children[0])
        return self.visit_expression(node.children[0])
    def visit_expression(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if node.children[0].symbol == 'application':
            return self.visit_application(node.children[0])
        if node.children[0].symbol == 'constructor':
            return self.visit_constructor(node.children[0])
        if node.children[0].symbol == 'lambda':
            return self.visit_lambda(node.children[0])
        if node.children[0].symbol == 'primary':
            return self.visit_primary(node.children[0])
        if node.children[0].symbol == 'primitive':
            return self.visit_primitive(node.children[0])
        return self.visit_variable(node.children[0])
    def visit_primary(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if node.children[0].symbol == 'INTEGER':
            return [node.children[0]]
        if node.children[0].symbol == 'QQSTRING':
            return [node.children[0]]
        return [node.children[0]]
    def visit_variable(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend([node.children[0]])
        return [Nonterminal(node.symbol, children)]
    def visit_definition(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if node.children[2].symbol == 'expression':
            children = []
            children.extend([node.children[0]])
            children.extend(self.visit_expression(node.children[2]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend([node.children[0]])
        children.extend(self.visit_lambda(node.children[2]))
        return [Nonterminal(node.symbol, children)]
    def visit_constructor(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend([node.children[0]])
        children.extend(self.visit_constructor_args(node.children[1]))
        return [Nonterminal(node.symbol, children)]
    def visit_constructor_args(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit_arglist(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol4(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol5(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit____star_symbol5_rest_0_0(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol4(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit____star_symbol5_rest_0_0(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_arglist(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_expression(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_expression(node.children[0]))
        expr = self.visit__star_symbol5(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_application(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 4:
            children = []
            children.extend(self.visit_expression(node.children[2]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_expression(node.children[2]))
        children.extend(self.visit_application_args(node.children[3]))
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol6(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit__plus_symbol1(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            children.extend(self.visit_expression(node.children[1]))
            return [Nonterminal(node.symbol, children)]
        if length == 3:
            if node.children[1].symbol == '_maybe_symbol6':
                children = []
                expr = self.visit__maybe_symbol6(node.children[1])
                assert len(expr) == 1
                children.extend(expr[0].children)
                children.extend(self.visit_expression(node.children[2]))
                return [Nonterminal(node.symbol, children)]
            children = []
            children.extend(self.visit_expression(node.children[1]))
            expr = self.visit__plus_symbol1(node.children[2])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol6(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        children.extend(self.visit_expression(node.children[2]))
        expr = self.visit__plus_symbol1(node.children[3])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_application_args(self, node):
        #auto-generated code, don't edit
        children = []
        expr = self.visit__plus_symbol1(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol7(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit_lambda(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit_rules(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol7(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit_rules(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__plus_symbol2(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__plus_symbol2(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol8(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit__plus_symbol2(node.children[0])
            assert len(expr) == 1
            children.extend(expr[0].children)
            children.extend(self.visit_rule(node.children[1]))
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__plus_symbol2(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        children.extend(self.visit_rule(node.children[1]))
        expr = self.visit__star_symbol8(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_rules(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_rule(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_rule(node.children[0]))
        expr = self.visit__star_symbol8(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol9(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend(self.visit_patterns(node.children[0]))
        return [Nonterminal(node.symbol, children)]
    def visit_rule(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 4:
            children = []
            children.extend(self.visit_expression(node.children[3]))
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol9(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        children.extend(self.visit_expression(node.children[4]))
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol10(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol11(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit____star_symbol11_rest_0_0(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol10(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit____star_symbol11_rest_0_0(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_patterns(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_pattern(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_pattern(node.children[0]))
        expr = self.visit__star_symbol11(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_pattern(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if node.children[0].symbol == 'constructor_pattern':
            return self.visit_constructor_pattern(node.children[0])
        if node.children[0].symbol == 'primary_pattern':
            return self.visit_primary_pattern(node.children[0])
        return self.visit_variable_pattern(node.children[0])
    def visit_variable_pattern(self, node):
        #auto-generated code, don't edit
        children = []
        expr = self.visit_variable(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_primary_pattern(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend(self.visit_primary(node.children[0]))
        return [Nonterminal(node.symbol, children)]
    def visit_constructor_pattern(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend([node.children[0]])
        children.extend(self.visit_constructor_pattern_args(node.children[1]))
        return [Nonterminal(node.symbol, children)]
    def visit_constructor_pattern_args(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit_pattern_arglist(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol12(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol13(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit____star_symbol13_rest_0_0(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol12(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit____star_symbol13_rest_0_0(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_pattern_arglist(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_pattern(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_pattern(node.children[0]))
        expr = self.visit__star_symbol13(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_primitive(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend([node.children[1]])
        return [Nonterminal(node.symbol, children)]
    def visit___lamb_source_rest_0_0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol1(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit___toplevel_expressions_rest_0_0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 0:
            children = []
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__star_symbol3(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit____star_symbol5_rest_0_0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_expression(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_expression(node.children[0]))
        expr = self.visit__star_symbol5(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit____star_symbol11_rest_0_0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_pattern(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_pattern(node.children[0]))
        expr = self.visit__star_symbol11(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit____star_symbol13_rest_0_0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_pattern(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_pattern(node.children[0]))
        expr = self.visit__star_symbol13(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def transform(self, tree):
        #auto-generated code, don't edit
        assert isinstance(tree, Nonterminal)
        assert tree.symbol == 'lamb_source'
        r = self.visit_lamb_source(tree)
        assert len(r) == 1
        if not we_are_translated():
            try:
                if py.test.config.option.view:
                    r[0].view()
            except AttributeError:
                pass
        return r[0]
parser = PackratParser([Rule('lamb_source', [['_star_symbol0', '__lamb_source_rest_0_0'], ['__lamb_source_rest_0_0']]),
  Rule('_maybe_symbol1', [['toplevel_expressions']]),
  Rule('_star_symbol0', [['NEWLINE', '_star_symbol0'], ['NEWLINE']]),
  Rule('_plus_symbol0', [['NEWLINE', '_plus_symbol0'], ['NEWLINE']]),
  Rule('_star_symbol2', [['_plus_symbol0', 'toplevel_expressions', '_star_symbol2'], ['_plus_symbol0', 'toplevel_expressions']]),
  Rule('_star_symbol3', [['NEWLINE', '_star_symbol3'], ['NEWLINE']]),
  Rule('toplevel_expressions', [['toplevel_expression', '_star_symbol2', '__toplevel_expressions_rest_0_0'], ['toplevel_expression', '__toplevel_expressions_rest_0_0']]),
  Rule('toplevel_expression', [['definition'], ['expression']]),
  Rule('expression', [['constructor'], ['application'], ['lambda'], ['variable'], ['primitive'], ['primary']]),
  Rule('primary', [['INTEGER'], ['QSTRING'], ['QQSTRING']]),
  Rule('variable', [['NAME']]),
  Rule('definition', [['NAME', 'DEFINEDAS', 'lambda'], ['NAME', 'DEFINEDAS', 'expression']]),
  Rule('constructor', [['NAME', 'constructor_args']]),
  Rule('constructor_args', [['LEFT_PARENTHESIS', 'arglist', 'RIGHT_PARENTHESIS'], ['LEFT_PARENTHESIS', 'RIGHT_PARENTHESIS']]),
  Rule('_maybe_symbol4', [['NEWLINE']]),
  Rule('_star_symbol5', [['__0_,', '_maybe_symbol4', '___star_symbol5_rest_0_0'], ['__0_,', '___star_symbol5_rest_0_0']]),
  Rule('arglist', [['expression', '_star_symbol5'], ['expression']]),
  Rule('application', [['MU', 'LEFT_PARENTHESIS', 'expression', 'application_args', 'RIGHT_PARENTHESIS'], ['MU', 'LEFT_PARENTHESIS', 'expression', 'RIGHT_PARENTHESIS']]),
  Rule('_maybe_symbol6', [['NEWLINE']]),
  Rule('_plus_symbol1', [['__0_,', '_maybe_symbol6', 'expression', '_plus_symbol1'], ['__0_,', 'expression', '_plus_symbol1'], ['__0_,', '_maybe_symbol6', 'expression'], ['__0_,', 'expression']]),
  Rule('application_args', [['_plus_symbol1']]),
  Rule('_maybe_symbol7', [['NEWLINE']]),
  Rule('lambda', [['LAMBDA', '_maybe_symbol7', 'rules'], ['LAMBDA', 'rules']]),
  Rule('_plus_symbol2', [['NEWLINE', '_plus_symbol2'], ['NEWLINE']]),
  Rule('_star_symbol8', [['_plus_symbol2', 'rule', '_star_symbol8'], ['_plus_symbol2', 'rule']]),
  Rule('rules', [['rule', '_star_symbol8'], ['rule']]),
  Rule('_maybe_symbol9', [['patterns']]),
  Rule('rule', [['INTEGER', '__1_.', '_maybe_symbol9', 'MAPSTO', 'expression'], ['INTEGER', '__1_.', 'MAPSTO', 'expression']]),
  Rule('_maybe_symbol10', [['NEWLINE']]),
  Rule('_star_symbol11', [['__0_,', '_maybe_symbol10', '___star_symbol11_rest_0_0'], ['__0_,', '___star_symbol11_rest_0_0']]),
  Rule('patterns', [['pattern', '_star_symbol11'], ['pattern']]),
  Rule('pattern', [['constructor_pattern'], ['variable_pattern'], ['primary_pattern']]),
  Rule('variable_pattern', [['variable']]),
  Rule('primary_pattern', [['primary']]),
  Rule('constructor_pattern', [['NAME', 'constructor_pattern_args']]),
  Rule('constructor_pattern_args', [['LEFT_PARENTHESIS', 'pattern_arglist', 'RIGHT_PARENTHESIS'], ['LEFT_PARENTHESIS', 'RIGHT_PARENTHESIS']]),
  Rule('_maybe_symbol12', [['NEWLINE']]),
  Rule('_star_symbol13', [['__0_,', '_maybe_symbol12', '___star_symbol13_rest_0_0'], ['__0_,', '___star_symbol13_rest_0_0']]),
  Rule('pattern_arglist', [['pattern', '_star_symbol13'], ['pattern']]),
  Rule('primitive', [['LEFT_DOUBLE_ANGLE', 'NAME', 'RIGHT_DOUBLE_ANGLE']]),
  Rule('__lamb_source_rest_0_0', [['_maybe_symbol1', 'EOF'], ['EOF']]),
  Rule('__toplevel_expressions_rest_0_0', [['_star_symbol3'], []]),
  Rule('___star_symbol5_rest_0_0', [['expression', '_star_symbol5'], ['expression']]),
  Rule('___star_symbol11_rest_0_0', [['pattern', '_star_symbol11'], ['pattern']]),
  Rule('___star_symbol13_rest_0_0', [['pattern', '_star_symbol13'], ['pattern']])],
 'lamb_source')
def recognize(runner, i):
    #auto-generated code, don't edit
    assert i >= 0
    input = runner.text
    state = 0
    while 1:
        if state == 0:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 0
                return i
            if ':' <= char <= '\x9e':
                state = 1
            elif '\xac' <= char <= '\xcd':
                state = 1
            elif '\xe3' <= char <= '\xff':
                state = 1
            elif '\xcf' <= char <= '\xe1':
                state = 1
            elif '\x0e' <= char <= '\x1f':
                state = 1
            elif '\xa0' <= char <= '\xa9':
                state = 1
            elif '\x00' <= char <= '\x08':
                state = 1
            elif '$' <= char <= "'":
                state = 1
            elif char == '!':
                state = 1
            elif char == '"':
                state = 1
            elif char == '*':
                state = 1
            elif char == '+':
                state = 1
            elif char == '\x0b':
                state = 1
            elif char == '-':
                state = 1
            elif char == '/':
                state = 1
            elif char == '\t':
                state = 2
            elif char == '\x0c':
                state = 2
            elif char == ' ':
                state = 2
            elif char == '(':
                state = 3
            elif char == ',':
                state = 4
            elif '0' <= char <= '9':
                state = 5
            elif char == '#':
                state = 6
            elif char == '\n':
                state = 7
            elif char == '\r':
                state = 7
            elif char == '.':
                state = 8
            elif char == ')':
                state = 9
            elif char == '\xce':
                state = 10
            elif char == '\xe2':
                state = 11
            else:
                break
        if state == 1:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 1
                return i
            if '-' <= char <= '\x9e':
                state = 1
                continue
            elif '\xac' <= char <= '\xe1':
                state = 1
                continue
            elif '\xe3' <= char <= '\xff':
                state = 1
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 1
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 1
                continue
            elif '\x00' <= char <= '\x08':
                state = 1
                continue
            elif '$' <= char <= "'":
                state = 1
                continue
            elif char == '!':
                state = 1
                continue
            elif char == '"':
                state = 1
                continue
            elif char == '*':
                state = 1
                continue
            elif char == '+':
                state = 1
                continue
            elif char == '\x0b':
                state = 1
                continue
            else:
                break
        if state == 2:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 2
                return i
            if char == '\t':
                state = 2
                continue
            elif char == '\x0c':
                state = 2
                continue
            elif char == ' ':
                state = 2
                continue
            else:
                break
        if state == 5:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 5
                return i
            if '0' <= char <= '9':
                state = 5
                continue
            else:
                break
        if state == 6:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 6
                return i
            if '\x0b' <= char <= '\xff':
                state = 6
                continue
            elif '\x00' <= char <= '\t':
                state = 6
                continue
            else:
                break
        if state == 8:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 8
                return i
            if '-' <= char <= '\x9e':
                state = 1
                continue
            elif '\xac' <= char <= '\xe1':
                state = 1
                continue
            elif '\xe3' <= char <= '\xff':
                state = 1
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 1
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 1
                continue
            elif '\x00' <= char <= '\x08':
                state = 1
                continue
            elif '$' <= char <= "'":
                state = 1
                continue
            elif char == '!':
                state = 1
                continue
            elif char == '"':
                state = 1
                continue
            elif char == '*':
                state = 1
                continue
            elif char == '+':
                state = 1
                continue
            elif char == '\x0b':
                state = 1
                continue
            else:
                break
        if state == 10:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 10
                return i
            if '-' <= char <= '\x9e':
                state = 1
                continue
            elif '\xbd' <= char <= '\xe1':
                state = 1
                continue
            elif '\xe3' <= char <= '\xff':
                state = 1
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 1
                continue
            elif '\xac' <= char <= '\xba':
                state = 1
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 1
                continue
            elif '\x00' <= char <= '\x08':
                state = 1
                continue
            elif '$' <= char <= "'":
                state = 1
                continue
            elif char == '!':
                state = 1
                continue
            elif char == '"':
                state = 1
                continue
            elif char == '*':
                state = 1
                continue
            elif char == '+':
                state = 1
                continue
            elif char == '\x0b':
                state = 1
                continue
            elif char == '\xbb':
                state = 28
            elif char == '\xbc':
                state = 29
            else:
                break
        if state == 11:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 11
                return ~i
            if char == '\x89':
                state = 12
            elif char == '\x80':
                state = 13
            elif char == '\x9f':
                state = 14
            elif char == '\x86':
                state = 15
            else:
                break
        if state == 12:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 12
                return ~i
            if char == '\x94':
                state = 27
            else:
                break
        if state == 13:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 13
                return ~i
            if char == '\x98':
                state = 19
            elif char == '\x9c':
                state = 20
            else:
                break
        if state == 14:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 14
                return ~i
            if char == '\xab':
                state = 17
            elif char == '\xaa':
                state = 18
            else:
                break
        if state == 15:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 15
                return ~i
            if char == '\xa6':
                state = 16
            else:
                break
        if state == 19:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 19
                return ~i
            if char == '\xe2':
                state = 24
            elif '\x00' <= char <= '\x7f':
                state = 19
                continue
            elif '\x9a' <= char <= '\xe1':
                state = 19
                continue
            elif '\xe3' <= char <= '\xff':
                state = 19
                continue
            elif '\x81' <= char <= '\x98':
                state = 19
                continue
            else:
                break
        if state == 20:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 20
                return ~i
            if '\x00' <= char <= '\x7f':
                state = 20
                continue
            elif '\x9e' <= char <= '\xe1':
                state = 20
                continue
            elif '\xe3' <= char <= '\xff':
                state = 20
                continue
            elif '\x81' <= char <= '\x9c':
                state = 20
                continue
            elif char == '\xe2':
                state = 21
            else:
                break
        if state == 21:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 21
                return ~i
            if char == '\x80':
                state = 22
            else:
                break
        if state == 22:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 22
                return ~i
            if char == '\x9d':
                state = 23
            else:
                break
        if state == 24:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 24
                return ~i
            if char == '\x80':
                state = 25
            else:
                break
        if state == 25:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 25
                return ~i
            if char == '\x99':
                state = 26
            else:
                break
        if state == 28:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 28
                return i
            if '-' <= char <= '\x9e':
                state = 30
            elif '\xac' <= char <= '\xe1':
                state = 30
            elif '\xe3' <= char <= '\xff':
                state = 30
            elif '\x0e' <= char <= '\x1f':
                state = 30
            elif '\xa0' <= char <= '\xa9':
                state = 30
            elif '\x00' <= char <= '\x08':
                state = 30
            elif '$' <= char <= "'":
                state = 30
            elif char == '!':
                state = 30
            elif char == '"':
                state = 30
            elif char == '*':
                state = 30
            elif char == '+':
                state = 30
            elif char == '\x0b':
                state = 30
            elif char == '\t':
                state = 31
            elif char == '\n':
                state = 31
            elif char == '\x0c':
                state = 31
            elif char == '\r':
                state = 31
            elif char == '(':
                state = 31
            elif char == ')':
                state = 31
            elif char == '\xaa':
                state = 31
            elif char == '\xab':
                state = 31
            elif char == ' ':
                state = 31
            elif char == '#':
                state = 31
            elif char == ',':
                state = 31
            elif char == '\x9f':
                state = 31
            elif char == '\xe2':
                state = 31
            else:
                break
        if state == 29:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 29
                return i
            if '-' <= char <= '\x9e':
                state = 1
                continue
            elif '\xac' <= char <= '\xe1':
                state = 1
                continue
            elif '\xe3' <= char <= '\xff':
                state = 1
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 1
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 1
                continue
            elif '\x00' <= char <= '\x08':
                state = 1
                continue
            elif '$' <= char <= "'":
                state = 1
                continue
            elif char == '!':
                state = 1
                continue
            elif char == '"':
                state = 1
                continue
            elif char == '*':
                state = 1
                continue
            elif char == '+':
                state = 1
                continue
            elif char == '\x0b':
                state = 1
                continue
            else:
                break
        if state == 30:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 30
                return i
            if '-' <= char <= '\x9e':
                state = 1
                continue
            elif '\xac' <= char <= '\xe1':
                state = 1
                continue
            elif '\xe3' <= char <= '\xff':
                state = 1
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 1
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 1
                continue
            elif '\x00' <= char <= '\x08':
                state = 1
                continue
            elif '$' <= char <= "'":
                state = 1
                continue
            elif char == '!':
                state = 1
                continue
            elif char == '"':
                state = 1
                continue
            elif char == '*':
                state = 1
                continue
            elif char == '+':
                state = 1
                continue
            elif char == '\x0b':
                state = 1
                continue
            else:
                break
        runner.last_matched_state = state
        runner.last_matched_index = i - 1
        runner.state = state
        if i == len(input):
            return i
        else:
            return ~i
        break
    runner.state = state
    return ~i
lexer = DummyLexer(recognize, DFA(32,
 {(0, '\x00'): 1,
  (0, '\x01'): 1,
  (0, '\x02'): 1,
  (0, '\x03'): 1,
  (0, '\x04'): 1,
  (0, '\x05'): 1,
  (0, '\x06'): 1,
  (0, '\x07'): 1,
  (0, '\x08'): 1,
  (0, '\t'): 2,
  (0, '\n'): 7,
  (0, '\x0b'): 1,
  (0, '\x0c'): 2,
  (0, '\r'): 7,
  (0, '\x0e'): 1,
  (0, '\x0f'): 1,
  (0, '\x10'): 1,
  (0, '\x11'): 1,
  (0, '\x12'): 1,
  (0, '\x13'): 1,
  (0, '\x14'): 1,
  (0, '\x15'): 1,
  (0, '\x16'): 1,
  (0, '\x17'): 1,
  (0, '\x18'): 1,
  (0, '\x19'): 1,
  (0, '\x1a'): 1,
  (0, '\x1b'): 1,
  (0, '\x1c'): 1,
  (0, '\x1d'): 1,
  (0, '\x1e'): 1,
  (0, '\x1f'): 1,
  (0, ' '): 2,
  (0, '!'): 1,
  (0, '"'): 1,
  (0, '#'): 6,
  (0, '$'): 1,
  (0, '%'): 1,
  (0, '&'): 1,
  (0, "'"): 1,
  (0, '('): 3,
  (0, ')'): 9,
  (0, '*'): 1,
  (0, '+'): 1,
  (0, ','): 4,
  (0, '-'): 1,
  (0, '.'): 8,
  (0, '/'): 1,
  (0, '0'): 5,
  (0, '1'): 5,
  (0, '2'): 5,
  (0, '3'): 5,
  (0, '4'): 5,
  (0, '5'): 5,
  (0, '6'): 5,
  (0, '7'): 5,
  (0, '8'): 5,
  (0, '9'): 5,
  (0, ':'): 1,
  (0, ';'): 1,
  (0, '<'): 1,
  (0, '='): 1,
  (0, '>'): 1,
  (0, '?'): 1,
  (0, '@'): 1,
  (0, 'A'): 1,
  (0, 'B'): 1,
  (0, 'C'): 1,
  (0, 'D'): 1,
  (0, 'E'): 1,
  (0, 'F'): 1,
  (0, 'G'): 1,
  (0, 'H'): 1,
  (0, 'I'): 1,
  (0, 'J'): 1,
  (0, 'K'): 1,
  (0, 'L'): 1,
  (0, 'M'): 1,
  (0, 'N'): 1,
  (0, 'O'): 1,
  (0, 'P'): 1,
  (0, 'Q'): 1,
  (0, 'R'): 1,
  (0, 'S'): 1,
  (0, 'T'): 1,
  (0, 'U'): 1,
  (0, 'V'): 1,
  (0, 'W'): 1,
  (0, 'X'): 1,
  (0, 'Y'): 1,
  (0, 'Z'): 1,
  (0, '['): 1,
  (0, '\\'): 1,
  (0, ']'): 1,
  (0, '^'): 1,
  (0, '_'): 1,
  (0, '`'): 1,
  (0, 'a'): 1,
  (0, 'b'): 1,
  (0, 'c'): 1,
  (0, 'd'): 1,
  (0, 'e'): 1,
  (0, 'f'): 1,
  (0, 'g'): 1,
  (0, 'h'): 1,
  (0, 'i'): 1,
  (0, 'j'): 1,
  (0, 'k'): 1,
  (0, 'l'): 1,
  (0, 'm'): 1,
  (0, 'n'): 1,
  (0, 'o'): 1,
  (0, 'p'): 1,
  (0, 'q'): 1,
  (0, 'r'): 1,
  (0, 's'): 1,
  (0, 't'): 1,
  (0, 'u'): 1,
  (0, 'v'): 1,
  (0, 'w'): 1,
  (0, 'x'): 1,
  (0, 'y'): 1,
  (0, 'z'): 1,
  (0, '{'): 1,
  (0, '|'): 1,
  (0, '}'): 1,
  (0, '~'): 1,
  (0, '\x7f'): 1,
  (0, '\x80'): 1,
  (0, '\x81'): 1,
  (0, '\x82'): 1,
  (0, '\x83'): 1,
  (0, '\x84'): 1,
  (0, '\x85'): 1,
  (0, '\x86'): 1,
  (0, '\x87'): 1,
  (0, '\x88'): 1,
  (0, '\x89'): 1,
  (0, '\x8a'): 1,
  (0, '\x8b'): 1,
  (0, '\x8c'): 1,
  (0, '\x8d'): 1,
  (0, '\x8e'): 1,
  (0, '\x8f'): 1,
  (0, '\x90'): 1,
  (0, '\x91'): 1,
  (0, '\x92'): 1,
  (0, '\x93'): 1,
  (0, '\x94'): 1,
  (0, '\x95'): 1,
  (0, '\x96'): 1,
  (0, '\x97'): 1,
  (0, '\x98'): 1,
  (0, '\x99'): 1,
  (0, '\x9a'): 1,
  (0, '\x9b'): 1,
  (0, '\x9c'): 1,
  (0, '\x9d'): 1,
  (0, '\x9e'): 1,
  (0, '\xa0'): 1,
  (0, '\xa1'): 1,
  (0, '\xa2'): 1,
  (0, '\xa3'): 1,
  (0, '\xa4'): 1,
  (0, '\xa5'): 1,
  (0, '\xa6'): 1,
  (0, '\xa7'): 1,
  (0, '\xa8'): 1,
  (0, '\xa9'): 1,
  (0, '\xac'): 1,
  (0, '\xad'): 1,
  (0, '\xae'): 1,
  (0, '\xaf'): 1,
  (0, '\xb0'): 1,
  (0, '\xb1'): 1,
  (0, '\xb2'): 1,
  (0, '\xb3'): 1,
  (0, '\xb4'): 1,
  (0, '\xb5'): 1,
  (0, '\xb6'): 1,
  (0, '\xb7'): 1,
  (0, '\xb8'): 1,
  (0, '\xb9'): 1,
  (0, '\xba'): 1,
  (0, '\xbb'): 1,
  (0, '\xbc'): 1,
  (0, '\xbd'): 1,
  (0, '\xbe'): 1,
  (0, '\xbf'): 1,
  (0, '\xc0'): 1,
  (0, '\xc1'): 1,
  (0, '\xc2'): 1,
  (0, '\xc3'): 1,
  (0, '\xc4'): 1,
  (0, '\xc5'): 1,
  (0, '\xc6'): 1,
  (0, '\xc7'): 1,
  (0, '\xc8'): 1,
  (0, '\xc9'): 1,
  (0, '\xca'): 1,
  (0, '\xcb'): 1,
  (0, '\xcc'): 1,
  (0, '\xcd'): 1,
  (0, '\xce'): 10,
  (0, '\xcf'): 1,
  (0, '\xd0'): 1,
  (0, '\xd1'): 1,
  (0, '\xd2'): 1,
  (0, '\xd3'): 1,
  (0, '\xd4'): 1,
  (0, '\xd5'): 1,
  (0, '\xd6'): 1,
  (0, '\xd7'): 1,
  (0, '\xd8'): 1,
  (0, '\xd9'): 1,
  (0, '\xda'): 1,
  (0, '\xdb'): 1,
  (0, '\xdc'): 1,
  (0, '\xdd'): 1,
  (0, '\xde'): 1,
  (0, '\xdf'): 1,
  (0, '\xe0'): 1,
  (0, '\xe1'): 1,
  (0, '\xe2'): 11,
  (0, '\xe3'): 1,
  (0, '\xe4'): 1,
  (0, '\xe5'): 1,
  (0, '\xe6'): 1,
  (0, '\xe7'): 1,
  (0, '\xe8'): 1,
  (0, '\xe9'): 1,
  (0, '\xea'): 1,
  (0, '\xeb'): 1,
  (0, '\xec'): 1,
  (0, '\xed'): 1,
  (0, '\xee'): 1,
  (0, '\xef'): 1,
  (0, '\xf0'): 1,
  (0, '\xf1'): 1,
  (0, '\xf2'): 1,
  (0, '\xf3'): 1,
  (0, '\xf4'): 1,
  (0, '\xf5'): 1,
  (0, '\xf6'): 1,
  (0, '\xf7'): 1,
  (0, '\xf8'): 1,
  (0, '\xf9'): 1,
  (0, '\xfa'): 1,
  (0, '\xfb'): 1,
  (0, '\xfc'): 1,
  (0, '\xfd'): 1,
  (0, '\xfe'): 1,
  (0, '\xff'): 1,
  (1, '\x00'): 1,
  (1, '\x01'): 1,
  (1, '\x02'): 1,
  (1, '\x03'): 1,
  (1, '\x04'): 1,
  (1, '\x05'): 1,
  (1, '\x06'): 1,
  (1, '\x07'): 1,
  (1, '\x08'): 1,
  (1, '\x0b'): 1,
  (1, '\x0e'): 1,
  (1, '\x0f'): 1,
  (1, '\x10'): 1,
  (1, '\x11'): 1,
  (1, '\x12'): 1,
  (1, '\x13'): 1,
  (1, '\x14'): 1,
  (1, '\x15'): 1,
  (1, '\x16'): 1,
  (1, '\x17'): 1,
  (1, '\x18'): 1,
  (1, '\x19'): 1,
  (1, '\x1a'): 1,
  (1, '\x1b'): 1,
  (1, '\x1c'): 1,
  (1, '\x1d'): 1,
  (1, '\x1e'): 1,
  (1, '\x1f'): 1,
  (1, '!'): 1,
  (1, '"'): 1,
  (1, '$'): 1,
  (1, '%'): 1,
  (1, '&'): 1,
  (1, "'"): 1,
  (1, '*'): 1,
  (1, '+'): 1,
  (1, '-'): 1,
  (1, '.'): 1,
  (1, '/'): 1,
  (1, '0'): 1,
  (1, '1'): 1,
  (1, '2'): 1,
  (1, '3'): 1,
  (1, '4'): 1,
  (1, '5'): 1,
  (1, '6'): 1,
  (1, '7'): 1,
  (1, '8'): 1,
  (1, '9'): 1,
  (1, ':'): 1,
  (1, ';'): 1,
  (1, '<'): 1,
  (1, '='): 1,
  (1, '>'): 1,
  (1, '?'): 1,
  (1, '@'): 1,
  (1, 'A'): 1,
  (1, 'B'): 1,
  (1, 'C'): 1,
  (1, 'D'): 1,
  (1, 'E'): 1,
  (1, 'F'): 1,
  (1, 'G'): 1,
  (1, 'H'): 1,
  (1, 'I'): 1,
  (1, 'J'): 1,
  (1, 'K'): 1,
  (1, 'L'): 1,
  (1, 'M'): 1,
  (1, 'N'): 1,
  (1, 'O'): 1,
  (1, 'P'): 1,
  (1, 'Q'): 1,
  (1, 'R'): 1,
  (1, 'S'): 1,
  (1, 'T'): 1,
  (1, 'U'): 1,
  (1, 'V'): 1,
  (1, 'W'): 1,
  (1, 'X'): 1,
  (1, 'Y'): 1,
  (1, 'Z'): 1,
  (1, '['): 1,
  (1, '\\'): 1,
  (1, ']'): 1,
  (1, '^'): 1,
  (1, '_'): 1,
  (1, '`'): 1,
  (1, 'a'): 1,
  (1, 'b'): 1,
  (1, 'c'): 1,
  (1, 'd'): 1,
  (1, 'e'): 1,
  (1, 'f'): 1,
  (1, 'g'): 1,
  (1, 'h'): 1,
  (1, 'i'): 1,
  (1, 'j'): 1,
  (1, 'k'): 1,
  (1, 'l'): 1,
  (1, 'm'): 1,
  (1, 'n'): 1,
  (1, 'o'): 1,
  (1, 'p'): 1,
  (1, 'q'): 1,
  (1, 'r'): 1,
  (1, 's'): 1,
  (1, 't'): 1,
  (1, 'u'): 1,
  (1, 'v'): 1,
  (1, 'w'): 1,
  (1, 'x'): 1,
  (1, 'y'): 1,
  (1, 'z'): 1,
  (1, '{'): 1,
  (1, '|'): 1,
  (1, '}'): 1,
  (1, '~'): 1,
  (1, '\x7f'): 1,
  (1, '\x80'): 1,
  (1, '\x81'): 1,
  (1, '\x82'): 1,
  (1, '\x83'): 1,
  (1, '\x84'): 1,
  (1, '\x85'): 1,
  (1, '\x86'): 1,
  (1, '\x87'): 1,
  (1, '\x88'): 1,
  (1, '\x89'): 1,
  (1, '\x8a'): 1,
  (1, '\x8b'): 1,
  (1, '\x8c'): 1,
  (1, '\x8d'): 1,
  (1, '\x8e'): 1,
  (1, '\x8f'): 1,
  (1, '\x90'): 1,
  (1, '\x91'): 1,
  (1, '\x92'): 1,
  (1, '\x93'): 1,
  (1, '\x94'): 1,
  (1, '\x95'): 1,
  (1, '\x96'): 1,
  (1, '\x97'): 1,
  (1, '\x98'): 1,
  (1, '\x99'): 1,
  (1, '\x9a'): 1,
  (1, '\x9b'): 1,
  (1, '\x9c'): 1,
  (1, '\x9d'): 1,
  (1, '\x9e'): 1,
  (1, '\xa0'): 1,
  (1, '\xa1'): 1,
  (1, '\xa2'): 1,
  (1, '\xa3'): 1,
  (1, '\xa4'): 1,
  (1, '\xa5'): 1,
  (1, '\xa6'): 1,
  (1, '\xa7'): 1,
  (1, '\xa8'): 1,
  (1, '\xa9'): 1,
  (1, '\xac'): 1,
  (1, '\xad'): 1,
  (1, '\xae'): 1,
  (1, '\xaf'): 1,
  (1, '\xb0'): 1,
  (1, '\xb1'): 1,
  (1, '\xb2'): 1,
  (1, '\xb3'): 1,
  (1, '\xb4'): 1,
  (1, '\xb5'): 1,
  (1, '\xb6'): 1,
  (1, '\xb7'): 1,
  (1, '\xb8'): 1,
  (1, '\xb9'): 1,
  (1, '\xba'): 1,
  (1, '\xbb'): 1,
  (1, '\xbc'): 1,
  (1, '\xbd'): 1,
  (1, '\xbe'): 1,
  (1, '\xbf'): 1,
  (1, '\xc0'): 1,
  (1, '\xc1'): 1,
  (1, '\xc2'): 1,
  (1, '\xc3'): 1,
  (1, '\xc4'): 1,
  (1, '\xc5'): 1,
  (1, '\xc6'): 1,
  (1, '\xc7'): 1,
  (1, '\xc8'): 1,
  (1, '\xc9'): 1,
  (1, '\xca'): 1,
  (1, '\xcb'): 1,
  (1, '\xcc'): 1,
  (1, '\xcd'): 1,
  (1, '\xce'): 1,
  (1, '\xcf'): 1,
  (1, '\xd0'): 1,
  (1, '\xd1'): 1,
  (1, '\xd2'): 1,
  (1, '\xd3'): 1,
  (1, '\xd4'): 1,
  (1, '\xd5'): 1,
  (1, '\xd6'): 1,
  (1, '\xd7'): 1,
  (1, '\xd8'): 1,
  (1, '\xd9'): 1,
  (1, '\xda'): 1,
  (1, '\xdb'): 1,
  (1, '\xdc'): 1,
  (1, '\xdd'): 1,
  (1, '\xde'): 1,
  (1, '\xdf'): 1,
  (1, '\xe0'): 1,
  (1, '\xe1'): 1,
  (1, '\xe3'): 1,
  (1, '\xe4'): 1,
  (1, '\xe5'): 1,
  (1, '\xe6'): 1,
  (1, '\xe7'): 1,
  (1, '\xe8'): 1,
  (1, '\xe9'): 1,
  (1, '\xea'): 1,
  (1, '\xeb'): 1,
  (1, '\xec'): 1,
  (1, '\xed'): 1,
  (1, '\xee'): 1,
  (1, '\xef'): 1,
  (1, '\xf0'): 1,
  (1, '\xf1'): 1,
  (1, '\xf2'): 1,
  (1, '\xf3'): 1,
  (1, '\xf4'): 1,
  (1, '\xf5'): 1,
  (1, '\xf6'): 1,
  (1, '\xf7'): 1,
  (1, '\xf8'): 1,
  (1, '\xf9'): 1,
  (1, '\xfa'): 1,
  (1, '\xfb'): 1,
  (1, '\xfc'): 1,
  (1, '\xfd'): 1,
  (1, '\xfe'): 1,
  (1, '\xff'): 1,
  (2, '\t'): 2,
  (2, '\x0c'): 2,
  (2, ' '): 2,
  (5, '0'): 5,
  (5, '1'): 5,
  (5, '2'): 5,
  (5, '3'): 5,
  (5, '4'): 5,
  (5, '5'): 5,
  (5, '6'): 5,
  (5, '7'): 5,
  (5, '8'): 5,
  (5, '9'): 5,
  (6, '\x00'): 6,
  (6, '\x01'): 6,
  (6, '\x02'): 6,
  (6, '\x03'): 6,
  (6, '\x04'): 6,
  (6, '\x05'): 6,
  (6, '\x06'): 6,
  (6, '\x07'): 6,
  (6, '\x08'): 6,
  (6, '\t'): 6,
  (6, '\x0b'): 6,
  (6, '\x0c'): 6,
  (6, '\r'): 6,
  (6, '\x0e'): 6,
  (6, '\x0f'): 6,
  (6, '\x10'): 6,
  (6, '\x11'): 6,
  (6, '\x12'): 6,
  (6, '\x13'): 6,
  (6, '\x14'): 6,
  (6, '\x15'): 6,
  (6, '\x16'): 6,
  (6, '\x17'): 6,
  (6, '\x18'): 6,
  (6, '\x19'): 6,
  (6, '\x1a'): 6,
  (6, '\x1b'): 6,
  (6, '\x1c'): 6,
  (6, '\x1d'): 6,
  (6, '\x1e'): 6,
  (6, '\x1f'): 6,
  (6, ' '): 6,
  (6, '!'): 6,
  (6, '"'): 6,
  (6, '#'): 6,
  (6, '$'): 6,
  (6, '%'): 6,
  (6, '&'): 6,
  (6, "'"): 6,
  (6, '('): 6,
  (6, ')'): 6,
  (6, '*'): 6,
  (6, '+'): 6,
  (6, ','): 6,
  (6, '-'): 6,
  (6, '.'): 6,
  (6, '/'): 6,
  (6, '0'): 6,
  (6, '1'): 6,
  (6, '2'): 6,
  (6, '3'): 6,
  (6, '4'): 6,
  (6, '5'): 6,
  (6, '6'): 6,
  (6, '7'): 6,
  (6, '8'): 6,
  (6, '9'): 6,
  (6, ':'): 6,
  (6, ';'): 6,
  (6, '<'): 6,
  (6, '='): 6,
  (6, '>'): 6,
  (6, '?'): 6,
  (6, '@'): 6,
  (6, 'A'): 6,
  (6, 'B'): 6,
  (6, 'C'): 6,
  (6, 'D'): 6,
  (6, 'E'): 6,
  (6, 'F'): 6,
  (6, 'G'): 6,
  (6, 'H'): 6,
  (6, 'I'): 6,
  (6, 'J'): 6,
  (6, 'K'): 6,
  (6, 'L'): 6,
  (6, 'M'): 6,
  (6, 'N'): 6,
  (6, 'O'): 6,
  (6, 'P'): 6,
  (6, 'Q'): 6,
  (6, 'R'): 6,
  (6, 'S'): 6,
  (6, 'T'): 6,
  (6, 'U'): 6,
  (6, 'V'): 6,
  (6, 'W'): 6,
  (6, 'X'): 6,
  (6, 'Y'): 6,
  (6, 'Z'): 6,
  (6, '['): 6,
  (6, '\\'): 6,
  (6, ']'): 6,
  (6, '^'): 6,
  (6, '_'): 6,
  (6, '`'): 6,
  (6, 'a'): 6,
  (6, 'b'): 6,
  (6, 'c'): 6,
  (6, 'd'): 6,
  (6, 'e'): 6,
  (6, 'f'): 6,
  (6, 'g'): 6,
  (6, 'h'): 6,
  (6, 'i'): 6,
  (6, 'j'): 6,
  (6, 'k'): 6,
  (6, 'l'): 6,
  (6, 'm'): 6,
  (6, 'n'): 6,
  (6, 'o'): 6,
  (6, 'p'): 6,
  (6, 'q'): 6,
  (6, 'r'): 6,
  (6, 's'): 6,
  (6, 't'): 6,
  (6, 'u'): 6,
  (6, 'v'): 6,
  (6, 'w'): 6,
  (6, 'x'): 6,
  (6, 'y'): 6,
  (6, 'z'): 6,
  (6, '{'): 6,
  (6, '|'): 6,
  (6, '}'): 6,
  (6, '~'): 6,
  (6, '\x7f'): 6,
  (6, '\x80'): 6,
  (6, '\x81'): 6,
  (6, '\x82'): 6,
  (6, '\x83'): 6,
  (6, '\x84'): 6,
  (6, '\x85'): 6,
  (6, '\x86'): 6,
  (6, '\x87'): 6,
  (6, '\x88'): 6,
  (6, '\x89'): 6,
  (6, '\x8a'): 6,
  (6, '\x8b'): 6,
  (6, '\x8c'): 6,
  (6, '\x8d'): 6,
  (6, '\x8e'): 6,
  (6, '\x8f'): 6,
  (6, '\x90'): 6,
  (6, '\x91'): 6,
  (6, '\x92'): 6,
  (6, '\x93'): 6,
  (6, '\x94'): 6,
  (6, '\x95'): 6,
  (6, '\x96'): 6,
  (6, '\x97'): 6,
  (6, '\x98'): 6,
  (6, '\x99'): 6,
  (6, '\x9a'): 6,
  (6, '\x9b'): 6,
  (6, '\x9c'): 6,
  (6, '\x9d'): 6,
  (6, '\x9e'): 6,
  (6, '\x9f'): 6,
  (6, '\xa0'): 6,
  (6, '\xa1'): 6,
  (6, '\xa2'): 6,
  (6, '\xa3'): 6,
  (6, '\xa4'): 6,
  (6, '\xa5'): 6,
  (6, '\xa6'): 6,
  (6, '\xa7'): 6,
  (6, '\xa8'): 6,
  (6, '\xa9'): 6,
  (6, '\xaa'): 6,
  (6, '\xab'): 6,
  (6, '\xac'): 6,
  (6, '\xad'): 6,
  (6, '\xae'): 6,
  (6, '\xaf'): 6,
  (6, '\xb0'): 6,
  (6, '\xb1'): 6,
  (6, '\xb2'): 6,
  (6, '\xb3'): 6,
  (6, '\xb4'): 6,
  (6, '\xb5'): 6,
  (6, '\xb6'): 6,
  (6, '\xb7'): 6,
  (6, '\xb8'): 6,
  (6, '\xb9'): 6,
  (6, '\xba'): 6,
  (6, '\xbb'): 6,
  (6, '\xbc'): 6,
  (6, '\xbd'): 6,
  (6, '\xbe'): 6,
  (6, '\xbf'): 6,
  (6, '\xc0'): 6,
  (6, '\xc1'): 6,
  (6, '\xc2'): 6,
  (6, '\xc3'): 6,
  (6, '\xc4'): 6,
  (6, '\xc5'): 6,
  (6, '\xc6'): 6,
  (6, '\xc7'): 6,
  (6, '\xc8'): 6,
  (6, '\xc9'): 6,
  (6, '\xca'): 6,
  (6, '\xcb'): 6,
  (6, '\xcc'): 6,
  (6, '\xcd'): 6,
  (6, '\xce'): 6,
  (6, '\xcf'): 6,
  (6, '\xd0'): 6,
  (6, '\xd1'): 6,
  (6, '\xd2'): 6,
  (6, '\xd3'): 6,
  (6, '\xd4'): 6,
  (6, '\xd5'): 6,
  (6, '\xd6'): 6,
  (6, '\xd7'): 6,
  (6, '\xd8'): 6,
  (6, '\xd9'): 6,
  (6, '\xda'): 6,
  (6, '\xdb'): 6,
  (6, '\xdc'): 6,
  (6, '\xdd'): 6,
  (6, '\xde'): 6,
  (6, '\xdf'): 6,
  (6, '\xe0'): 6,
  (6, '\xe1'): 6,
  (6, '\xe2'): 6,
  (6, '\xe3'): 6,
  (6, '\xe4'): 6,
  (6, '\xe5'): 6,
  (6, '\xe6'): 6,
  (6, '\xe7'): 6,
  (6, '\xe8'): 6,
  (6, '\xe9'): 6,
  (6, '\xea'): 6,
  (6, '\xeb'): 6,
  (6, '\xec'): 6,
  (6, '\xed'): 6,
  (6, '\xee'): 6,
  (6, '\xef'): 6,
  (6, '\xf0'): 6,
  (6, '\xf1'): 6,
  (6, '\xf2'): 6,
  (6, '\xf3'): 6,
  (6, '\xf4'): 6,
  (6, '\xf5'): 6,
  (6, '\xf6'): 6,
  (6, '\xf7'): 6,
  (6, '\xf8'): 6,
  (6, '\xf9'): 6,
  (6, '\xfa'): 6,
  (6, '\xfb'): 6,
  (6, '\xfc'): 6,
  (6, '\xfd'): 6,
  (6, '\xfe'): 6,
  (6, '\xff'): 6,
  (8, '\x00'): 1,
  (8, '\x01'): 1,
  (8, '\x02'): 1,
  (8, '\x03'): 1,
  (8, '\x04'): 1,
  (8, '\x05'): 1,
  (8, '\x06'): 1,
  (8, '\x07'): 1,
  (8, '\x08'): 1,
  (8, '\x0b'): 1,
  (8, '\x0e'): 1,
  (8, '\x0f'): 1,
  (8, '\x10'): 1,
  (8, '\x11'): 1,
  (8, '\x12'): 1,
  (8, '\x13'): 1,
  (8, '\x14'): 1,
  (8, '\x15'): 1,
  (8, '\x16'): 1,
  (8, '\x17'): 1,
  (8, '\x18'): 1,
  (8, '\x19'): 1,
  (8, '\x1a'): 1,
  (8, '\x1b'): 1,
  (8, '\x1c'): 1,
  (8, '\x1d'): 1,
  (8, '\x1e'): 1,
  (8, '\x1f'): 1,
  (8, '!'): 1,
  (8, '"'): 1,
  (8, '$'): 1,
  (8, '%'): 1,
  (8, '&'): 1,
  (8, "'"): 1,
  (8, '*'): 1,
  (8, '+'): 1,
  (8, '-'): 1,
  (8, '.'): 1,
  (8, '/'): 1,
  (8, '0'): 1,
  (8, '1'): 1,
  (8, '2'): 1,
  (8, '3'): 1,
  (8, '4'): 1,
  (8, '5'): 1,
  (8, '6'): 1,
  (8, '7'): 1,
  (8, '8'): 1,
  (8, '9'): 1,
  (8, ':'): 1,
  (8, ';'): 1,
  (8, '<'): 1,
  (8, '='): 1,
  (8, '>'): 1,
  (8, '?'): 1,
  (8, '@'): 1,
  (8, 'A'): 1,
  (8, 'B'): 1,
  (8, 'C'): 1,
  (8, 'D'): 1,
  (8, 'E'): 1,
  (8, 'F'): 1,
  (8, 'G'): 1,
  (8, 'H'): 1,
  (8, 'I'): 1,
  (8, 'J'): 1,
  (8, 'K'): 1,
  (8, 'L'): 1,
  (8, 'M'): 1,
  (8, 'N'): 1,
  (8, 'O'): 1,
  (8, 'P'): 1,
  (8, 'Q'): 1,
  (8, 'R'): 1,
  (8, 'S'): 1,
  (8, 'T'): 1,
  (8, 'U'): 1,
  (8, 'V'): 1,
  (8, 'W'): 1,
  (8, 'X'): 1,
  (8, 'Y'): 1,
  (8, 'Z'): 1,
  (8, '['): 1,
  (8, '\\'): 1,
  (8, ']'): 1,
  (8, '^'): 1,
  (8, '_'): 1,
  (8, '`'): 1,
  (8, 'a'): 1,
  (8, 'b'): 1,
  (8, 'c'): 1,
  (8, 'd'): 1,
  (8, 'e'): 1,
  (8, 'f'): 1,
  (8, 'g'): 1,
  (8, 'h'): 1,
  (8, 'i'): 1,
  (8, 'j'): 1,
  (8, 'k'): 1,
  (8, 'l'): 1,
  (8, 'm'): 1,
  (8, 'n'): 1,
  (8, 'o'): 1,
  (8, 'p'): 1,
  (8, 'q'): 1,
  (8, 'r'): 1,
  (8, 's'): 1,
  (8, 't'): 1,
  (8, 'u'): 1,
  (8, 'v'): 1,
  (8, 'w'): 1,
  (8, 'x'): 1,
  (8, 'y'): 1,
  (8, 'z'): 1,
  (8, '{'): 1,
  (8, '|'): 1,
  (8, '}'): 1,
  (8, '~'): 1,
  (8, '\x7f'): 1,
  (8, '\x80'): 1,
  (8, '\x81'): 1,
  (8, '\x82'): 1,
  (8, '\x83'): 1,
  (8, '\x84'): 1,
  (8, '\x85'): 1,
  (8, '\x86'): 1,
  (8, '\x87'): 1,
  (8, '\x88'): 1,
  (8, '\x89'): 1,
  (8, '\x8a'): 1,
  (8, '\x8b'): 1,
  (8, '\x8c'): 1,
  (8, '\x8d'): 1,
  (8, '\x8e'): 1,
  (8, '\x8f'): 1,
  (8, '\x90'): 1,
  (8, '\x91'): 1,
  (8, '\x92'): 1,
  (8, '\x93'): 1,
  (8, '\x94'): 1,
  (8, '\x95'): 1,
  (8, '\x96'): 1,
  (8, '\x97'): 1,
  (8, '\x98'): 1,
  (8, '\x99'): 1,
  (8, '\x9a'): 1,
  (8, '\x9b'): 1,
  (8, '\x9c'): 1,
  (8, '\x9d'): 1,
  (8, '\x9e'): 1,
  (8, '\xa0'): 1,
  (8, '\xa1'): 1,
  (8, '\xa2'): 1,
  (8, '\xa3'): 1,
  (8, '\xa4'): 1,
  (8, '\xa5'): 1,
  (8, '\xa6'): 1,
  (8, '\xa7'): 1,
  (8, '\xa8'): 1,
  (8, '\xa9'): 1,
  (8, '\xac'): 1,
  (8, '\xad'): 1,
  (8, '\xae'): 1,
  (8, '\xaf'): 1,
  (8, '\xb0'): 1,
  (8, '\xb1'): 1,
  (8, '\xb2'): 1,
  (8, '\xb3'): 1,
  (8, '\xb4'): 1,
  (8, '\xb5'): 1,
  (8, '\xb6'): 1,
  (8, '\xb7'): 1,
  (8, '\xb8'): 1,
  (8, '\xb9'): 1,
  (8, '\xba'): 1,
  (8, '\xbb'): 1,
  (8, '\xbc'): 1,
  (8, '\xbd'): 1,
  (8, '\xbe'): 1,
  (8, '\xbf'): 1,
  (8, '\xc0'): 1,
  (8, '\xc1'): 1,
  (8, '\xc2'): 1,
  (8, '\xc3'): 1,
  (8, '\xc4'): 1,
  (8, '\xc5'): 1,
  (8, '\xc6'): 1,
  (8, '\xc7'): 1,
  (8, '\xc8'): 1,
  (8, '\xc9'): 1,
  (8, '\xca'): 1,
  (8, '\xcb'): 1,
  (8, '\xcc'): 1,
  (8, '\xcd'): 1,
  (8, '\xce'): 1,
  (8, '\xcf'): 1,
  (8, '\xd0'): 1,
  (8, '\xd1'): 1,
  (8, '\xd2'): 1,
  (8, '\xd3'): 1,
  (8, '\xd4'): 1,
  (8, '\xd5'): 1,
  (8, '\xd6'): 1,
  (8, '\xd7'): 1,
  (8, '\xd8'): 1,
  (8, '\xd9'): 1,
  (8, '\xda'): 1,
  (8, '\xdb'): 1,
  (8, '\xdc'): 1,
  (8, '\xdd'): 1,
  (8, '\xde'): 1,
  (8, '\xdf'): 1,
  (8, '\xe0'): 1,
  (8, '\xe1'): 1,
  (8, '\xe3'): 1,
  (8, '\xe4'): 1,
  (8, '\xe5'): 1,
  (8, '\xe6'): 1,
  (8, '\xe7'): 1,
  (8, '\xe8'): 1,
  (8, '\xe9'): 1,
  (8, '\xea'): 1,
  (8, '\xeb'): 1,
  (8, '\xec'): 1,
  (8, '\xed'): 1,
  (8, '\xee'): 1,
  (8, '\xef'): 1,
  (8, '\xf0'): 1,
  (8, '\xf1'): 1,
  (8, '\xf2'): 1,
  (8, '\xf3'): 1,
  (8, '\xf4'): 1,
  (8, '\xf5'): 1,
  (8, '\xf6'): 1,
  (8, '\xf7'): 1,
  (8, '\xf8'): 1,
  (8, '\xf9'): 1,
  (8, '\xfa'): 1,
  (8, '\xfb'): 1,
  (8, '\xfc'): 1,
  (8, '\xfd'): 1,
  (8, '\xfe'): 1,
  (8, '\xff'): 1,
  (10, '\x00'): 1,
  (10, '\x01'): 1,
  (10, '\x02'): 1,
  (10, '\x03'): 1,
  (10, '\x04'): 1,
  (10, '\x05'): 1,
  (10, '\x06'): 1,
  (10, '\x07'): 1,
  (10, '\x08'): 1,
  (10, '\x0b'): 1,
  (10, '\x0e'): 1,
  (10, '\x0f'): 1,
  (10, '\x10'): 1,
  (10, '\x11'): 1,
  (10, '\x12'): 1,
  (10, '\x13'): 1,
  (10, '\x14'): 1,
  (10, '\x15'): 1,
  (10, '\x16'): 1,
  (10, '\x17'): 1,
  (10, '\x18'): 1,
  (10, '\x19'): 1,
  (10, '\x1a'): 1,
  (10, '\x1b'): 1,
  (10, '\x1c'): 1,
  (10, '\x1d'): 1,
  (10, '\x1e'): 1,
  (10, '\x1f'): 1,
  (10, '!'): 1,
  (10, '"'): 1,
  (10, '$'): 1,
  (10, '%'): 1,
  (10, '&'): 1,
  (10, "'"): 1,
  (10, '*'): 1,
  (10, '+'): 1,
  (10, '-'): 1,
  (10, '.'): 1,
  (10, '/'): 1,
  (10, '0'): 1,
  (10, '1'): 1,
  (10, '2'): 1,
  (10, '3'): 1,
  (10, '4'): 1,
  (10, '5'): 1,
  (10, '6'): 1,
  (10, '7'): 1,
  (10, '8'): 1,
  (10, '9'): 1,
  (10, ':'): 1,
  (10, ';'): 1,
  (10, '<'): 1,
  (10, '='): 1,
  (10, '>'): 1,
  (10, '?'): 1,
  (10, '@'): 1,
  (10, 'A'): 1,
  (10, 'B'): 1,
  (10, 'C'): 1,
  (10, 'D'): 1,
  (10, 'E'): 1,
  (10, 'F'): 1,
  (10, 'G'): 1,
  (10, 'H'): 1,
  (10, 'I'): 1,
  (10, 'J'): 1,
  (10, 'K'): 1,
  (10, 'L'): 1,
  (10, 'M'): 1,
  (10, 'N'): 1,
  (10, 'O'): 1,
  (10, 'P'): 1,
  (10, 'Q'): 1,
  (10, 'R'): 1,
  (10, 'S'): 1,
  (10, 'T'): 1,
  (10, 'U'): 1,
  (10, 'V'): 1,
  (10, 'W'): 1,
  (10, 'X'): 1,
  (10, 'Y'): 1,
  (10, 'Z'): 1,
  (10, '['): 1,
  (10, '\\'): 1,
  (10, ']'): 1,
  (10, '^'): 1,
  (10, '_'): 1,
  (10, '`'): 1,
  (10, 'a'): 1,
  (10, 'b'): 1,
  (10, 'c'): 1,
  (10, 'd'): 1,
  (10, 'e'): 1,
  (10, 'f'): 1,
  (10, 'g'): 1,
  (10, 'h'): 1,
  (10, 'i'): 1,
  (10, 'j'): 1,
  (10, 'k'): 1,
  (10, 'l'): 1,
  (10, 'm'): 1,
  (10, 'n'): 1,
  (10, 'o'): 1,
  (10, 'p'): 1,
  (10, 'q'): 1,
  (10, 'r'): 1,
  (10, 's'): 1,
  (10, 't'): 1,
  (10, 'u'): 1,
  (10, 'v'): 1,
  (10, 'w'): 1,
  (10, 'x'): 1,
  (10, 'y'): 1,
  (10, 'z'): 1,
  (10, '{'): 1,
  (10, '|'): 1,
  (10, '}'): 1,
  (10, '~'): 1,
  (10, '\x7f'): 1,
  (10, '\x80'): 1,
  (10, '\x81'): 1,
  (10, '\x82'): 1,
  (10, '\x83'): 1,
  (10, '\x84'): 1,
  (10, '\x85'): 1,
  (10, '\x86'): 1,
  (10, '\x87'): 1,
  (10, '\x88'): 1,
  (10, '\x89'): 1,
  (10, '\x8a'): 1,
  (10, '\x8b'): 1,
  (10, '\x8c'): 1,
  (10, '\x8d'): 1,
  (10, '\x8e'): 1,
  (10, '\x8f'): 1,
  (10, '\x90'): 1,
  (10, '\x91'): 1,
  (10, '\x92'): 1,
  (10, '\x93'): 1,
  (10, '\x94'): 1,
  (10, '\x95'): 1,
  (10, '\x96'): 1,
  (10, '\x97'): 1,
  (10, '\x98'): 1,
  (10, '\x99'): 1,
  (10, '\x9a'): 1,
  (10, '\x9b'): 1,
  (10, '\x9c'): 1,
  (10, '\x9d'): 1,
  (10, '\x9e'): 1,
  (10, '\xa0'): 1,
  (10, '\xa1'): 1,
  (10, '\xa2'): 1,
  (10, '\xa3'): 1,
  (10, '\xa4'): 1,
  (10, '\xa5'): 1,
  (10, '\xa6'): 1,
  (10, '\xa7'): 1,
  (10, '\xa8'): 1,
  (10, '\xa9'): 1,
  (10, '\xac'): 1,
  (10, '\xad'): 1,
  (10, '\xae'): 1,
  (10, '\xaf'): 1,
  (10, '\xb0'): 1,
  (10, '\xb1'): 1,
  (10, '\xb2'): 1,
  (10, '\xb3'): 1,
  (10, '\xb4'): 1,
  (10, '\xb5'): 1,
  (10, '\xb6'): 1,
  (10, '\xb7'): 1,
  (10, '\xb8'): 1,
  (10, '\xb9'): 1,
  (10, '\xba'): 1,
  (10, '\xbb'): 28,
  (10, '\xbc'): 29,
  (10, '\xbd'): 1,
  (10, '\xbe'): 1,
  (10, '\xbf'): 1,
  (10, '\xc0'): 1,
  (10, '\xc1'): 1,
  (10, '\xc2'): 1,
  (10, '\xc3'): 1,
  (10, '\xc4'): 1,
  (10, '\xc5'): 1,
  (10, '\xc6'): 1,
  (10, '\xc7'): 1,
  (10, '\xc8'): 1,
  (10, '\xc9'): 1,
  (10, '\xca'): 1,
  (10, '\xcb'): 1,
  (10, '\xcc'): 1,
  (10, '\xcd'): 1,
  (10, '\xce'): 1,
  (10, '\xcf'): 1,
  (10, '\xd0'): 1,
  (10, '\xd1'): 1,
  (10, '\xd2'): 1,
  (10, '\xd3'): 1,
  (10, '\xd4'): 1,
  (10, '\xd5'): 1,
  (10, '\xd6'): 1,
  (10, '\xd7'): 1,
  (10, '\xd8'): 1,
  (10, '\xd9'): 1,
  (10, '\xda'): 1,
  (10, '\xdb'): 1,
  (10, '\xdc'): 1,
  (10, '\xdd'): 1,
  (10, '\xde'): 1,
  (10, '\xdf'): 1,
  (10, '\xe0'): 1,
  (10, '\xe1'): 1,
  (10, '\xe3'): 1,
  (10, '\xe4'): 1,
  (10, '\xe5'): 1,
  (10, '\xe6'): 1,
  (10, '\xe7'): 1,
  (10, '\xe8'): 1,
  (10, '\xe9'): 1,
  (10, '\xea'): 1,
  (10, '\xeb'): 1,
  (10, '\xec'): 1,
  (10, '\xed'): 1,
  (10, '\xee'): 1,
  (10, '\xef'): 1,
  (10, '\xf0'): 1,
  (10, '\xf1'): 1,
  (10, '\xf2'): 1,
  (10, '\xf3'): 1,
  (10, '\xf4'): 1,
  (10, '\xf5'): 1,
  (10, '\xf6'): 1,
  (10, '\xf7'): 1,
  (10, '\xf8'): 1,
  (10, '\xf9'): 1,
  (10, '\xfa'): 1,
  (10, '\xfb'): 1,
  (10, '\xfc'): 1,
  (10, '\xfd'): 1,
  (10, '\xfe'): 1,
  (10, '\xff'): 1,
  (11, '\x80'): 13,
  (11, '\x86'): 15,
  (11, '\x89'): 12,
  (11, '\x9f'): 14,
  (12, '\x94'): 27,
  (13, '\x98'): 19,
  (13, '\x9c'): 20,
  (14, '\xaa'): 18,
  (14, '\xab'): 17,
  (15, '\xa6'): 16,
  (19, '\x00'): 19,
  (19, '\x01'): 19,
  (19, '\x02'): 19,
  (19, '\x03'): 19,
  (19, '\x04'): 19,
  (19, '\x05'): 19,
  (19, '\x06'): 19,
  (19, '\x07'): 19,
  (19, '\x08'): 19,
  (19, '\t'): 19,
  (19, '\n'): 19,
  (19, '\x0b'): 19,
  (19, '\x0c'): 19,
  (19, '\r'): 19,
  (19, '\x0e'): 19,
  (19, '\x0f'): 19,
  (19, '\x10'): 19,
  (19, '\x11'): 19,
  (19, '\x12'): 19,
  (19, '\x13'): 19,
  (19, '\x14'): 19,
  (19, '\x15'): 19,
  (19, '\x16'): 19,
  (19, '\x17'): 19,
  (19, '\x18'): 19,
  (19, '\x19'): 19,
  (19, '\x1a'): 19,
  (19, '\x1b'): 19,
  (19, '\x1c'): 19,
  (19, '\x1d'): 19,
  (19, '\x1e'): 19,
  (19, '\x1f'): 19,
  (19, ' '): 19,
  (19, '!'): 19,
  (19, '"'): 19,
  (19, '#'): 19,
  (19, '$'): 19,
  (19, '%'): 19,
  (19, '&'): 19,
  (19, "'"): 19,
  (19, '('): 19,
  (19, ')'): 19,
  (19, '*'): 19,
  (19, '+'): 19,
  (19, ','): 19,
  (19, '-'): 19,
  (19, '.'): 19,
  (19, '/'): 19,
  (19, '0'): 19,
  (19, '1'): 19,
  (19, '2'): 19,
  (19, '3'): 19,
  (19, '4'): 19,
  (19, '5'): 19,
  (19, '6'): 19,
  (19, '7'): 19,
  (19, '8'): 19,
  (19, '9'): 19,
  (19, ':'): 19,
  (19, ';'): 19,
  (19, '<'): 19,
  (19, '='): 19,
  (19, '>'): 19,
  (19, '?'): 19,
  (19, '@'): 19,
  (19, 'A'): 19,
  (19, 'B'): 19,
  (19, 'C'): 19,
  (19, 'D'): 19,
  (19, 'E'): 19,
  (19, 'F'): 19,
  (19, 'G'): 19,
  (19, 'H'): 19,
  (19, 'I'): 19,
  (19, 'J'): 19,
  (19, 'K'): 19,
  (19, 'L'): 19,
  (19, 'M'): 19,
  (19, 'N'): 19,
  (19, 'O'): 19,
  (19, 'P'): 19,
  (19, 'Q'): 19,
  (19, 'R'): 19,
  (19, 'S'): 19,
  (19, 'T'): 19,
  (19, 'U'): 19,
  (19, 'V'): 19,
  (19, 'W'): 19,
  (19, 'X'): 19,
  (19, 'Y'): 19,
  (19, 'Z'): 19,
  (19, '['): 19,
  (19, '\\'): 19,
  (19, ']'): 19,
  (19, '^'): 19,
  (19, '_'): 19,
  (19, '`'): 19,
  (19, 'a'): 19,
  (19, 'b'): 19,
  (19, 'c'): 19,
  (19, 'd'): 19,
  (19, 'e'): 19,
  (19, 'f'): 19,
  (19, 'g'): 19,
  (19, 'h'): 19,
  (19, 'i'): 19,
  (19, 'j'): 19,
  (19, 'k'): 19,
  (19, 'l'): 19,
  (19, 'm'): 19,
  (19, 'n'): 19,
  (19, 'o'): 19,
  (19, 'p'): 19,
  (19, 'q'): 19,
  (19, 'r'): 19,
  (19, 's'): 19,
  (19, 't'): 19,
  (19, 'u'): 19,
  (19, 'v'): 19,
  (19, 'w'): 19,
  (19, 'x'): 19,
  (19, 'y'): 19,
  (19, 'z'): 19,
  (19, '{'): 19,
  (19, '|'): 19,
  (19, '}'): 19,
  (19, '~'): 19,
  (19, '\x7f'): 19,
  (19, '\x81'): 19,
  (19, '\x82'): 19,
  (19, '\x83'): 19,
  (19, '\x84'): 19,
  (19, '\x85'): 19,
  (19, '\x86'): 19,
  (19, '\x87'): 19,
  (19, '\x88'): 19,
  (19, '\x89'): 19,
  (19, '\x8a'): 19,
  (19, '\x8b'): 19,
  (19, '\x8c'): 19,
  (19, '\x8d'): 19,
  (19, '\x8e'): 19,
  (19, '\x8f'): 19,
  (19, '\x90'): 19,
  (19, '\x91'): 19,
  (19, '\x92'): 19,
  (19, '\x93'): 19,
  (19, '\x94'): 19,
  (19, '\x95'): 19,
  (19, '\x96'): 19,
  (19, '\x97'): 19,
  (19, '\x98'): 19,
  (19, '\x9a'): 19,
  (19, '\x9b'): 19,
  (19, '\x9c'): 19,
  (19, '\x9d'): 19,
  (19, '\x9e'): 19,
  (19, '\x9f'): 19,
  (19, '\xa0'): 19,
  (19, '\xa1'): 19,
  (19, '\xa2'): 19,
  (19, '\xa3'): 19,
  (19, '\xa4'): 19,
  (19, '\xa5'): 19,
  (19, '\xa6'): 19,
  (19, '\xa7'): 19,
  (19, '\xa8'): 19,
  (19, '\xa9'): 19,
  (19, '\xaa'): 19,
  (19, '\xab'): 19,
  (19, '\xac'): 19,
  (19, '\xad'): 19,
  (19, '\xae'): 19,
  (19, '\xaf'): 19,
  (19, '\xb0'): 19,
  (19, '\xb1'): 19,
  (19, '\xb2'): 19,
  (19, '\xb3'): 19,
  (19, '\xb4'): 19,
  (19, '\xb5'): 19,
  (19, '\xb6'): 19,
  (19, '\xb7'): 19,
  (19, '\xb8'): 19,
  (19, '\xb9'): 19,
  (19, '\xba'): 19,
  (19, '\xbb'): 19,
  (19, '\xbc'): 19,
  (19, '\xbd'): 19,
  (19, '\xbe'): 19,
  (19, '\xbf'): 19,
  (19, '\xc0'): 19,
  (19, '\xc1'): 19,
  (19, '\xc2'): 19,
  (19, '\xc3'): 19,
  (19, '\xc4'): 19,
  (19, '\xc5'): 19,
  (19, '\xc6'): 19,
  (19, '\xc7'): 19,
  (19, '\xc8'): 19,
  (19, '\xc9'): 19,
  (19, '\xca'): 19,
  (19, '\xcb'): 19,
  (19, '\xcc'): 19,
  (19, '\xcd'): 19,
  (19, '\xce'): 19,
  (19, '\xcf'): 19,
  (19, '\xd0'): 19,
  (19, '\xd1'): 19,
  (19, '\xd2'): 19,
  (19, '\xd3'): 19,
  (19, '\xd4'): 19,
  (19, '\xd5'): 19,
  (19, '\xd6'): 19,
  (19, '\xd7'): 19,
  (19, '\xd8'): 19,
  (19, '\xd9'): 19,
  (19, '\xda'): 19,
  (19, '\xdb'): 19,
  (19, '\xdc'): 19,
  (19, '\xdd'): 19,
  (19, '\xde'): 19,
  (19, '\xdf'): 19,
  (19, '\xe0'): 19,
  (19, '\xe1'): 19,
  (19, '\xe2'): 24,
  (19, '\xe3'): 19,
  (19, '\xe4'): 19,
  (19, '\xe5'): 19,
  (19, '\xe6'): 19,
  (19, '\xe7'): 19,
  (19, '\xe8'): 19,
  (19, '\xe9'): 19,
  (19, '\xea'): 19,
  (19, '\xeb'): 19,
  (19, '\xec'): 19,
  (19, '\xed'): 19,
  (19, '\xee'): 19,
  (19, '\xef'): 19,
  (19, '\xf0'): 19,
  (19, '\xf1'): 19,
  (19, '\xf2'): 19,
  (19, '\xf3'): 19,
  (19, '\xf4'): 19,
  (19, '\xf5'): 19,
  (19, '\xf6'): 19,
  (19, '\xf7'): 19,
  (19, '\xf8'): 19,
  (19, '\xf9'): 19,
  (19, '\xfa'): 19,
  (19, '\xfb'): 19,
  (19, '\xfc'): 19,
  (19, '\xfd'): 19,
  (19, '\xfe'): 19,
  (19, '\xff'): 19,
  (20, '\x00'): 20,
  (20, '\x01'): 20,
  (20, '\x02'): 20,
  (20, '\x03'): 20,
  (20, '\x04'): 20,
  (20, '\x05'): 20,
  (20, '\x06'): 20,
  (20, '\x07'): 20,
  (20, '\x08'): 20,
  (20, '\t'): 20,
  (20, '\n'): 20,
  (20, '\x0b'): 20,
  (20, '\x0c'): 20,
  (20, '\r'): 20,
  (20, '\x0e'): 20,
  (20, '\x0f'): 20,
  (20, '\x10'): 20,
  (20, '\x11'): 20,
  (20, '\x12'): 20,
  (20, '\x13'): 20,
  (20, '\x14'): 20,
  (20, '\x15'): 20,
  (20, '\x16'): 20,
  (20, '\x17'): 20,
  (20, '\x18'): 20,
  (20, '\x19'): 20,
  (20, '\x1a'): 20,
  (20, '\x1b'): 20,
  (20, '\x1c'): 20,
  (20, '\x1d'): 20,
  (20, '\x1e'): 20,
  (20, '\x1f'): 20,
  (20, ' '): 20,
  (20, '!'): 20,
  (20, '"'): 20,
  (20, '#'): 20,
  (20, '$'): 20,
  (20, '%'): 20,
  (20, '&'): 20,
  (20, "'"): 20,
  (20, '('): 20,
  (20, ')'): 20,
  (20, '*'): 20,
  (20, '+'): 20,
  (20, ','): 20,
  (20, '-'): 20,
  (20, '.'): 20,
  (20, '/'): 20,
  (20, '0'): 20,
  (20, '1'): 20,
  (20, '2'): 20,
  (20, '3'): 20,
  (20, '4'): 20,
  (20, '5'): 20,
  (20, '6'): 20,
  (20, '7'): 20,
  (20, '8'): 20,
  (20, '9'): 20,
  (20, ':'): 20,
  (20, ';'): 20,
  (20, '<'): 20,
  (20, '='): 20,
  (20, '>'): 20,
  (20, '?'): 20,
  (20, '@'): 20,
  (20, 'A'): 20,
  (20, 'B'): 20,
  (20, 'C'): 20,
  (20, 'D'): 20,
  (20, 'E'): 20,
  (20, 'F'): 20,
  (20, 'G'): 20,
  (20, 'H'): 20,
  (20, 'I'): 20,
  (20, 'J'): 20,
  (20, 'K'): 20,
  (20, 'L'): 20,
  (20, 'M'): 20,
  (20, 'N'): 20,
  (20, 'O'): 20,
  (20, 'P'): 20,
  (20, 'Q'): 20,
  (20, 'R'): 20,
  (20, 'S'): 20,
  (20, 'T'): 20,
  (20, 'U'): 20,
  (20, 'V'): 20,
  (20, 'W'): 20,
  (20, 'X'): 20,
  (20, 'Y'): 20,
  (20, 'Z'): 20,
  (20, '['): 20,
  (20, '\\'): 20,
  (20, ']'): 20,
  (20, '^'): 20,
  (20, '_'): 20,
  (20, '`'): 20,
  (20, 'a'): 20,
  (20, 'b'): 20,
  (20, 'c'): 20,
  (20, 'd'): 20,
  (20, 'e'): 20,
  (20, 'f'): 20,
  (20, 'g'): 20,
  (20, 'h'): 20,
  (20, 'i'): 20,
  (20, 'j'): 20,
  (20, 'k'): 20,
  (20, 'l'): 20,
  (20, 'm'): 20,
  (20, 'n'): 20,
  (20, 'o'): 20,
  (20, 'p'): 20,
  (20, 'q'): 20,
  (20, 'r'): 20,
  (20, 's'): 20,
  (20, 't'): 20,
  (20, 'u'): 20,
  (20, 'v'): 20,
  (20, 'w'): 20,
  (20, 'x'): 20,
  (20, 'y'): 20,
  (20, 'z'): 20,
  (20, '{'): 20,
  (20, '|'): 20,
  (20, '}'): 20,
  (20, '~'): 20,
  (20, '\x7f'): 20,
  (20, '\x81'): 20,
  (20, '\x82'): 20,
  (20, '\x83'): 20,
  (20, '\x84'): 20,
  (20, '\x85'): 20,
  (20, '\x86'): 20,
  (20, '\x87'): 20,
  (20, '\x88'): 20,
  (20, '\x89'): 20,
  (20, '\x8a'): 20,
  (20, '\x8b'): 20,
  (20, '\x8c'): 20,
  (20, '\x8d'): 20,
  (20, '\x8e'): 20,
  (20, '\x8f'): 20,
  (20, '\x90'): 20,
  (20, '\x91'): 20,
  (20, '\x92'): 20,
  (20, '\x93'): 20,
  (20, '\x94'): 20,
  (20, '\x95'): 20,
  (20, '\x96'): 20,
  (20, '\x97'): 20,
  (20, '\x98'): 20,
  (20, '\x99'): 20,
  (20, '\x9a'): 20,
  (20, '\x9b'): 20,
  (20, '\x9c'): 20,
  (20, '\x9e'): 20,
  (20, '\x9f'): 20,
  (20, '\xa0'): 20,
  (20, '\xa1'): 20,
  (20, '\xa2'): 20,
  (20, '\xa3'): 20,
  (20, '\xa4'): 20,
  (20, '\xa5'): 20,
  (20, '\xa6'): 20,
  (20, '\xa7'): 20,
  (20, '\xa8'): 20,
  (20, '\xa9'): 20,
  (20, '\xaa'): 20,
  (20, '\xab'): 20,
  (20, '\xac'): 20,
  (20, '\xad'): 20,
  (20, '\xae'): 20,
  (20, '\xaf'): 20,
  (20, '\xb0'): 20,
  (20, '\xb1'): 20,
  (20, '\xb2'): 20,
  (20, '\xb3'): 20,
  (20, '\xb4'): 20,
  (20, '\xb5'): 20,
  (20, '\xb6'): 20,
  (20, '\xb7'): 20,
  (20, '\xb8'): 20,
  (20, '\xb9'): 20,
  (20, '\xba'): 20,
  (20, '\xbb'): 20,
  (20, '\xbc'): 20,
  (20, '\xbd'): 20,
  (20, '\xbe'): 20,
  (20, '\xbf'): 20,
  (20, '\xc0'): 20,
  (20, '\xc1'): 20,
  (20, '\xc2'): 20,
  (20, '\xc3'): 20,
  (20, '\xc4'): 20,
  (20, '\xc5'): 20,
  (20, '\xc6'): 20,
  (20, '\xc7'): 20,
  (20, '\xc8'): 20,
  (20, '\xc9'): 20,
  (20, '\xca'): 20,
  (20, '\xcb'): 20,
  (20, '\xcc'): 20,
  (20, '\xcd'): 20,
  (20, '\xce'): 20,
  (20, '\xcf'): 20,
  (20, '\xd0'): 20,
  (20, '\xd1'): 20,
  (20, '\xd2'): 20,
  (20, '\xd3'): 20,
  (20, '\xd4'): 20,
  (20, '\xd5'): 20,
  (20, '\xd6'): 20,
  (20, '\xd7'): 20,
  (20, '\xd8'): 20,
  (20, '\xd9'): 20,
  (20, '\xda'): 20,
  (20, '\xdb'): 20,
  (20, '\xdc'): 20,
  (20, '\xdd'): 20,
  (20, '\xde'): 20,
  (20, '\xdf'): 20,
  (20, '\xe0'): 20,
  (20, '\xe1'): 20,
  (20, '\xe2'): 21,
  (20, '\xe3'): 20,
  (20, '\xe4'): 20,
  (20, '\xe5'): 20,
  (20, '\xe6'): 20,
  (20, '\xe7'): 20,
  (20, '\xe8'): 20,
  (20, '\xe9'): 20,
  (20, '\xea'): 20,
  (20, '\xeb'): 20,
  (20, '\xec'): 20,
  (20, '\xed'): 20,
  (20, '\xee'): 20,
  (20, '\xef'): 20,
  (20, '\xf0'): 20,
  (20, '\xf1'): 20,
  (20, '\xf2'): 20,
  (20, '\xf3'): 20,
  (20, '\xf4'): 20,
  (20, '\xf5'): 20,
  (20, '\xf6'): 20,
  (20, '\xf7'): 20,
  (20, '\xf8'): 20,
  (20, '\xf9'): 20,
  (20, '\xfa'): 20,
  (20, '\xfb'): 20,
  (20, '\xfc'): 20,
  (20, '\xfd'): 20,
  (20, '\xfe'): 20,
  (20, '\xff'): 20,
  (21, '\x80'): 22,
  (22, '\x9d'): 23,
  (24, '\x80'): 25,
  (25, '\x99'): 26,
  (28, '\x00'): 30,
  (28, '\x01'): 30,
  (28, '\x02'): 30,
  (28, '\x03'): 30,
  (28, '\x04'): 30,
  (28, '\x05'): 30,
  (28, '\x06'): 30,
  (28, '\x07'): 30,
  (28, '\x08'): 30,
  (28, '\t'): 31,
  (28, '\n'): 31,
  (28, '\x0b'): 30,
  (28, '\x0c'): 31,
  (28, '\r'): 31,
  (28, '\x0e'): 30,
  (28, '\x0f'): 30,
  (28, '\x10'): 30,
  (28, '\x11'): 30,
  (28, '\x12'): 30,
  (28, '\x13'): 30,
  (28, '\x14'): 30,
  (28, '\x15'): 30,
  (28, '\x16'): 30,
  (28, '\x17'): 30,
  (28, '\x18'): 30,
  (28, '\x19'): 30,
  (28, '\x1a'): 30,
  (28, '\x1b'): 30,
  (28, '\x1c'): 30,
  (28, '\x1d'): 30,
  (28, '\x1e'): 30,
  (28, '\x1f'): 30,
  (28, ' '): 31,
  (28, '!'): 30,
  (28, '"'): 30,
  (28, '#'): 31,
  (28, '$'): 30,
  (28, '%'): 30,
  (28, '&'): 30,
  (28, "'"): 30,
  (28, '('): 31,
  (28, ')'): 31,
  (28, '*'): 30,
  (28, '+'): 30,
  (28, ','): 31,
  (28, '-'): 30,
  (28, '.'): 30,
  (28, '/'): 30,
  (28, '0'): 30,
  (28, '1'): 30,
  (28, '2'): 30,
  (28, '3'): 30,
  (28, '4'): 30,
  (28, '5'): 30,
  (28, '6'): 30,
  (28, '7'): 30,
  (28, '8'): 30,
  (28, '9'): 30,
  (28, ':'): 30,
  (28, ';'): 30,
  (28, '<'): 30,
  (28, '='): 30,
  (28, '>'): 30,
  (28, '?'): 30,
  (28, '@'): 30,
  (28, 'A'): 30,
  (28, 'B'): 30,
  (28, 'C'): 30,
  (28, 'D'): 30,
  (28, 'E'): 30,
  (28, 'F'): 30,
  (28, 'G'): 30,
  (28, 'H'): 30,
  (28, 'I'): 30,
  (28, 'J'): 30,
  (28, 'K'): 30,
  (28, 'L'): 30,
  (28, 'M'): 30,
  (28, 'N'): 30,
  (28, 'O'): 30,
  (28, 'P'): 30,
  (28, 'Q'): 30,
  (28, 'R'): 30,
  (28, 'S'): 30,
  (28, 'T'): 30,
  (28, 'U'): 30,
  (28, 'V'): 30,
  (28, 'W'): 30,
  (28, 'X'): 30,
  (28, 'Y'): 30,
  (28, 'Z'): 30,
  (28, '['): 30,
  (28, '\\'): 30,
  (28, ']'): 30,
  (28, '^'): 30,
  (28, '_'): 30,
  (28, '`'): 30,
  (28, 'a'): 30,
  (28, 'b'): 30,
  (28, 'c'): 30,
  (28, 'd'): 30,
  (28, 'e'): 30,
  (28, 'f'): 30,
  (28, 'g'): 30,
  (28, 'h'): 30,
  (28, 'i'): 30,
  (28, 'j'): 30,
  (28, 'k'): 30,
  (28, 'l'): 30,
  (28, 'm'): 30,
  (28, 'n'): 30,
  (28, 'o'): 30,
  (28, 'p'): 30,
  (28, 'q'): 30,
  (28, 'r'): 30,
  (28, 's'): 30,
  (28, 't'): 30,
  (28, 'u'): 30,
  (28, 'v'): 30,
  (28, 'w'): 30,
  (28, 'x'): 30,
  (28, 'y'): 30,
  (28, 'z'): 30,
  (28, '{'): 30,
  (28, '|'): 30,
  (28, '}'): 30,
  (28, '~'): 30,
  (28, '\x7f'): 30,
  (28, '\x80'): 30,
  (28, '\x81'): 30,
  (28, '\x82'): 30,
  (28, '\x83'): 30,
  (28, '\x84'): 30,
  (28, '\x85'): 30,
  (28, '\x86'): 30,
  (28, '\x87'): 30,
  (28, '\x88'): 30,
  (28, '\x89'): 30,
  (28, '\x8a'): 30,
  (28, '\x8b'): 30,
  (28, '\x8c'): 30,
  (28, '\x8d'): 30,
  (28, '\x8e'): 30,
  (28, '\x8f'): 30,
  (28, '\x90'): 30,
  (28, '\x91'): 30,
  (28, '\x92'): 30,
  (28, '\x93'): 30,
  (28, '\x94'): 30,
  (28, '\x95'): 30,
  (28, '\x96'): 30,
  (28, '\x97'): 30,
  (28, '\x98'): 30,
  (28, '\x99'): 30,
  (28, '\x9a'): 30,
  (28, '\x9b'): 30,
  (28, '\x9c'): 30,
  (28, '\x9d'): 30,
  (28, '\x9e'): 30,
  (28, '\x9f'): 31,
  (28, '\xa0'): 30,
  (28, '\xa1'): 30,
  (28, '\xa2'): 30,
  (28, '\xa3'): 30,
  (28, '\xa4'): 30,
  (28, '\xa5'): 30,
  (28, '\xa6'): 30,
  (28, '\xa7'): 30,
  (28, '\xa8'): 30,
  (28, '\xa9'): 30,
  (28, '\xaa'): 31,
  (28, '\xab'): 31,
  (28, '\xac'): 30,
  (28, '\xad'): 30,
  (28, '\xae'): 30,
  (28, '\xaf'): 30,
  (28, '\xb0'): 30,
  (28, '\xb1'): 30,
  (28, '\xb2'): 30,
  (28, '\xb3'): 30,
  (28, '\xb4'): 30,
  (28, '\xb5'): 30,
  (28, '\xb6'): 30,
  (28, '\xb7'): 30,
  (28, '\xb8'): 30,
  (28, '\xb9'): 30,
  (28, '\xba'): 30,
  (28, '\xbb'): 30,
  (28, '\xbc'): 30,
  (28, '\xbd'): 30,
  (28, '\xbe'): 30,
  (28, '\xbf'): 30,
  (28, '\xc0'): 30,
  (28, '\xc1'): 30,
  (28, '\xc2'): 30,
  (28, '\xc3'): 30,
  (28, '\xc4'): 30,
  (28, '\xc5'): 30,
  (28, '\xc6'): 30,
  (28, '\xc7'): 30,
  (28, '\xc8'): 30,
  (28, '\xc9'): 30,
  (28, '\xca'): 30,
  (28, '\xcb'): 30,
  (28, '\xcc'): 30,
  (28, '\xcd'): 30,
  (28, '\xce'): 30,
  (28, '\xcf'): 30,
  (28, '\xd0'): 30,
  (28, '\xd1'): 30,
  (28, '\xd2'): 30,
  (28, '\xd3'): 30,
  (28, '\xd4'): 30,
  (28, '\xd5'): 30,
  (28, '\xd6'): 30,
  (28, '\xd7'): 30,
  (28, '\xd8'): 30,
  (28, '\xd9'): 30,
  (28, '\xda'): 30,
  (28, '\xdb'): 30,
  (28, '\xdc'): 30,
  (28, '\xdd'): 30,
  (28, '\xde'): 30,
  (28, '\xdf'): 30,
  (28, '\xe0'): 30,
  (28, '\xe1'): 30,
  (28, '\xe2'): 31,
  (28, '\xe3'): 30,
  (28, '\xe4'): 30,
  (28, '\xe5'): 30,
  (28, '\xe6'): 30,
  (28, '\xe7'): 30,
  (28, '\xe8'): 30,
  (28, '\xe9'): 30,
  (28, '\xea'): 30,
  (28, '\xeb'): 30,
  (28, '\xec'): 30,
  (28, '\xed'): 30,
  (28, '\xee'): 30,
  (28, '\xef'): 30,
  (28, '\xf0'): 30,
  (28, '\xf1'): 30,
  (28, '\xf2'): 30,
  (28, '\xf3'): 30,
  (28, '\xf4'): 30,
  (28, '\xf5'): 30,
  (28, '\xf6'): 30,
  (28, '\xf7'): 30,
  (28, '\xf8'): 30,
  (28, '\xf9'): 30,
  (28, '\xfa'): 30,
  (28, '\xfb'): 30,
  (28, '\xfc'): 30,
  (28, '\xfd'): 30,
  (28, '\xfe'): 30,
  (28, '\xff'): 30,
  (29, '\x00'): 1,
  (29, '\x01'): 1,
  (29, '\x02'): 1,
  (29, '\x03'): 1,
  (29, '\x04'): 1,
  (29, '\x05'): 1,
  (29, '\x06'): 1,
  (29, '\x07'): 1,
  (29, '\x08'): 1,
  (29, '\x0b'): 1,
  (29, '\x0e'): 1,
  (29, '\x0f'): 1,
  (29, '\x10'): 1,
  (29, '\x11'): 1,
  (29, '\x12'): 1,
  (29, '\x13'): 1,
  (29, '\x14'): 1,
  (29, '\x15'): 1,
  (29, '\x16'): 1,
  (29, '\x17'): 1,
  (29, '\x18'): 1,
  (29, '\x19'): 1,
  (29, '\x1a'): 1,
  (29, '\x1b'): 1,
  (29, '\x1c'): 1,
  (29, '\x1d'): 1,
  (29, '\x1e'): 1,
  (29, '\x1f'): 1,
  (29, '!'): 1,
  (29, '"'): 1,
  (29, '$'): 1,
  (29, '%'): 1,
  (29, '&'): 1,
  (29, "'"): 1,
  (29, '*'): 1,
  (29, '+'): 1,
  (29, '-'): 1,
  (29, '.'): 1,
  (29, '/'): 1,
  (29, '0'): 1,
  (29, '1'): 1,
  (29, '2'): 1,
  (29, '3'): 1,
  (29, '4'): 1,
  (29, '5'): 1,
  (29, '6'): 1,
  (29, '7'): 1,
  (29, '8'): 1,
  (29, '9'): 1,
  (29, ':'): 1,
  (29, ';'): 1,
  (29, '<'): 1,
  (29, '='): 1,
  (29, '>'): 1,
  (29, '?'): 1,
  (29, '@'): 1,
  (29, 'A'): 1,
  (29, 'B'): 1,
  (29, 'C'): 1,
  (29, 'D'): 1,
  (29, 'E'): 1,
  (29, 'F'): 1,
  (29, 'G'): 1,
  (29, 'H'): 1,
  (29, 'I'): 1,
  (29, 'J'): 1,
  (29, 'K'): 1,
  (29, 'L'): 1,
  (29, 'M'): 1,
  (29, 'N'): 1,
  (29, 'O'): 1,
  (29, 'P'): 1,
  (29, 'Q'): 1,
  (29, 'R'): 1,
  (29, 'S'): 1,
  (29, 'T'): 1,
  (29, 'U'): 1,
  (29, 'V'): 1,
  (29, 'W'): 1,
  (29, 'X'): 1,
  (29, 'Y'): 1,
  (29, 'Z'): 1,
  (29, '['): 1,
  (29, '\\'): 1,
  (29, ']'): 1,
  (29, '^'): 1,
  (29, '_'): 1,
  (29, '`'): 1,
  (29, 'a'): 1,
  (29, 'b'): 1,
  (29, 'c'): 1,
  (29, 'd'): 1,
  (29, 'e'): 1,
  (29, 'f'): 1,
  (29, 'g'): 1,
  (29, 'h'): 1,
  (29, 'i'): 1,
  (29, 'j'): 1,
  (29, 'k'): 1,
  (29, 'l'): 1,
  (29, 'm'): 1,
  (29, 'n'): 1,
  (29, 'o'): 1,
  (29, 'p'): 1,
  (29, 'q'): 1,
  (29, 'r'): 1,
  (29, 's'): 1,
  (29, 't'): 1,
  (29, 'u'): 1,
  (29, 'v'): 1,
  (29, 'w'): 1,
  (29, 'x'): 1,
  (29, 'y'): 1,
  (29, 'z'): 1,
  (29, '{'): 1,
  (29, '|'): 1,
  (29, '}'): 1,
  (29, '~'): 1,
  (29, '\x7f'): 1,
  (29, '\x80'): 1,
  (29, '\x81'): 1,
  (29, '\x82'): 1,
  (29, '\x83'): 1,
  (29, '\x84'): 1,
  (29, '\x85'): 1,
  (29, '\x86'): 1,
  (29, '\x87'): 1,
  (29, '\x88'): 1,
  (29, '\x89'): 1,
  (29, '\x8a'): 1,
  (29, '\x8b'): 1,
  (29, '\x8c'): 1,
  (29, '\x8d'): 1,
  (29, '\x8e'): 1,
  (29, '\x8f'): 1,
  (29, '\x90'): 1,
  (29, '\x91'): 1,
  (29, '\x92'): 1,
  (29, '\x93'): 1,
  (29, '\x94'): 1,
  (29, '\x95'): 1,
  (29, '\x96'): 1,
  (29, '\x97'): 1,
  (29, '\x98'): 1,
  (29, '\x99'): 1,
  (29, '\x9a'): 1,
  (29, '\x9b'): 1,
  (29, '\x9c'): 1,
  (29, '\x9d'): 1,
  (29, '\x9e'): 1,
  (29, '\xa0'): 1,
  (29, '\xa1'): 1,
  (29, '\xa2'): 1,
  (29, '\xa3'): 1,
  (29, '\xa4'): 1,
  (29, '\xa5'): 1,
  (29, '\xa6'): 1,
  (29, '\xa7'): 1,
  (29, '\xa8'): 1,
  (29, '\xa9'): 1,
  (29, '\xac'): 1,
  (29, '\xad'): 1,
  (29, '\xae'): 1,
  (29, '\xaf'): 1,
  (29, '\xb0'): 1,
  (29, '\xb1'): 1,
  (29, '\xb2'): 1,
  (29, '\xb3'): 1,
  (29, '\xb4'): 1,
  (29, '\xb5'): 1,
  (29, '\xb6'): 1,
  (29, '\xb7'): 1,
  (29, '\xb8'): 1,
  (29, '\xb9'): 1,
  (29, '\xba'): 1,
  (29, '\xbb'): 1,
  (29, '\xbc'): 1,
  (29, '\xbd'): 1,
  (29, '\xbe'): 1,
  (29, '\xbf'): 1,
  (29, '\xc0'): 1,
  (29, '\xc1'): 1,
  (29, '\xc2'): 1,
  (29, '\xc3'): 1,
  (29, '\xc4'): 1,
  (29, '\xc5'): 1,
  (29, '\xc6'): 1,
  (29, '\xc7'): 1,
  (29, '\xc8'): 1,
  (29, '\xc9'): 1,
  (29, '\xca'): 1,
  (29, '\xcb'): 1,
  (29, '\xcc'): 1,
  (29, '\xcd'): 1,
  (29, '\xce'): 1,
  (29, '\xcf'): 1,
  (29, '\xd0'): 1,
  (29, '\xd1'): 1,
  (29, '\xd2'): 1,
  (29, '\xd3'): 1,
  (29, '\xd4'): 1,
  (29, '\xd5'): 1,
  (29, '\xd6'): 1,
  (29, '\xd7'): 1,
  (29, '\xd8'): 1,
  (29, '\xd9'): 1,
  (29, '\xda'): 1,
  (29, '\xdb'): 1,
  (29, '\xdc'): 1,
  (29, '\xdd'): 1,
  (29, '\xde'): 1,
  (29, '\xdf'): 1,
  (29, '\xe0'): 1,
  (29, '\xe1'): 1,
  (29, '\xe3'): 1,
  (29, '\xe4'): 1,
  (29, '\xe5'): 1,
  (29, '\xe6'): 1,
  (29, '\xe7'): 1,
  (29, '\xe8'): 1,
  (29, '\xe9'): 1,
  (29, '\xea'): 1,
  (29, '\xeb'): 1,
  (29, '\xec'): 1,
  (29, '\xed'): 1,
  (29, '\xee'): 1,
  (29, '\xef'): 1,
  (29, '\xf0'): 1,
  (29, '\xf1'): 1,
  (29, '\xf2'): 1,
  (29, '\xf3'): 1,
  (29, '\xf4'): 1,
  (29, '\xf5'): 1,
  (29, '\xf6'): 1,
  (29, '\xf7'): 1,
  (29, '\xf8'): 1,
  (29, '\xf9'): 1,
  (29, '\xfa'): 1,
  (29, '\xfb'): 1,
  (29, '\xfc'): 1,
  (29, '\xfd'): 1,
  (29, '\xfe'): 1,
  (29, '\xff'): 1,
  (30, '\x00'): 1,
  (30, '\x01'): 1,
  (30, '\x02'): 1,
  (30, '\x03'): 1,
  (30, '\x04'): 1,
  (30, '\x05'): 1,
  (30, '\x06'): 1,
  (30, '\x07'): 1,
  (30, '\x08'): 1,
  (30, '\x0b'): 1,
  (30, '\x0e'): 1,
  (30, '\x0f'): 1,
  (30, '\x10'): 1,
  (30, '\x11'): 1,
  (30, '\x12'): 1,
  (30, '\x13'): 1,
  (30, '\x14'): 1,
  (30, '\x15'): 1,
  (30, '\x16'): 1,
  (30, '\x17'): 1,
  (30, '\x18'): 1,
  (30, '\x19'): 1,
  (30, '\x1a'): 1,
  (30, '\x1b'): 1,
  (30, '\x1c'): 1,
  (30, '\x1d'): 1,
  (30, '\x1e'): 1,
  (30, '\x1f'): 1,
  (30, '!'): 1,
  (30, '"'): 1,
  (30, '$'): 1,
  (30, '%'): 1,
  (30, '&'): 1,
  (30, "'"): 1,
  (30, '*'): 1,
  (30, '+'): 1,
  (30, '-'): 1,
  (30, '.'): 1,
  (30, '/'): 1,
  (30, '0'): 1,
  (30, '1'): 1,
  (30, '2'): 1,
  (30, '3'): 1,
  (30, '4'): 1,
  (30, '5'): 1,
  (30, '6'): 1,
  (30, '7'): 1,
  (30, '8'): 1,
  (30, '9'): 1,
  (30, ':'): 1,
  (30, ';'): 1,
  (30, '<'): 1,
  (30, '='): 1,
  (30, '>'): 1,
  (30, '?'): 1,
  (30, '@'): 1,
  (30, 'A'): 1,
  (30, 'B'): 1,
  (30, 'C'): 1,
  (30, 'D'): 1,
  (30, 'E'): 1,
  (30, 'F'): 1,
  (30, 'G'): 1,
  (30, 'H'): 1,
  (30, 'I'): 1,
  (30, 'J'): 1,
  (30, 'K'): 1,
  (30, 'L'): 1,
  (30, 'M'): 1,
  (30, 'N'): 1,
  (30, 'O'): 1,
  (30, 'P'): 1,
  (30, 'Q'): 1,
  (30, 'R'): 1,
  (30, 'S'): 1,
  (30, 'T'): 1,
  (30, 'U'): 1,
  (30, 'V'): 1,
  (30, 'W'): 1,
  (30, 'X'): 1,
  (30, 'Y'): 1,
  (30, 'Z'): 1,
  (30, '['): 1,
  (30, '\\'): 1,
  (30, ']'): 1,
  (30, '^'): 1,
  (30, '_'): 1,
  (30, '`'): 1,
  (30, 'a'): 1,
  (30, 'b'): 1,
  (30, 'c'): 1,
  (30, 'd'): 1,
  (30, 'e'): 1,
  (30, 'f'): 1,
  (30, 'g'): 1,
  (30, 'h'): 1,
  (30, 'i'): 1,
  (30, 'j'): 1,
  (30, 'k'): 1,
  (30, 'l'): 1,
  (30, 'm'): 1,
  (30, 'n'): 1,
  (30, 'o'): 1,
  (30, 'p'): 1,
  (30, 'q'): 1,
  (30, 'r'): 1,
  (30, 's'): 1,
  (30, 't'): 1,
  (30, 'u'): 1,
  (30, 'v'): 1,
  (30, 'w'): 1,
  (30, 'x'): 1,
  (30, 'y'): 1,
  (30, 'z'): 1,
  (30, '{'): 1,
  (30, '|'): 1,
  (30, '}'): 1,
  (30, '~'): 1,
  (30, '\x7f'): 1,
  (30, '\x80'): 1,
  (30, '\x81'): 1,
  (30, '\x82'): 1,
  (30, '\x83'): 1,
  (30, '\x84'): 1,
  (30, '\x85'): 1,
  (30, '\x86'): 1,
  (30, '\x87'): 1,
  (30, '\x88'): 1,
  (30, '\x89'): 1,
  (30, '\x8a'): 1,
  (30, '\x8b'): 1,
  (30, '\x8c'): 1,
  (30, '\x8d'): 1,
  (30, '\x8e'): 1,
  (30, '\x8f'): 1,
  (30, '\x90'): 1,
  (30, '\x91'): 1,
  (30, '\x92'): 1,
  (30, '\x93'): 1,
  (30, '\x94'): 1,
  (30, '\x95'): 1,
  (30, '\x96'): 1,
  (30, '\x97'): 1,
  (30, '\x98'): 1,
  (30, '\x99'): 1,
  (30, '\x9a'): 1,
  (30, '\x9b'): 1,
  (30, '\x9c'): 1,
  (30, '\x9d'): 1,
  (30, '\x9e'): 1,
  (30, '\xa0'): 1,
  (30, '\xa1'): 1,
  (30, '\xa2'): 1,
  (30, '\xa3'): 1,
  (30, '\xa4'): 1,
  (30, '\xa5'): 1,
  (30, '\xa6'): 1,
  (30, '\xa7'): 1,
  (30, '\xa8'): 1,
  (30, '\xa9'): 1,
  (30, '\xac'): 1,
  (30, '\xad'): 1,
  (30, '\xae'): 1,
  (30, '\xaf'): 1,
  (30, '\xb0'): 1,
  (30, '\xb1'): 1,
  (30, '\xb2'): 1,
  (30, '\xb3'): 1,
  (30, '\xb4'): 1,
  (30, '\xb5'): 1,
  (30, '\xb6'): 1,
  (30, '\xb7'): 1,
  (30, '\xb8'): 1,
  (30, '\xb9'): 1,
  (30, '\xba'): 1,
  (30, '\xbb'): 1,
  (30, '\xbc'): 1,
  (30, '\xbd'): 1,
  (30, '\xbe'): 1,
  (30, '\xbf'): 1,
  (30, '\xc0'): 1,
  (30, '\xc1'): 1,
  (30, '\xc2'): 1,
  (30, '\xc3'): 1,
  (30, '\xc4'): 1,
  (30, '\xc5'): 1,
  (30, '\xc6'): 1,
  (30, '\xc7'): 1,
  (30, '\xc8'): 1,
  (30, '\xc9'): 1,
  (30, '\xca'): 1,
  (30, '\xcb'): 1,
  (30, '\xcc'): 1,
  (30, '\xcd'): 1,
  (30, '\xce'): 1,
  (30, '\xcf'): 1,
  (30, '\xd0'): 1,
  (30, '\xd1'): 1,
  (30, '\xd2'): 1,
  (30, '\xd3'): 1,
  (30, '\xd4'): 1,
  (30, '\xd5'): 1,
  (30, '\xd6'): 1,
  (30, '\xd7'): 1,
  (30, '\xd8'): 1,
  (30, '\xd9'): 1,
  (30, '\xda'): 1,
  (30, '\xdb'): 1,
  (30, '\xdc'): 1,
  (30, '\xdd'): 1,
  (30, '\xde'): 1,
  (30, '\xdf'): 1,
  (30, '\xe0'): 1,
  (30, '\xe1'): 1,
  (30, '\xe3'): 1,
  (30, '\xe4'): 1,
  (30, '\xe5'): 1,
  (30, '\xe6'): 1,
  (30, '\xe7'): 1,
  (30, '\xe8'): 1,
  (30, '\xe9'): 1,
  (30, '\xea'): 1,
  (30, '\xeb'): 1,
  (30, '\xec'): 1,
  (30, '\xed'): 1,
  (30, '\xee'): 1,
  (30, '\xef'): 1,
  (30, '\xf0'): 1,
  (30, '\xf1'): 1,
  (30, '\xf2'): 1,
  (30, '\xf3'): 1,
  (30, '\xf4'): 1,
  (30, '\xf5'): 1,
  (30, '\xf6'): 1,
  (30, '\xf7'): 1,
  (30, '\xf8'): 1,
  (30, '\xf9'): 1,
  (30, '\xfa'): 1,
  (30, '\xfb'): 1,
  (30, '\xfc'): 1,
  (30, '\xfd'): 1,
  (30, '\xfe'): 1,
  (30, '\xff'): 1},
 set([0,
      1,
      2,
      3,
      4,
      5,
      6,
      7,
      8,
      9,
      10,
      16,
      17,
      18,
      23,
      26,
      27,
      28,
      29,
      30,
      31]),
 set([0,
      1,
      2,
      3,
      4,
      5,
      6,
      7,
      8,
      9,
      10,
      16,
      17,
      18,
      23,
      26,
      27,
      28,
      29,
      30,
      31]),
 ['IGNORE',
  'NAME',
  'IGNORE',
  'LEFT_PARENTHESIS',
  '__0_,',
  'INTEGER',
  'IGNORE',
  'NEWLINE',
  '__1_.',
  'RIGHT_PARENTHESIS',
  'NAME',
  '1, 1, 1, 1, 1, 1',
  '2',
  '2, 2',
  '2, 2',
  '2',
  'MAPSTO',
  'RIGHT_DOUBLE_ANGLE',
  'LEFT_DOUBLE_ANGLE',
  '3, final*, 0, start|, 0, start|, 0, start|, 0, final*, start*, 0, final*, 0, 1, final|, start|, 0, final|, start|, 0, final|, start|, 0, final*, start*, 0, final*, 0, start|, 0, start|, 0, final|, start|, 0, 1, final*, start*, 0, final*, 0, final|, start|, 0, 1, final|, start|, 0, final|, start|, 0, final*, start*, 0, final*, 0, start|, 0, final|, start|, 0, 1, final|, start|, 0, final*, start*, 0',
  '3, final*, 0, start|, 0, start|, 0, start|, 0, final*, start*, 0, final*, 0, 1, final|, start|, 0, final|, start|, 0, final|, start|, 0, final*, start*, 0, final*, 0, start|, 0, start|, 0, final|, start|, 0, 1, final*, start*, 0, final*, 0, final|, start|, 0, 1, final|, start|, 0, final|, start|, 0, final*, start*, 0, final*, 0, start|, 0, final|, start|, 0, 1, final|, start|, 0, final*, start*, 0',
  '0, final*, 1',
  'final*, 1, 0',
  'QQSTRING',
  '0, final*, 1',
  'final*, 1, 0',
  'QSTRING',
  'DEFINEDAS',
  'NAME',
  'MU',
  'LAMBDA',
  'LAMBDA']), {'IGNORE': None})
# generated code between this line and its other occurence

def make_lamb_parser_dynamic():
    from rpython.rlib.parsing.ebnfparse import parse_ebnf, check_for_missing_names

    filename = py.path.local(__file__).dirpath("lamb.ebnf")
    try:
        ebnf_source = py.path.local(filename).read(mode='U')
        rs, rules, tr = parse_ebnf(ebnf_source)
    except PyParseError,e:
        print e.nice_error_message(filename=filename,source=ebnf_source)
        raise

    names, regexs = zip(*rs)
    check_for_missing_names(names, regexs, rules)
    lx = Lexer(list(regexs), list(names), ignore=["IGNORE"])
    pr = PackratParser(rules, rules[0].nonterminal)
    # pr = PackratParser(rules, rules[0].nonterminal, check_for_left_recursion=True)
    return pr, lx, tr

def make_lamb_parser_generated():
    return parser, lexer, LambToAST

def make_lamb_parser():
    if use_dynamic_parser:
        return make_lamb_parser_dynamic()
    else:
        return make_lamb_parser_generated()

############################################################################
if __name__ == '__main__':
    f = py.path.local(__file__)
    oldcontent = f.read().decode("utf-8")
    s = u"# GENERATED CODE BETWEEN THIS LINE AND ITS OTHER OCCURENCE\n".lower()
    pre, gen, after = oldcontent.split(s)

    parser, lexer, ToAST = make_lamb_parser_dynamic()
    transformer = ToAST.source
    newcontent = u"%s%s%s\nparser = %r\n%s\n%s%s" % (
            pre, s, transformer.replace("ToAST", "LambToAST"),
            parser, lexer.get_dummy_repr(), s, after)
    print newcontent
    f.write(newcontent.encode("utf-8"))
