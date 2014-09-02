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

sys.setrecursionlimit(100000)
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

class LambdaInfo(object):
    def __init__(self, node):
        self._node = node
    def node(self):
        return node
    def error(self, reason):
        raise ParseError(self._node.getsourcepos(), reason)


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

    def parse(self, source, w_argv=None, is_file=False):
        self._reset()
        if w_argv is not None:
            self.define("arguments", w_argv)
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

    def define_lambda(self, inbox):
        innermost_scope = self.bindings_stack[-1]
        box = innermost_scope.get(inbox.name, None)
        if box is not None:
            box.update(inbox)
        else:
            innermost_scope[inbox.name] = inbox

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
                self.define_lambda(expression.LambdaBox(
                    LambdaInfo(node), name, l))
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
        return [model.w_integer(int(node.additional_info))]

    def visit_FLOAT(self, node):
        return [model.w_float(float(node.additional_info))]

    # productions

    def visit_lambda_definition(self, node):
        assert len(node.children) == 2
        name = self.get_name(node)
        definee = self.make_lambda(node.children[1], name)
        self.define_lambda(expression.LambdaBox(
            LambdaInfo(node), name, definee))
        return [no_result]

    def visit_lambda_forward(self, node):
        "Forward-define a lambda, for co-recursion"
        assert len(node.children) >= 1
        name = self.get_name(node)
        l = model.W_Lambda(rules=[], name=name)
        self.define_lambda(expression.LambdaBox(
            LambdaInfo(node),name, l))
        return [no_result]

    def visit_value_definition(self, node):
        assert len(node.children) == 2
        name = self.get_name(node)
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
        w_c = expression.W_ConstructorEvaluator(model.tag(name, len(ch)), ch)
        return [w_c]

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


def parse_file(filename, w_argv=None):
     p = Parser()
     elements = p.parse(filename, w_argv, is_file=True)
     result = [element for element in elements if element is not no_result]
     bindings = p.toplevel_bindings()
     return (result, bindings)

def parse_string(string, w_argv=None):
     p = Parser()
     elements = p.parse(string, w_argv, is_file=False)
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
        if node.children[0].symbol == 'FLOAT':
            return [node.children[0]]
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
        if node.children[0].symbol == 'lambda_definition':
            return self.visit_lambda_definition(node.children[0])
        if node.children[0].symbol == 'lambda_forward':
            return self.visit_lambda_forward(node.children[0])
        return self.visit_value_definition(node.children[0])
    def visit_lambda_definition(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend([node.children[0]])
        children.extend(self.visit_lambda(node.children[2]))
        return [Nonterminal(node.symbol, children)]
    def visit_lambda_forward(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend([node.children[0]])
        return [Nonterminal(node.symbol, children)]
    def visit_value_definition(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend([node.children[0]])
        children.extend(self.visit_expression(node.children[2]))
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
  Rule('primary', [['INTEGER'], ['FLOAT'], ['QSTRING'], ['QQSTRING']]),
  Rule('variable', [['NAME']]),
  Rule('definition', [['lambda_definition'], ['lambda_forward'], ['value_definition']]),
  Rule('lambda_definition', [['NAME', 'DEFINEDAS', 'lambda']]),
  Rule('lambda_forward', [['NAME', 'DEFINEDAS', 'ULAMBDA']]),
  Rule('value_definition', [['NAME', 'DEFINEDAS', 'expression']]),
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
            elif char == '\x0b':
                state = 1
            elif char == '*':
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
            elif char == '+':
                state = 7
            elif char == '-':
                state = 7
            elif char == '\n':
                state = 8
            elif char == '\r':
                state = 8
            elif char == '.':
                state = 9
            elif char == ')':
                state = 10
            elif char == '\xce':
                state = 11
            elif char == '\xe2':
                state = 12
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
            elif char == '.':
                state = 39
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
        if state == 7:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 7
                return i
            if ':' <= char <= '\x9e':
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
            elif char == '-':
                state = 1
                continue
            elif char == '/':
                state = 1
                continue
            elif '0' <= char <= '9':
                state = 37
            elif char == '.':
                state = 38
            else:
                break
        if state == 9:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 9
                return i
            if ':' <= char <= '\x9e':
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
            elif '-' <= char <= '/':
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
            elif '0' <= char <= '9':
                state = 36
            else:
                break
        if state == 11:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 11
                return i
            if '-' <= char <= '\x9a':
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
            elif '\x9c' <= char <= '\x9e':
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
            elif char == '\x9b':
                state = 29
            elif char == '\xbb':
                state = 30
            elif char == '\xbc':
                state = 31
            else:
                break
        if state == 12:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 12
                return ~i
            if char == '\x86':
                state = 16
            elif char == '\x89':
                state = 13
            elif char == '\x80':
                state = 14
            elif char == '\x9f':
                state = 15
            else:
                break
        if state == 13:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 13
                return ~i
            if char == '\x94':
                state = 28
            else:
                break
        if state == 14:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 14
                return ~i
            if char == '\x98':
                state = 20
            elif char == '\x9c':
                state = 21
            else:
                break
        if state == 15:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 15
                return ~i
            if char == '\xab':
                state = 18
            elif char == '\xaa':
                state = 19
            else:
                break
        if state == 16:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 16
                return ~i
            if char == '\xa6':
                state = 17
            else:
                break
        if state == 20:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 20
                return ~i
            if char == '\xe2':
                state = 25
            elif '\x00' <= char <= '\x7f':
                state = 20
                continue
            elif '\x9a' <= char <= '\xe1':
                state = 20
                continue
            elif '\xe3' <= char <= '\xff':
                state = 20
                continue
            elif '\x81' <= char <= '\x98':
                state = 20
                continue
            else:
                break
        if state == 21:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 21
                return ~i
            if '\x00' <= char <= '\x7f':
                state = 21
                continue
            elif '\x9e' <= char <= '\xe1':
                state = 21
                continue
            elif '\xe3' <= char <= '\xff':
                state = 21
                continue
            elif '\x81' <= char <= '\x9c':
                state = 21
                continue
            elif char == '\xe2':
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
            if char == '\x80':
                state = 23
            else:
                break
        if state == 23:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 23
                return ~i
            if char == '\x9d':
                state = 24
            else:
                break
        if state == 25:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 25
                return ~i
            if char == '\x80':
                state = 26
            else:
                break
        if state == 26:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 26
                return ~i
            if char == '\x99':
                state = 27
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
                state = 34
            elif '\xac' <= char <= '\xe1':
                state = 34
            elif '\xe3' <= char <= '\xff':
                state = 34
            elif '\x0e' <= char <= '\x1f':
                state = 34
            elif '\xa0' <= char <= '\xa9':
                state = 34
            elif '\x00' <= char <= '\x08':
                state = 34
            elif '$' <= char <= "'":
                state = 34
            elif char == '!':
                state = 34
            elif char == '"':
                state = 34
            elif char == '*':
                state = 34
            elif char == '+':
                state = 34
            elif char == '\x0b':
                state = 34
            elif char == '\t':
                state = 35
            elif char == '\n':
                state = 35
            elif char == '\x0c':
                state = 35
            elif char == '\r':
                state = 35
            elif char == '(':
                state = 35
            elif char == ')':
                state = 35
            elif char == '\xaa':
                state = 35
            elif char == '\xab':
                state = 35
            elif char == ' ':
                state = 35
            elif char == '#':
                state = 35
            elif char == ',':
                state = 35
            elif char == '\x9f':
                state = 35
            elif char == '\xe2':
                state = 35
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
                state = 32
            elif '\xac' <= char <= '\xe1':
                state = 32
            elif '\xe3' <= char <= '\xff':
                state = 32
            elif '\x0e' <= char <= '\x1f':
                state = 32
            elif '\xa0' <= char <= '\xa9':
                state = 32
            elif '\x00' <= char <= '\x08':
                state = 32
            elif '$' <= char <= "'":
                state = 32
            elif char == '!':
                state = 32
            elif char == '"':
                state = 32
            elif char == '*':
                state = 32
            elif char == '+':
                state = 32
            elif char == '\x0b':
                state = 32
            elif char == '\t':
                state = 33
            elif char == '\n':
                state = 33
            elif char == '\x0c':
                state = 33
            elif char == '\r':
                state = 33
            elif char == '(':
                state = 33
            elif char == ')':
                state = 33
            elif char == '\xaa':
                state = 33
            elif char == '\xab':
                state = 33
            elif char == ' ':
                state = 33
            elif char == '#':
                state = 33
            elif char == ',':
                state = 33
            elif char == '\x9f':
                state = 33
            elif char == '\xe2':
                state = 33
            else:
                break
        if state == 31:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 31
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
        if state == 32:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 32
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
        if state == 34:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 34
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
        if state == 36:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 36
                return i
            if ':' <= char <= '\x9e':
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
            elif '-' <= char <= '/':
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
            elif '0' <= char <= '9':
                state = 36
                continue
            else:
                break
        if state == 37:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 37
                return i
            if ':' <= char <= '\x9e':
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
            elif char == '-':
                state = 1
                continue
            elif char == '/':
                state = 1
                continue
            elif '0' <= char <= '9':
                state = 37
                continue
            elif char == '.':
                state = 38
            else:
                break
        if state == 38:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 38
                return i
            if ':' <= char <= '\x9e':
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
            elif '-' <= char <= '/':
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
            elif '0' <= char <= '9':
                state = 36
                continue
            else:
                break
        if state == 39:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 39
                return ~i
            if '0' <= char <= '9':
                state = 40
            else:
                break
        if state == 40:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 40
                return i
            if '0' <= char <= '9':
                state = 40
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
lexer = DummyLexer(recognize, DFA(41,
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
  (0, '\n'): 8,
  (0, '\x0b'): 1,
  (0, '\x0c'): 2,
  (0, '\r'): 8,
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
  (0, ')'): 10,
  (0, '*'): 1,
  (0, '+'): 7,
  (0, ','): 4,
  (0, '-'): 7,
  (0, '.'): 9,
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
  (0, '\xce'): 11,
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
  (0, '\xe2'): 12,
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
  (5, '.'): 39,
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
  (7, '\x00'): 1,
  (7, '\x01'): 1,
  (7, '\x02'): 1,
  (7, '\x03'): 1,
  (7, '\x04'): 1,
  (7, '\x05'): 1,
  (7, '\x06'): 1,
  (7, '\x07'): 1,
  (7, '\x08'): 1,
  (7, '\x0b'): 1,
  (7, '\x0e'): 1,
  (7, '\x0f'): 1,
  (7, '\x10'): 1,
  (7, '\x11'): 1,
  (7, '\x12'): 1,
  (7, '\x13'): 1,
  (7, '\x14'): 1,
  (7, '\x15'): 1,
  (7, '\x16'): 1,
  (7, '\x17'): 1,
  (7, '\x18'): 1,
  (7, '\x19'): 1,
  (7, '\x1a'): 1,
  (7, '\x1b'): 1,
  (7, '\x1c'): 1,
  (7, '\x1d'): 1,
  (7, '\x1e'): 1,
  (7, '\x1f'): 1,
  (7, '!'): 1,
  (7, '"'): 1,
  (7, '$'): 1,
  (7, '%'): 1,
  (7, '&'): 1,
  (7, "'"): 1,
  (7, '*'): 1,
  (7, '+'): 1,
  (7, '-'): 1,
  (7, '.'): 38,
  (7, '/'): 1,
  (7, '0'): 37,
  (7, '1'): 37,
  (7, '2'): 37,
  (7, '3'): 37,
  (7, '4'): 37,
  (7, '5'): 37,
  (7, '6'): 37,
  (7, '7'): 37,
  (7, '8'): 37,
  (7, '9'): 37,
  (7, ':'): 1,
  (7, ';'): 1,
  (7, '<'): 1,
  (7, '='): 1,
  (7, '>'): 1,
  (7, '?'): 1,
  (7, '@'): 1,
  (7, 'A'): 1,
  (7, 'B'): 1,
  (7, 'C'): 1,
  (7, 'D'): 1,
  (7, 'E'): 1,
  (7, 'F'): 1,
  (7, 'G'): 1,
  (7, 'H'): 1,
  (7, 'I'): 1,
  (7, 'J'): 1,
  (7, 'K'): 1,
  (7, 'L'): 1,
  (7, 'M'): 1,
  (7, 'N'): 1,
  (7, 'O'): 1,
  (7, 'P'): 1,
  (7, 'Q'): 1,
  (7, 'R'): 1,
  (7, 'S'): 1,
  (7, 'T'): 1,
  (7, 'U'): 1,
  (7, 'V'): 1,
  (7, 'W'): 1,
  (7, 'X'): 1,
  (7, 'Y'): 1,
  (7, 'Z'): 1,
  (7, '['): 1,
  (7, '\\'): 1,
  (7, ']'): 1,
  (7, '^'): 1,
  (7, '_'): 1,
  (7, '`'): 1,
  (7, 'a'): 1,
  (7, 'b'): 1,
  (7, 'c'): 1,
  (7, 'd'): 1,
  (7, 'e'): 1,
  (7, 'f'): 1,
  (7, 'g'): 1,
  (7, 'h'): 1,
  (7, 'i'): 1,
  (7, 'j'): 1,
  (7, 'k'): 1,
  (7, 'l'): 1,
  (7, 'm'): 1,
  (7, 'n'): 1,
  (7, 'o'): 1,
  (7, 'p'): 1,
  (7, 'q'): 1,
  (7, 'r'): 1,
  (7, 's'): 1,
  (7, 't'): 1,
  (7, 'u'): 1,
  (7, 'v'): 1,
  (7, 'w'): 1,
  (7, 'x'): 1,
  (7, 'y'): 1,
  (7, 'z'): 1,
  (7, '{'): 1,
  (7, '|'): 1,
  (7, '}'): 1,
  (7, '~'): 1,
  (7, '\x7f'): 1,
  (7, '\x80'): 1,
  (7, '\x81'): 1,
  (7, '\x82'): 1,
  (7, '\x83'): 1,
  (7, '\x84'): 1,
  (7, '\x85'): 1,
  (7, '\x86'): 1,
  (7, '\x87'): 1,
  (7, '\x88'): 1,
  (7, '\x89'): 1,
  (7, '\x8a'): 1,
  (7, '\x8b'): 1,
  (7, '\x8c'): 1,
  (7, '\x8d'): 1,
  (7, '\x8e'): 1,
  (7, '\x8f'): 1,
  (7, '\x90'): 1,
  (7, '\x91'): 1,
  (7, '\x92'): 1,
  (7, '\x93'): 1,
  (7, '\x94'): 1,
  (7, '\x95'): 1,
  (7, '\x96'): 1,
  (7, '\x97'): 1,
  (7, '\x98'): 1,
  (7, '\x99'): 1,
  (7, '\x9a'): 1,
  (7, '\x9b'): 1,
  (7, '\x9c'): 1,
  (7, '\x9d'): 1,
  (7, '\x9e'): 1,
  (7, '\xa0'): 1,
  (7, '\xa1'): 1,
  (7, '\xa2'): 1,
  (7, '\xa3'): 1,
  (7, '\xa4'): 1,
  (7, '\xa5'): 1,
  (7, '\xa6'): 1,
  (7, '\xa7'): 1,
  (7, '\xa8'): 1,
  (7, '\xa9'): 1,
  (7, '\xac'): 1,
  (7, '\xad'): 1,
  (7, '\xae'): 1,
  (7, '\xaf'): 1,
  (7, '\xb0'): 1,
  (7, '\xb1'): 1,
  (7, '\xb2'): 1,
  (7, '\xb3'): 1,
  (7, '\xb4'): 1,
  (7, '\xb5'): 1,
  (7, '\xb6'): 1,
  (7, '\xb7'): 1,
  (7, '\xb8'): 1,
  (7, '\xb9'): 1,
  (7, '\xba'): 1,
  (7, '\xbb'): 1,
  (7, '\xbc'): 1,
  (7, '\xbd'): 1,
  (7, '\xbe'): 1,
  (7, '\xbf'): 1,
  (7, '\xc0'): 1,
  (7, '\xc1'): 1,
  (7, '\xc2'): 1,
  (7, '\xc3'): 1,
  (7, '\xc4'): 1,
  (7, '\xc5'): 1,
  (7, '\xc6'): 1,
  (7, '\xc7'): 1,
  (7, '\xc8'): 1,
  (7, '\xc9'): 1,
  (7, '\xca'): 1,
  (7, '\xcb'): 1,
  (7, '\xcc'): 1,
  (7, '\xcd'): 1,
  (7, '\xce'): 1,
  (7, '\xcf'): 1,
  (7, '\xd0'): 1,
  (7, '\xd1'): 1,
  (7, '\xd2'): 1,
  (7, '\xd3'): 1,
  (7, '\xd4'): 1,
  (7, '\xd5'): 1,
  (7, '\xd6'): 1,
  (7, '\xd7'): 1,
  (7, '\xd8'): 1,
  (7, '\xd9'): 1,
  (7, '\xda'): 1,
  (7, '\xdb'): 1,
  (7, '\xdc'): 1,
  (7, '\xdd'): 1,
  (7, '\xde'): 1,
  (7, '\xdf'): 1,
  (7, '\xe0'): 1,
  (7, '\xe1'): 1,
  (7, '\xe3'): 1,
  (7, '\xe4'): 1,
  (7, '\xe5'): 1,
  (7, '\xe6'): 1,
  (7, '\xe7'): 1,
  (7, '\xe8'): 1,
  (7, '\xe9'): 1,
  (7, '\xea'): 1,
  (7, '\xeb'): 1,
  (7, '\xec'): 1,
  (7, '\xed'): 1,
  (7, '\xee'): 1,
  (7, '\xef'): 1,
  (7, '\xf0'): 1,
  (7, '\xf1'): 1,
  (7, '\xf2'): 1,
  (7, '\xf3'): 1,
  (7, '\xf4'): 1,
  (7, '\xf5'): 1,
  (7, '\xf6'): 1,
  (7, '\xf7'): 1,
  (7, '\xf8'): 1,
  (7, '\xf9'): 1,
  (7, '\xfa'): 1,
  (7, '\xfb'): 1,
  (7, '\xfc'): 1,
  (7, '\xfd'): 1,
  (7, '\xfe'): 1,
  (7, '\xff'): 1,
  (9, '\x00'): 1,
  (9, '\x01'): 1,
  (9, '\x02'): 1,
  (9, '\x03'): 1,
  (9, '\x04'): 1,
  (9, '\x05'): 1,
  (9, '\x06'): 1,
  (9, '\x07'): 1,
  (9, '\x08'): 1,
  (9, '\x0b'): 1,
  (9, '\x0e'): 1,
  (9, '\x0f'): 1,
  (9, '\x10'): 1,
  (9, '\x11'): 1,
  (9, '\x12'): 1,
  (9, '\x13'): 1,
  (9, '\x14'): 1,
  (9, '\x15'): 1,
  (9, '\x16'): 1,
  (9, '\x17'): 1,
  (9, '\x18'): 1,
  (9, '\x19'): 1,
  (9, '\x1a'): 1,
  (9, '\x1b'): 1,
  (9, '\x1c'): 1,
  (9, '\x1d'): 1,
  (9, '\x1e'): 1,
  (9, '\x1f'): 1,
  (9, '!'): 1,
  (9, '"'): 1,
  (9, '$'): 1,
  (9, '%'): 1,
  (9, '&'): 1,
  (9, "'"): 1,
  (9, '*'): 1,
  (9, '+'): 1,
  (9, '-'): 1,
  (9, '.'): 1,
  (9, '/'): 1,
  (9, '0'): 36,
  (9, '1'): 36,
  (9, '2'): 36,
  (9, '3'): 36,
  (9, '4'): 36,
  (9, '5'): 36,
  (9, '6'): 36,
  (9, '7'): 36,
  (9, '8'): 36,
  (9, '9'): 36,
  (9, ':'): 1,
  (9, ';'): 1,
  (9, '<'): 1,
  (9, '='): 1,
  (9, '>'): 1,
  (9, '?'): 1,
  (9, '@'): 1,
  (9, 'A'): 1,
  (9, 'B'): 1,
  (9, 'C'): 1,
  (9, 'D'): 1,
  (9, 'E'): 1,
  (9, 'F'): 1,
  (9, 'G'): 1,
  (9, 'H'): 1,
  (9, 'I'): 1,
  (9, 'J'): 1,
  (9, 'K'): 1,
  (9, 'L'): 1,
  (9, 'M'): 1,
  (9, 'N'): 1,
  (9, 'O'): 1,
  (9, 'P'): 1,
  (9, 'Q'): 1,
  (9, 'R'): 1,
  (9, 'S'): 1,
  (9, 'T'): 1,
  (9, 'U'): 1,
  (9, 'V'): 1,
  (9, 'W'): 1,
  (9, 'X'): 1,
  (9, 'Y'): 1,
  (9, 'Z'): 1,
  (9, '['): 1,
  (9, '\\'): 1,
  (9, ']'): 1,
  (9, '^'): 1,
  (9, '_'): 1,
  (9, '`'): 1,
  (9, 'a'): 1,
  (9, 'b'): 1,
  (9, 'c'): 1,
  (9, 'd'): 1,
  (9, 'e'): 1,
  (9, 'f'): 1,
  (9, 'g'): 1,
  (9, 'h'): 1,
  (9, 'i'): 1,
  (9, 'j'): 1,
  (9, 'k'): 1,
  (9, 'l'): 1,
  (9, 'm'): 1,
  (9, 'n'): 1,
  (9, 'o'): 1,
  (9, 'p'): 1,
  (9, 'q'): 1,
  (9, 'r'): 1,
  (9, 's'): 1,
  (9, 't'): 1,
  (9, 'u'): 1,
  (9, 'v'): 1,
  (9, 'w'): 1,
  (9, 'x'): 1,
  (9, 'y'): 1,
  (9, 'z'): 1,
  (9, '{'): 1,
  (9, '|'): 1,
  (9, '}'): 1,
  (9, '~'): 1,
  (9, '\x7f'): 1,
  (9, '\x80'): 1,
  (9, '\x81'): 1,
  (9, '\x82'): 1,
  (9, '\x83'): 1,
  (9, '\x84'): 1,
  (9, '\x85'): 1,
  (9, '\x86'): 1,
  (9, '\x87'): 1,
  (9, '\x88'): 1,
  (9, '\x89'): 1,
  (9, '\x8a'): 1,
  (9, '\x8b'): 1,
  (9, '\x8c'): 1,
  (9, '\x8d'): 1,
  (9, '\x8e'): 1,
  (9, '\x8f'): 1,
  (9, '\x90'): 1,
  (9, '\x91'): 1,
  (9, '\x92'): 1,
  (9, '\x93'): 1,
  (9, '\x94'): 1,
  (9, '\x95'): 1,
  (9, '\x96'): 1,
  (9, '\x97'): 1,
  (9, '\x98'): 1,
  (9, '\x99'): 1,
  (9, '\x9a'): 1,
  (9, '\x9b'): 1,
  (9, '\x9c'): 1,
  (9, '\x9d'): 1,
  (9, '\x9e'): 1,
  (9, '\xa0'): 1,
  (9, '\xa1'): 1,
  (9, '\xa2'): 1,
  (9, '\xa3'): 1,
  (9, '\xa4'): 1,
  (9, '\xa5'): 1,
  (9, '\xa6'): 1,
  (9, '\xa7'): 1,
  (9, '\xa8'): 1,
  (9, '\xa9'): 1,
  (9, '\xac'): 1,
  (9, '\xad'): 1,
  (9, '\xae'): 1,
  (9, '\xaf'): 1,
  (9, '\xb0'): 1,
  (9, '\xb1'): 1,
  (9, '\xb2'): 1,
  (9, '\xb3'): 1,
  (9, '\xb4'): 1,
  (9, '\xb5'): 1,
  (9, '\xb6'): 1,
  (9, '\xb7'): 1,
  (9, '\xb8'): 1,
  (9, '\xb9'): 1,
  (9, '\xba'): 1,
  (9, '\xbb'): 1,
  (9, '\xbc'): 1,
  (9, '\xbd'): 1,
  (9, '\xbe'): 1,
  (9, '\xbf'): 1,
  (9, '\xc0'): 1,
  (9, '\xc1'): 1,
  (9, '\xc2'): 1,
  (9, '\xc3'): 1,
  (9, '\xc4'): 1,
  (9, '\xc5'): 1,
  (9, '\xc6'): 1,
  (9, '\xc7'): 1,
  (9, '\xc8'): 1,
  (9, '\xc9'): 1,
  (9, '\xca'): 1,
  (9, '\xcb'): 1,
  (9, '\xcc'): 1,
  (9, '\xcd'): 1,
  (9, '\xce'): 1,
  (9, '\xcf'): 1,
  (9, '\xd0'): 1,
  (9, '\xd1'): 1,
  (9, '\xd2'): 1,
  (9, '\xd3'): 1,
  (9, '\xd4'): 1,
  (9, '\xd5'): 1,
  (9, '\xd6'): 1,
  (9, '\xd7'): 1,
  (9, '\xd8'): 1,
  (9, '\xd9'): 1,
  (9, '\xda'): 1,
  (9, '\xdb'): 1,
  (9, '\xdc'): 1,
  (9, '\xdd'): 1,
  (9, '\xde'): 1,
  (9, '\xdf'): 1,
  (9, '\xe0'): 1,
  (9, '\xe1'): 1,
  (9, '\xe3'): 1,
  (9, '\xe4'): 1,
  (9, '\xe5'): 1,
  (9, '\xe6'): 1,
  (9, '\xe7'): 1,
  (9, '\xe8'): 1,
  (9, '\xe9'): 1,
  (9, '\xea'): 1,
  (9, '\xeb'): 1,
  (9, '\xec'): 1,
  (9, '\xed'): 1,
  (9, '\xee'): 1,
  (9, '\xef'): 1,
  (9, '\xf0'): 1,
  (9, '\xf1'): 1,
  (9, '\xf2'): 1,
  (9, '\xf3'): 1,
  (9, '\xf4'): 1,
  (9, '\xf5'): 1,
  (9, '\xf6'): 1,
  (9, '\xf7'): 1,
  (9, '\xf8'): 1,
  (9, '\xf9'): 1,
  (9, '\xfa'): 1,
  (9, '\xfb'): 1,
  (9, '\xfc'): 1,
  (9, '\xfd'): 1,
  (9, '\xfe'): 1,
  (9, '\xff'): 1,
  (11, '\x00'): 1,
  (11, '\x01'): 1,
  (11, '\x02'): 1,
  (11, '\x03'): 1,
  (11, '\x04'): 1,
  (11, '\x05'): 1,
  (11, '\x06'): 1,
  (11, '\x07'): 1,
  (11, '\x08'): 1,
  (11, '\x0b'): 1,
  (11, '\x0e'): 1,
  (11, '\x0f'): 1,
  (11, '\x10'): 1,
  (11, '\x11'): 1,
  (11, '\x12'): 1,
  (11, '\x13'): 1,
  (11, '\x14'): 1,
  (11, '\x15'): 1,
  (11, '\x16'): 1,
  (11, '\x17'): 1,
  (11, '\x18'): 1,
  (11, '\x19'): 1,
  (11, '\x1a'): 1,
  (11, '\x1b'): 1,
  (11, '\x1c'): 1,
  (11, '\x1d'): 1,
  (11, '\x1e'): 1,
  (11, '\x1f'): 1,
  (11, '!'): 1,
  (11, '"'): 1,
  (11, '$'): 1,
  (11, '%'): 1,
  (11, '&'): 1,
  (11, "'"): 1,
  (11, '*'): 1,
  (11, '+'): 1,
  (11, '-'): 1,
  (11, '.'): 1,
  (11, '/'): 1,
  (11, '0'): 1,
  (11, '1'): 1,
  (11, '2'): 1,
  (11, '3'): 1,
  (11, '4'): 1,
  (11, '5'): 1,
  (11, '6'): 1,
  (11, '7'): 1,
  (11, '8'): 1,
  (11, '9'): 1,
  (11, ':'): 1,
  (11, ';'): 1,
  (11, '<'): 1,
  (11, '='): 1,
  (11, '>'): 1,
  (11, '?'): 1,
  (11, '@'): 1,
  (11, 'A'): 1,
  (11, 'B'): 1,
  (11, 'C'): 1,
  (11, 'D'): 1,
  (11, 'E'): 1,
  (11, 'F'): 1,
  (11, 'G'): 1,
  (11, 'H'): 1,
  (11, 'I'): 1,
  (11, 'J'): 1,
  (11, 'K'): 1,
  (11, 'L'): 1,
  (11, 'M'): 1,
  (11, 'N'): 1,
  (11, 'O'): 1,
  (11, 'P'): 1,
  (11, 'Q'): 1,
  (11, 'R'): 1,
  (11, 'S'): 1,
  (11, 'T'): 1,
  (11, 'U'): 1,
  (11, 'V'): 1,
  (11, 'W'): 1,
  (11, 'X'): 1,
  (11, 'Y'): 1,
  (11, 'Z'): 1,
  (11, '['): 1,
  (11, '\\'): 1,
  (11, ']'): 1,
  (11, '^'): 1,
  (11, '_'): 1,
  (11, '`'): 1,
  (11, 'a'): 1,
  (11, 'b'): 1,
  (11, 'c'): 1,
  (11, 'd'): 1,
  (11, 'e'): 1,
  (11, 'f'): 1,
  (11, 'g'): 1,
  (11, 'h'): 1,
  (11, 'i'): 1,
  (11, 'j'): 1,
  (11, 'k'): 1,
  (11, 'l'): 1,
  (11, 'm'): 1,
  (11, 'n'): 1,
  (11, 'o'): 1,
  (11, 'p'): 1,
  (11, 'q'): 1,
  (11, 'r'): 1,
  (11, 's'): 1,
  (11, 't'): 1,
  (11, 'u'): 1,
  (11, 'v'): 1,
  (11, 'w'): 1,
  (11, 'x'): 1,
  (11, 'y'): 1,
  (11, 'z'): 1,
  (11, '{'): 1,
  (11, '|'): 1,
  (11, '}'): 1,
  (11, '~'): 1,
  (11, '\x7f'): 1,
  (11, '\x80'): 1,
  (11, '\x81'): 1,
  (11, '\x82'): 1,
  (11, '\x83'): 1,
  (11, '\x84'): 1,
  (11, '\x85'): 1,
  (11, '\x86'): 1,
  (11, '\x87'): 1,
  (11, '\x88'): 1,
  (11, '\x89'): 1,
  (11, '\x8a'): 1,
  (11, '\x8b'): 1,
  (11, '\x8c'): 1,
  (11, '\x8d'): 1,
  (11, '\x8e'): 1,
  (11, '\x8f'): 1,
  (11, '\x90'): 1,
  (11, '\x91'): 1,
  (11, '\x92'): 1,
  (11, '\x93'): 1,
  (11, '\x94'): 1,
  (11, '\x95'): 1,
  (11, '\x96'): 1,
  (11, '\x97'): 1,
  (11, '\x98'): 1,
  (11, '\x99'): 1,
  (11, '\x9a'): 1,
  (11, '\x9b'): 29,
  (11, '\x9c'): 1,
  (11, '\x9d'): 1,
  (11, '\x9e'): 1,
  (11, '\xa0'): 1,
  (11, '\xa1'): 1,
  (11, '\xa2'): 1,
  (11, '\xa3'): 1,
  (11, '\xa4'): 1,
  (11, '\xa5'): 1,
  (11, '\xa6'): 1,
  (11, '\xa7'): 1,
  (11, '\xa8'): 1,
  (11, '\xa9'): 1,
  (11, '\xac'): 1,
  (11, '\xad'): 1,
  (11, '\xae'): 1,
  (11, '\xaf'): 1,
  (11, '\xb0'): 1,
  (11, '\xb1'): 1,
  (11, '\xb2'): 1,
  (11, '\xb3'): 1,
  (11, '\xb4'): 1,
  (11, '\xb5'): 1,
  (11, '\xb6'): 1,
  (11, '\xb7'): 1,
  (11, '\xb8'): 1,
  (11, '\xb9'): 1,
  (11, '\xba'): 1,
  (11, '\xbb'): 30,
  (11, '\xbc'): 31,
  (11, '\xbd'): 1,
  (11, '\xbe'): 1,
  (11, '\xbf'): 1,
  (11, '\xc0'): 1,
  (11, '\xc1'): 1,
  (11, '\xc2'): 1,
  (11, '\xc3'): 1,
  (11, '\xc4'): 1,
  (11, '\xc5'): 1,
  (11, '\xc6'): 1,
  (11, '\xc7'): 1,
  (11, '\xc8'): 1,
  (11, '\xc9'): 1,
  (11, '\xca'): 1,
  (11, '\xcb'): 1,
  (11, '\xcc'): 1,
  (11, '\xcd'): 1,
  (11, '\xce'): 1,
  (11, '\xcf'): 1,
  (11, '\xd0'): 1,
  (11, '\xd1'): 1,
  (11, '\xd2'): 1,
  (11, '\xd3'): 1,
  (11, '\xd4'): 1,
  (11, '\xd5'): 1,
  (11, '\xd6'): 1,
  (11, '\xd7'): 1,
  (11, '\xd8'): 1,
  (11, '\xd9'): 1,
  (11, '\xda'): 1,
  (11, '\xdb'): 1,
  (11, '\xdc'): 1,
  (11, '\xdd'): 1,
  (11, '\xde'): 1,
  (11, '\xdf'): 1,
  (11, '\xe0'): 1,
  (11, '\xe1'): 1,
  (11, '\xe3'): 1,
  (11, '\xe4'): 1,
  (11, '\xe5'): 1,
  (11, '\xe6'): 1,
  (11, '\xe7'): 1,
  (11, '\xe8'): 1,
  (11, '\xe9'): 1,
  (11, '\xea'): 1,
  (11, '\xeb'): 1,
  (11, '\xec'): 1,
  (11, '\xed'): 1,
  (11, '\xee'): 1,
  (11, '\xef'): 1,
  (11, '\xf0'): 1,
  (11, '\xf1'): 1,
  (11, '\xf2'): 1,
  (11, '\xf3'): 1,
  (11, '\xf4'): 1,
  (11, '\xf5'): 1,
  (11, '\xf6'): 1,
  (11, '\xf7'): 1,
  (11, '\xf8'): 1,
  (11, '\xf9'): 1,
  (11, '\xfa'): 1,
  (11, '\xfb'): 1,
  (11, '\xfc'): 1,
  (11, '\xfd'): 1,
  (11, '\xfe'): 1,
  (11, '\xff'): 1,
  (12, '\x80'): 14,
  (12, '\x86'): 16,
  (12, '\x89'): 13,
  (12, '\x9f'): 15,
  (13, '\x94'): 28,
  (14, '\x98'): 20,
  (14, '\x9c'): 21,
  (15, '\xaa'): 19,
  (15, '\xab'): 18,
  (16, '\xa6'): 17,
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
  (20, '\x9a'): 20,
  (20, '\x9b'): 20,
  (20, '\x9c'): 20,
  (20, '\x9d'): 20,
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
  (20, '\xe2'): 25,
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
  (21, '\x00'): 21,
  (21, '\x01'): 21,
  (21, '\x02'): 21,
  (21, '\x03'): 21,
  (21, '\x04'): 21,
  (21, '\x05'): 21,
  (21, '\x06'): 21,
  (21, '\x07'): 21,
  (21, '\x08'): 21,
  (21, '\t'): 21,
  (21, '\n'): 21,
  (21, '\x0b'): 21,
  (21, '\x0c'): 21,
  (21, '\r'): 21,
  (21, '\x0e'): 21,
  (21, '\x0f'): 21,
  (21, '\x10'): 21,
  (21, '\x11'): 21,
  (21, '\x12'): 21,
  (21, '\x13'): 21,
  (21, '\x14'): 21,
  (21, '\x15'): 21,
  (21, '\x16'): 21,
  (21, '\x17'): 21,
  (21, '\x18'): 21,
  (21, '\x19'): 21,
  (21, '\x1a'): 21,
  (21, '\x1b'): 21,
  (21, '\x1c'): 21,
  (21, '\x1d'): 21,
  (21, '\x1e'): 21,
  (21, '\x1f'): 21,
  (21, ' '): 21,
  (21, '!'): 21,
  (21, '"'): 21,
  (21, '#'): 21,
  (21, '$'): 21,
  (21, '%'): 21,
  (21, '&'): 21,
  (21, "'"): 21,
  (21, '('): 21,
  (21, ')'): 21,
  (21, '*'): 21,
  (21, '+'): 21,
  (21, ','): 21,
  (21, '-'): 21,
  (21, '.'): 21,
  (21, '/'): 21,
  (21, '0'): 21,
  (21, '1'): 21,
  (21, '2'): 21,
  (21, '3'): 21,
  (21, '4'): 21,
  (21, '5'): 21,
  (21, '6'): 21,
  (21, '7'): 21,
  (21, '8'): 21,
  (21, '9'): 21,
  (21, ':'): 21,
  (21, ';'): 21,
  (21, '<'): 21,
  (21, '='): 21,
  (21, '>'): 21,
  (21, '?'): 21,
  (21, '@'): 21,
  (21, 'A'): 21,
  (21, 'B'): 21,
  (21, 'C'): 21,
  (21, 'D'): 21,
  (21, 'E'): 21,
  (21, 'F'): 21,
  (21, 'G'): 21,
  (21, 'H'): 21,
  (21, 'I'): 21,
  (21, 'J'): 21,
  (21, 'K'): 21,
  (21, 'L'): 21,
  (21, 'M'): 21,
  (21, 'N'): 21,
  (21, 'O'): 21,
  (21, 'P'): 21,
  (21, 'Q'): 21,
  (21, 'R'): 21,
  (21, 'S'): 21,
  (21, 'T'): 21,
  (21, 'U'): 21,
  (21, 'V'): 21,
  (21, 'W'): 21,
  (21, 'X'): 21,
  (21, 'Y'): 21,
  (21, 'Z'): 21,
  (21, '['): 21,
  (21, '\\'): 21,
  (21, ']'): 21,
  (21, '^'): 21,
  (21, '_'): 21,
  (21, '`'): 21,
  (21, 'a'): 21,
  (21, 'b'): 21,
  (21, 'c'): 21,
  (21, 'd'): 21,
  (21, 'e'): 21,
  (21, 'f'): 21,
  (21, 'g'): 21,
  (21, 'h'): 21,
  (21, 'i'): 21,
  (21, 'j'): 21,
  (21, 'k'): 21,
  (21, 'l'): 21,
  (21, 'm'): 21,
  (21, 'n'): 21,
  (21, 'o'): 21,
  (21, 'p'): 21,
  (21, 'q'): 21,
  (21, 'r'): 21,
  (21, 's'): 21,
  (21, 't'): 21,
  (21, 'u'): 21,
  (21, 'v'): 21,
  (21, 'w'): 21,
  (21, 'x'): 21,
  (21, 'y'): 21,
  (21, 'z'): 21,
  (21, '{'): 21,
  (21, '|'): 21,
  (21, '}'): 21,
  (21, '~'): 21,
  (21, '\x7f'): 21,
  (21, '\x81'): 21,
  (21, '\x82'): 21,
  (21, '\x83'): 21,
  (21, '\x84'): 21,
  (21, '\x85'): 21,
  (21, '\x86'): 21,
  (21, '\x87'): 21,
  (21, '\x88'): 21,
  (21, '\x89'): 21,
  (21, '\x8a'): 21,
  (21, '\x8b'): 21,
  (21, '\x8c'): 21,
  (21, '\x8d'): 21,
  (21, '\x8e'): 21,
  (21, '\x8f'): 21,
  (21, '\x90'): 21,
  (21, '\x91'): 21,
  (21, '\x92'): 21,
  (21, '\x93'): 21,
  (21, '\x94'): 21,
  (21, '\x95'): 21,
  (21, '\x96'): 21,
  (21, '\x97'): 21,
  (21, '\x98'): 21,
  (21, '\x99'): 21,
  (21, '\x9a'): 21,
  (21, '\x9b'): 21,
  (21, '\x9c'): 21,
  (21, '\x9e'): 21,
  (21, '\x9f'): 21,
  (21, '\xa0'): 21,
  (21, '\xa1'): 21,
  (21, '\xa2'): 21,
  (21, '\xa3'): 21,
  (21, '\xa4'): 21,
  (21, '\xa5'): 21,
  (21, '\xa6'): 21,
  (21, '\xa7'): 21,
  (21, '\xa8'): 21,
  (21, '\xa9'): 21,
  (21, '\xaa'): 21,
  (21, '\xab'): 21,
  (21, '\xac'): 21,
  (21, '\xad'): 21,
  (21, '\xae'): 21,
  (21, '\xaf'): 21,
  (21, '\xb0'): 21,
  (21, '\xb1'): 21,
  (21, '\xb2'): 21,
  (21, '\xb3'): 21,
  (21, '\xb4'): 21,
  (21, '\xb5'): 21,
  (21, '\xb6'): 21,
  (21, '\xb7'): 21,
  (21, '\xb8'): 21,
  (21, '\xb9'): 21,
  (21, '\xba'): 21,
  (21, '\xbb'): 21,
  (21, '\xbc'): 21,
  (21, '\xbd'): 21,
  (21, '\xbe'): 21,
  (21, '\xbf'): 21,
  (21, '\xc0'): 21,
  (21, '\xc1'): 21,
  (21, '\xc2'): 21,
  (21, '\xc3'): 21,
  (21, '\xc4'): 21,
  (21, '\xc5'): 21,
  (21, '\xc6'): 21,
  (21, '\xc7'): 21,
  (21, '\xc8'): 21,
  (21, '\xc9'): 21,
  (21, '\xca'): 21,
  (21, '\xcb'): 21,
  (21, '\xcc'): 21,
  (21, '\xcd'): 21,
  (21, '\xce'): 21,
  (21, '\xcf'): 21,
  (21, '\xd0'): 21,
  (21, '\xd1'): 21,
  (21, '\xd2'): 21,
  (21, '\xd3'): 21,
  (21, '\xd4'): 21,
  (21, '\xd5'): 21,
  (21, '\xd6'): 21,
  (21, '\xd7'): 21,
  (21, '\xd8'): 21,
  (21, '\xd9'): 21,
  (21, '\xda'): 21,
  (21, '\xdb'): 21,
  (21, '\xdc'): 21,
  (21, '\xdd'): 21,
  (21, '\xde'): 21,
  (21, '\xdf'): 21,
  (21, '\xe0'): 21,
  (21, '\xe1'): 21,
  (21, '\xe2'): 22,
  (21, '\xe3'): 21,
  (21, '\xe4'): 21,
  (21, '\xe5'): 21,
  (21, '\xe6'): 21,
  (21, '\xe7'): 21,
  (21, '\xe8'): 21,
  (21, '\xe9'): 21,
  (21, '\xea'): 21,
  (21, '\xeb'): 21,
  (21, '\xec'): 21,
  (21, '\xed'): 21,
  (21, '\xee'): 21,
  (21, '\xef'): 21,
  (21, '\xf0'): 21,
  (21, '\xf1'): 21,
  (21, '\xf2'): 21,
  (21, '\xf3'): 21,
  (21, '\xf4'): 21,
  (21, '\xf5'): 21,
  (21, '\xf6'): 21,
  (21, '\xf7'): 21,
  (21, '\xf8'): 21,
  (21, '\xf9'): 21,
  (21, '\xfa'): 21,
  (21, '\xfb'): 21,
  (21, '\xfc'): 21,
  (21, '\xfd'): 21,
  (21, '\xfe'): 21,
  (21, '\xff'): 21,
  (22, '\x80'): 23,
  (23, '\x9d'): 24,
  (25, '\x80'): 26,
  (26, '\x99'): 27,
  (29, '\x00'): 34,
  (29, '\x01'): 34,
  (29, '\x02'): 34,
  (29, '\x03'): 34,
  (29, '\x04'): 34,
  (29, '\x05'): 34,
  (29, '\x06'): 34,
  (29, '\x07'): 34,
  (29, '\x08'): 34,
  (29, '\t'): 35,
  (29, '\n'): 35,
  (29, '\x0b'): 34,
  (29, '\x0c'): 35,
  (29, '\r'): 35,
  (29, '\x0e'): 34,
  (29, '\x0f'): 34,
  (29, '\x10'): 34,
  (29, '\x11'): 34,
  (29, '\x12'): 34,
  (29, '\x13'): 34,
  (29, '\x14'): 34,
  (29, '\x15'): 34,
  (29, '\x16'): 34,
  (29, '\x17'): 34,
  (29, '\x18'): 34,
  (29, '\x19'): 34,
  (29, '\x1a'): 34,
  (29, '\x1b'): 34,
  (29, '\x1c'): 34,
  (29, '\x1d'): 34,
  (29, '\x1e'): 34,
  (29, '\x1f'): 34,
  (29, ' '): 35,
  (29, '!'): 34,
  (29, '"'): 34,
  (29, '#'): 35,
  (29, '$'): 34,
  (29, '%'): 34,
  (29, '&'): 34,
  (29, "'"): 34,
  (29, '('): 35,
  (29, ')'): 35,
  (29, '*'): 34,
  (29, '+'): 34,
  (29, ','): 35,
  (29, '-'): 34,
  (29, '.'): 34,
  (29, '/'): 34,
  (29, '0'): 34,
  (29, '1'): 34,
  (29, '2'): 34,
  (29, '3'): 34,
  (29, '4'): 34,
  (29, '5'): 34,
  (29, '6'): 34,
  (29, '7'): 34,
  (29, '8'): 34,
  (29, '9'): 34,
  (29, ':'): 34,
  (29, ';'): 34,
  (29, '<'): 34,
  (29, '='): 34,
  (29, '>'): 34,
  (29, '?'): 34,
  (29, '@'): 34,
  (29, 'A'): 34,
  (29, 'B'): 34,
  (29, 'C'): 34,
  (29, 'D'): 34,
  (29, 'E'): 34,
  (29, 'F'): 34,
  (29, 'G'): 34,
  (29, 'H'): 34,
  (29, 'I'): 34,
  (29, 'J'): 34,
  (29, 'K'): 34,
  (29, 'L'): 34,
  (29, 'M'): 34,
  (29, 'N'): 34,
  (29, 'O'): 34,
  (29, 'P'): 34,
  (29, 'Q'): 34,
  (29, 'R'): 34,
  (29, 'S'): 34,
  (29, 'T'): 34,
  (29, 'U'): 34,
  (29, 'V'): 34,
  (29, 'W'): 34,
  (29, 'X'): 34,
  (29, 'Y'): 34,
  (29, 'Z'): 34,
  (29, '['): 34,
  (29, '\\'): 34,
  (29, ']'): 34,
  (29, '^'): 34,
  (29, '_'): 34,
  (29, '`'): 34,
  (29, 'a'): 34,
  (29, 'b'): 34,
  (29, 'c'): 34,
  (29, 'd'): 34,
  (29, 'e'): 34,
  (29, 'f'): 34,
  (29, 'g'): 34,
  (29, 'h'): 34,
  (29, 'i'): 34,
  (29, 'j'): 34,
  (29, 'k'): 34,
  (29, 'l'): 34,
  (29, 'm'): 34,
  (29, 'n'): 34,
  (29, 'o'): 34,
  (29, 'p'): 34,
  (29, 'q'): 34,
  (29, 'r'): 34,
  (29, 's'): 34,
  (29, 't'): 34,
  (29, 'u'): 34,
  (29, 'v'): 34,
  (29, 'w'): 34,
  (29, 'x'): 34,
  (29, 'y'): 34,
  (29, 'z'): 34,
  (29, '{'): 34,
  (29, '|'): 34,
  (29, '}'): 34,
  (29, '~'): 34,
  (29, '\x7f'): 34,
  (29, '\x80'): 34,
  (29, '\x81'): 34,
  (29, '\x82'): 34,
  (29, '\x83'): 34,
  (29, '\x84'): 34,
  (29, '\x85'): 34,
  (29, '\x86'): 34,
  (29, '\x87'): 34,
  (29, '\x88'): 34,
  (29, '\x89'): 34,
  (29, '\x8a'): 34,
  (29, '\x8b'): 34,
  (29, '\x8c'): 34,
  (29, '\x8d'): 34,
  (29, '\x8e'): 34,
  (29, '\x8f'): 34,
  (29, '\x90'): 34,
  (29, '\x91'): 34,
  (29, '\x92'): 34,
  (29, '\x93'): 34,
  (29, '\x94'): 34,
  (29, '\x95'): 34,
  (29, '\x96'): 34,
  (29, '\x97'): 34,
  (29, '\x98'): 34,
  (29, '\x99'): 34,
  (29, '\x9a'): 34,
  (29, '\x9b'): 34,
  (29, '\x9c'): 34,
  (29, '\x9d'): 34,
  (29, '\x9e'): 34,
  (29, '\x9f'): 35,
  (29, '\xa0'): 34,
  (29, '\xa1'): 34,
  (29, '\xa2'): 34,
  (29, '\xa3'): 34,
  (29, '\xa4'): 34,
  (29, '\xa5'): 34,
  (29, '\xa6'): 34,
  (29, '\xa7'): 34,
  (29, '\xa8'): 34,
  (29, '\xa9'): 34,
  (29, '\xaa'): 35,
  (29, '\xab'): 35,
  (29, '\xac'): 34,
  (29, '\xad'): 34,
  (29, '\xae'): 34,
  (29, '\xaf'): 34,
  (29, '\xb0'): 34,
  (29, '\xb1'): 34,
  (29, '\xb2'): 34,
  (29, '\xb3'): 34,
  (29, '\xb4'): 34,
  (29, '\xb5'): 34,
  (29, '\xb6'): 34,
  (29, '\xb7'): 34,
  (29, '\xb8'): 34,
  (29, '\xb9'): 34,
  (29, '\xba'): 34,
  (29, '\xbb'): 34,
  (29, '\xbc'): 34,
  (29, '\xbd'): 34,
  (29, '\xbe'): 34,
  (29, '\xbf'): 34,
  (29, '\xc0'): 34,
  (29, '\xc1'): 34,
  (29, '\xc2'): 34,
  (29, '\xc3'): 34,
  (29, '\xc4'): 34,
  (29, '\xc5'): 34,
  (29, '\xc6'): 34,
  (29, '\xc7'): 34,
  (29, '\xc8'): 34,
  (29, '\xc9'): 34,
  (29, '\xca'): 34,
  (29, '\xcb'): 34,
  (29, '\xcc'): 34,
  (29, '\xcd'): 34,
  (29, '\xce'): 34,
  (29, '\xcf'): 34,
  (29, '\xd0'): 34,
  (29, '\xd1'): 34,
  (29, '\xd2'): 34,
  (29, '\xd3'): 34,
  (29, '\xd4'): 34,
  (29, '\xd5'): 34,
  (29, '\xd6'): 34,
  (29, '\xd7'): 34,
  (29, '\xd8'): 34,
  (29, '\xd9'): 34,
  (29, '\xda'): 34,
  (29, '\xdb'): 34,
  (29, '\xdc'): 34,
  (29, '\xdd'): 34,
  (29, '\xde'): 34,
  (29, '\xdf'): 34,
  (29, '\xe0'): 34,
  (29, '\xe1'): 34,
  (29, '\xe2'): 35,
  (29, '\xe3'): 34,
  (29, '\xe4'): 34,
  (29, '\xe5'): 34,
  (29, '\xe6'): 34,
  (29, '\xe7'): 34,
  (29, '\xe8'): 34,
  (29, '\xe9'): 34,
  (29, '\xea'): 34,
  (29, '\xeb'): 34,
  (29, '\xec'): 34,
  (29, '\xed'): 34,
  (29, '\xee'): 34,
  (29, '\xef'): 34,
  (29, '\xf0'): 34,
  (29, '\xf1'): 34,
  (29, '\xf2'): 34,
  (29, '\xf3'): 34,
  (29, '\xf4'): 34,
  (29, '\xf5'): 34,
  (29, '\xf6'): 34,
  (29, '\xf7'): 34,
  (29, '\xf8'): 34,
  (29, '\xf9'): 34,
  (29, '\xfa'): 34,
  (29, '\xfb'): 34,
  (29, '\xfc'): 34,
  (29, '\xfd'): 34,
  (29, '\xfe'): 34,
  (29, '\xff'): 34,
  (30, '\x00'): 32,
  (30, '\x01'): 32,
  (30, '\x02'): 32,
  (30, '\x03'): 32,
  (30, '\x04'): 32,
  (30, '\x05'): 32,
  (30, '\x06'): 32,
  (30, '\x07'): 32,
  (30, '\x08'): 32,
  (30, '\t'): 33,
  (30, '\n'): 33,
  (30, '\x0b'): 32,
  (30, '\x0c'): 33,
  (30, '\r'): 33,
  (30, '\x0e'): 32,
  (30, '\x0f'): 32,
  (30, '\x10'): 32,
  (30, '\x11'): 32,
  (30, '\x12'): 32,
  (30, '\x13'): 32,
  (30, '\x14'): 32,
  (30, '\x15'): 32,
  (30, '\x16'): 32,
  (30, '\x17'): 32,
  (30, '\x18'): 32,
  (30, '\x19'): 32,
  (30, '\x1a'): 32,
  (30, '\x1b'): 32,
  (30, '\x1c'): 32,
  (30, '\x1d'): 32,
  (30, '\x1e'): 32,
  (30, '\x1f'): 32,
  (30, ' '): 33,
  (30, '!'): 32,
  (30, '"'): 32,
  (30, '#'): 33,
  (30, '$'): 32,
  (30, '%'): 32,
  (30, '&'): 32,
  (30, "'"): 32,
  (30, '('): 33,
  (30, ')'): 33,
  (30, '*'): 32,
  (30, '+'): 32,
  (30, ','): 33,
  (30, '-'): 32,
  (30, '.'): 32,
  (30, '/'): 32,
  (30, '0'): 32,
  (30, '1'): 32,
  (30, '2'): 32,
  (30, '3'): 32,
  (30, '4'): 32,
  (30, '5'): 32,
  (30, '6'): 32,
  (30, '7'): 32,
  (30, '8'): 32,
  (30, '9'): 32,
  (30, ':'): 32,
  (30, ';'): 32,
  (30, '<'): 32,
  (30, '='): 32,
  (30, '>'): 32,
  (30, '?'): 32,
  (30, '@'): 32,
  (30, 'A'): 32,
  (30, 'B'): 32,
  (30, 'C'): 32,
  (30, 'D'): 32,
  (30, 'E'): 32,
  (30, 'F'): 32,
  (30, 'G'): 32,
  (30, 'H'): 32,
  (30, 'I'): 32,
  (30, 'J'): 32,
  (30, 'K'): 32,
  (30, 'L'): 32,
  (30, 'M'): 32,
  (30, 'N'): 32,
  (30, 'O'): 32,
  (30, 'P'): 32,
  (30, 'Q'): 32,
  (30, 'R'): 32,
  (30, 'S'): 32,
  (30, 'T'): 32,
  (30, 'U'): 32,
  (30, 'V'): 32,
  (30, 'W'): 32,
  (30, 'X'): 32,
  (30, 'Y'): 32,
  (30, 'Z'): 32,
  (30, '['): 32,
  (30, '\\'): 32,
  (30, ']'): 32,
  (30, '^'): 32,
  (30, '_'): 32,
  (30, '`'): 32,
  (30, 'a'): 32,
  (30, 'b'): 32,
  (30, 'c'): 32,
  (30, 'd'): 32,
  (30, 'e'): 32,
  (30, 'f'): 32,
  (30, 'g'): 32,
  (30, 'h'): 32,
  (30, 'i'): 32,
  (30, 'j'): 32,
  (30, 'k'): 32,
  (30, 'l'): 32,
  (30, 'm'): 32,
  (30, 'n'): 32,
  (30, 'o'): 32,
  (30, 'p'): 32,
  (30, 'q'): 32,
  (30, 'r'): 32,
  (30, 's'): 32,
  (30, 't'): 32,
  (30, 'u'): 32,
  (30, 'v'): 32,
  (30, 'w'): 32,
  (30, 'x'): 32,
  (30, 'y'): 32,
  (30, 'z'): 32,
  (30, '{'): 32,
  (30, '|'): 32,
  (30, '}'): 32,
  (30, '~'): 32,
  (30, '\x7f'): 32,
  (30, '\x80'): 32,
  (30, '\x81'): 32,
  (30, '\x82'): 32,
  (30, '\x83'): 32,
  (30, '\x84'): 32,
  (30, '\x85'): 32,
  (30, '\x86'): 32,
  (30, '\x87'): 32,
  (30, '\x88'): 32,
  (30, '\x89'): 32,
  (30, '\x8a'): 32,
  (30, '\x8b'): 32,
  (30, '\x8c'): 32,
  (30, '\x8d'): 32,
  (30, '\x8e'): 32,
  (30, '\x8f'): 32,
  (30, '\x90'): 32,
  (30, '\x91'): 32,
  (30, '\x92'): 32,
  (30, '\x93'): 32,
  (30, '\x94'): 32,
  (30, '\x95'): 32,
  (30, '\x96'): 32,
  (30, '\x97'): 32,
  (30, '\x98'): 32,
  (30, '\x99'): 32,
  (30, '\x9a'): 32,
  (30, '\x9b'): 32,
  (30, '\x9c'): 32,
  (30, '\x9d'): 32,
  (30, '\x9e'): 32,
  (30, '\x9f'): 33,
  (30, '\xa0'): 32,
  (30, '\xa1'): 32,
  (30, '\xa2'): 32,
  (30, '\xa3'): 32,
  (30, '\xa4'): 32,
  (30, '\xa5'): 32,
  (30, '\xa6'): 32,
  (30, '\xa7'): 32,
  (30, '\xa8'): 32,
  (30, '\xa9'): 32,
  (30, '\xaa'): 33,
  (30, '\xab'): 33,
  (30, '\xac'): 32,
  (30, '\xad'): 32,
  (30, '\xae'): 32,
  (30, '\xaf'): 32,
  (30, '\xb0'): 32,
  (30, '\xb1'): 32,
  (30, '\xb2'): 32,
  (30, '\xb3'): 32,
  (30, '\xb4'): 32,
  (30, '\xb5'): 32,
  (30, '\xb6'): 32,
  (30, '\xb7'): 32,
  (30, '\xb8'): 32,
  (30, '\xb9'): 32,
  (30, '\xba'): 32,
  (30, '\xbb'): 32,
  (30, '\xbc'): 32,
  (30, '\xbd'): 32,
  (30, '\xbe'): 32,
  (30, '\xbf'): 32,
  (30, '\xc0'): 32,
  (30, '\xc1'): 32,
  (30, '\xc2'): 32,
  (30, '\xc3'): 32,
  (30, '\xc4'): 32,
  (30, '\xc5'): 32,
  (30, '\xc6'): 32,
  (30, '\xc7'): 32,
  (30, '\xc8'): 32,
  (30, '\xc9'): 32,
  (30, '\xca'): 32,
  (30, '\xcb'): 32,
  (30, '\xcc'): 32,
  (30, '\xcd'): 32,
  (30, '\xce'): 32,
  (30, '\xcf'): 32,
  (30, '\xd0'): 32,
  (30, '\xd1'): 32,
  (30, '\xd2'): 32,
  (30, '\xd3'): 32,
  (30, '\xd4'): 32,
  (30, '\xd5'): 32,
  (30, '\xd6'): 32,
  (30, '\xd7'): 32,
  (30, '\xd8'): 32,
  (30, '\xd9'): 32,
  (30, '\xda'): 32,
  (30, '\xdb'): 32,
  (30, '\xdc'): 32,
  (30, '\xdd'): 32,
  (30, '\xde'): 32,
  (30, '\xdf'): 32,
  (30, '\xe0'): 32,
  (30, '\xe1'): 32,
  (30, '\xe2'): 33,
  (30, '\xe3'): 32,
  (30, '\xe4'): 32,
  (30, '\xe5'): 32,
  (30, '\xe6'): 32,
  (30, '\xe7'): 32,
  (30, '\xe8'): 32,
  (30, '\xe9'): 32,
  (30, '\xea'): 32,
  (30, '\xeb'): 32,
  (30, '\xec'): 32,
  (30, '\xed'): 32,
  (30, '\xee'): 32,
  (30, '\xef'): 32,
  (30, '\xf0'): 32,
  (30, '\xf1'): 32,
  (30, '\xf2'): 32,
  (30, '\xf3'): 32,
  (30, '\xf4'): 32,
  (30, '\xf5'): 32,
  (30, '\xf6'): 32,
  (30, '\xf7'): 32,
  (30, '\xf8'): 32,
  (30, '\xf9'): 32,
  (30, '\xfa'): 32,
  (30, '\xfb'): 32,
  (30, '\xfc'): 32,
  (30, '\xfd'): 32,
  (30, '\xfe'): 32,
  (30, '\xff'): 32,
  (31, '\x00'): 1,
  (31, '\x01'): 1,
  (31, '\x02'): 1,
  (31, '\x03'): 1,
  (31, '\x04'): 1,
  (31, '\x05'): 1,
  (31, '\x06'): 1,
  (31, '\x07'): 1,
  (31, '\x08'): 1,
  (31, '\x0b'): 1,
  (31, '\x0e'): 1,
  (31, '\x0f'): 1,
  (31, '\x10'): 1,
  (31, '\x11'): 1,
  (31, '\x12'): 1,
  (31, '\x13'): 1,
  (31, '\x14'): 1,
  (31, '\x15'): 1,
  (31, '\x16'): 1,
  (31, '\x17'): 1,
  (31, '\x18'): 1,
  (31, '\x19'): 1,
  (31, '\x1a'): 1,
  (31, '\x1b'): 1,
  (31, '\x1c'): 1,
  (31, '\x1d'): 1,
  (31, '\x1e'): 1,
  (31, '\x1f'): 1,
  (31, '!'): 1,
  (31, '"'): 1,
  (31, '$'): 1,
  (31, '%'): 1,
  (31, '&'): 1,
  (31, "'"): 1,
  (31, '*'): 1,
  (31, '+'): 1,
  (31, '-'): 1,
  (31, '.'): 1,
  (31, '/'): 1,
  (31, '0'): 1,
  (31, '1'): 1,
  (31, '2'): 1,
  (31, '3'): 1,
  (31, '4'): 1,
  (31, '5'): 1,
  (31, '6'): 1,
  (31, '7'): 1,
  (31, '8'): 1,
  (31, '9'): 1,
  (31, ':'): 1,
  (31, ';'): 1,
  (31, '<'): 1,
  (31, '='): 1,
  (31, '>'): 1,
  (31, '?'): 1,
  (31, '@'): 1,
  (31, 'A'): 1,
  (31, 'B'): 1,
  (31, 'C'): 1,
  (31, 'D'): 1,
  (31, 'E'): 1,
  (31, 'F'): 1,
  (31, 'G'): 1,
  (31, 'H'): 1,
  (31, 'I'): 1,
  (31, 'J'): 1,
  (31, 'K'): 1,
  (31, 'L'): 1,
  (31, 'M'): 1,
  (31, 'N'): 1,
  (31, 'O'): 1,
  (31, 'P'): 1,
  (31, 'Q'): 1,
  (31, 'R'): 1,
  (31, 'S'): 1,
  (31, 'T'): 1,
  (31, 'U'): 1,
  (31, 'V'): 1,
  (31, 'W'): 1,
  (31, 'X'): 1,
  (31, 'Y'): 1,
  (31, 'Z'): 1,
  (31, '['): 1,
  (31, '\\'): 1,
  (31, ']'): 1,
  (31, '^'): 1,
  (31, '_'): 1,
  (31, '`'): 1,
  (31, 'a'): 1,
  (31, 'b'): 1,
  (31, 'c'): 1,
  (31, 'd'): 1,
  (31, 'e'): 1,
  (31, 'f'): 1,
  (31, 'g'): 1,
  (31, 'h'): 1,
  (31, 'i'): 1,
  (31, 'j'): 1,
  (31, 'k'): 1,
  (31, 'l'): 1,
  (31, 'm'): 1,
  (31, 'n'): 1,
  (31, 'o'): 1,
  (31, 'p'): 1,
  (31, 'q'): 1,
  (31, 'r'): 1,
  (31, 's'): 1,
  (31, 't'): 1,
  (31, 'u'): 1,
  (31, 'v'): 1,
  (31, 'w'): 1,
  (31, 'x'): 1,
  (31, 'y'): 1,
  (31, 'z'): 1,
  (31, '{'): 1,
  (31, '|'): 1,
  (31, '}'): 1,
  (31, '~'): 1,
  (31, '\x7f'): 1,
  (31, '\x80'): 1,
  (31, '\x81'): 1,
  (31, '\x82'): 1,
  (31, '\x83'): 1,
  (31, '\x84'): 1,
  (31, '\x85'): 1,
  (31, '\x86'): 1,
  (31, '\x87'): 1,
  (31, '\x88'): 1,
  (31, '\x89'): 1,
  (31, '\x8a'): 1,
  (31, '\x8b'): 1,
  (31, '\x8c'): 1,
  (31, '\x8d'): 1,
  (31, '\x8e'): 1,
  (31, '\x8f'): 1,
  (31, '\x90'): 1,
  (31, '\x91'): 1,
  (31, '\x92'): 1,
  (31, '\x93'): 1,
  (31, '\x94'): 1,
  (31, '\x95'): 1,
  (31, '\x96'): 1,
  (31, '\x97'): 1,
  (31, '\x98'): 1,
  (31, '\x99'): 1,
  (31, '\x9a'): 1,
  (31, '\x9b'): 1,
  (31, '\x9c'): 1,
  (31, '\x9d'): 1,
  (31, '\x9e'): 1,
  (31, '\xa0'): 1,
  (31, '\xa1'): 1,
  (31, '\xa2'): 1,
  (31, '\xa3'): 1,
  (31, '\xa4'): 1,
  (31, '\xa5'): 1,
  (31, '\xa6'): 1,
  (31, '\xa7'): 1,
  (31, '\xa8'): 1,
  (31, '\xa9'): 1,
  (31, '\xac'): 1,
  (31, '\xad'): 1,
  (31, '\xae'): 1,
  (31, '\xaf'): 1,
  (31, '\xb0'): 1,
  (31, '\xb1'): 1,
  (31, '\xb2'): 1,
  (31, '\xb3'): 1,
  (31, '\xb4'): 1,
  (31, '\xb5'): 1,
  (31, '\xb6'): 1,
  (31, '\xb7'): 1,
  (31, '\xb8'): 1,
  (31, '\xb9'): 1,
  (31, '\xba'): 1,
  (31, '\xbb'): 1,
  (31, '\xbc'): 1,
  (31, '\xbd'): 1,
  (31, '\xbe'): 1,
  (31, '\xbf'): 1,
  (31, '\xc0'): 1,
  (31, '\xc1'): 1,
  (31, '\xc2'): 1,
  (31, '\xc3'): 1,
  (31, '\xc4'): 1,
  (31, '\xc5'): 1,
  (31, '\xc6'): 1,
  (31, '\xc7'): 1,
  (31, '\xc8'): 1,
  (31, '\xc9'): 1,
  (31, '\xca'): 1,
  (31, '\xcb'): 1,
  (31, '\xcc'): 1,
  (31, '\xcd'): 1,
  (31, '\xce'): 1,
  (31, '\xcf'): 1,
  (31, '\xd0'): 1,
  (31, '\xd1'): 1,
  (31, '\xd2'): 1,
  (31, '\xd3'): 1,
  (31, '\xd4'): 1,
  (31, '\xd5'): 1,
  (31, '\xd6'): 1,
  (31, '\xd7'): 1,
  (31, '\xd8'): 1,
  (31, '\xd9'): 1,
  (31, '\xda'): 1,
  (31, '\xdb'): 1,
  (31, '\xdc'): 1,
  (31, '\xdd'): 1,
  (31, '\xde'): 1,
  (31, '\xdf'): 1,
  (31, '\xe0'): 1,
  (31, '\xe1'): 1,
  (31, '\xe3'): 1,
  (31, '\xe4'): 1,
  (31, '\xe5'): 1,
  (31, '\xe6'): 1,
  (31, '\xe7'): 1,
  (31, '\xe8'): 1,
  (31, '\xe9'): 1,
  (31, '\xea'): 1,
  (31, '\xeb'): 1,
  (31, '\xec'): 1,
  (31, '\xed'): 1,
  (31, '\xee'): 1,
  (31, '\xef'): 1,
  (31, '\xf0'): 1,
  (31, '\xf1'): 1,
  (31, '\xf2'): 1,
  (31, '\xf3'): 1,
  (31, '\xf4'): 1,
  (31, '\xf5'): 1,
  (31, '\xf6'): 1,
  (31, '\xf7'): 1,
  (31, '\xf8'): 1,
  (31, '\xf9'): 1,
  (31, '\xfa'): 1,
  (31, '\xfb'): 1,
  (31, '\xfc'): 1,
  (31, '\xfd'): 1,
  (31, '\xfe'): 1,
  (31, '\xff'): 1,
  (32, '\x00'): 1,
  (32, '\x01'): 1,
  (32, '\x02'): 1,
  (32, '\x03'): 1,
  (32, '\x04'): 1,
  (32, '\x05'): 1,
  (32, '\x06'): 1,
  (32, '\x07'): 1,
  (32, '\x08'): 1,
  (32, '\x0b'): 1,
  (32, '\x0e'): 1,
  (32, '\x0f'): 1,
  (32, '\x10'): 1,
  (32, '\x11'): 1,
  (32, '\x12'): 1,
  (32, '\x13'): 1,
  (32, '\x14'): 1,
  (32, '\x15'): 1,
  (32, '\x16'): 1,
  (32, '\x17'): 1,
  (32, '\x18'): 1,
  (32, '\x19'): 1,
  (32, '\x1a'): 1,
  (32, '\x1b'): 1,
  (32, '\x1c'): 1,
  (32, '\x1d'): 1,
  (32, '\x1e'): 1,
  (32, '\x1f'): 1,
  (32, '!'): 1,
  (32, '"'): 1,
  (32, '$'): 1,
  (32, '%'): 1,
  (32, '&'): 1,
  (32, "'"): 1,
  (32, '*'): 1,
  (32, '+'): 1,
  (32, '-'): 1,
  (32, '.'): 1,
  (32, '/'): 1,
  (32, '0'): 1,
  (32, '1'): 1,
  (32, '2'): 1,
  (32, '3'): 1,
  (32, '4'): 1,
  (32, '5'): 1,
  (32, '6'): 1,
  (32, '7'): 1,
  (32, '8'): 1,
  (32, '9'): 1,
  (32, ':'): 1,
  (32, ';'): 1,
  (32, '<'): 1,
  (32, '='): 1,
  (32, '>'): 1,
  (32, '?'): 1,
  (32, '@'): 1,
  (32, 'A'): 1,
  (32, 'B'): 1,
  (32, 'C'): 1,
  (32, 'D'): 1,
  (32, 'E'): 1,
  (32, 'F'): 1,
  (32, 'G'): 1,
  (32, 'H'): 1,
  (32, 'I'): 1,
  (32, 'J'): 1,
  (32, 'K'): 1,
  (32, 'L'): 1,
  (32, 'M'): 1,
  (32, 'N'): 1,
  (32, 'O'): 1,
  (32, 'P'): 1,
  (32, 'Q'): 1,
  (32, 'R'): 1,
  (32, 'S'): 1,
  (32, 'T'): 1,
  (32, 'U'): 1,
  (32, 'V'): 1,
  (32, 'W'): 1,
  (32, 'X'): 1,
  (32, 'Y'): 1,
  (32, 'Z'): 1,
  (32, '['): 1,
  (32, '\\'): 1,
  (32, ']'): 1,
  (32, '^'): 1,
  (32, '_'): 1,
  (32, '`'): 1,
  (32, 'a'): 1,
  (32, 'b'): 1,
  (32, 'c'): 1,
  (32, 'd'): 1,
  (32, 'e'): 1,
  (32, 'f'): 1,
  (32, 'g'): 1,
  (32, 'h'): 1,
  (32, 'i'): 1,
  (32, 'j'): 1,
  (32, 'k'): 1,
  (32, 'l'): 1,
  (32, 'm'): 1,
  (32, 'n'): 1,
  (32, 'o'): 1,
  (32, 'p'): 1,
  (32, 'q'): 1,
  (32, 'r'): 1,
  (32, 's'): 1,
  (32, 't'): 1,
  (32, 'u'): 1,
  (32, 'v'): 1,
  (32, 'w'): 1,
  (32, 'x'): 1,
  (32, 'y'): 1,
  (32, 'z'): 1,
  (32, '{'): 1,
  (32, '|'): 1,
  (32, '}'): 1,
  (32, '~'): 1,
  (32, '\x7f'): 1,
  (32, '\x80'): 1,
  (32, '\x81'): 1,
  (32, '\x82'): 1,
  (32, '\x83'): 1,
  (32, '\x84'): 1,
  (32, '\x85'): 1,
  (32, '\x86'): 1,
  (32, '\x87'): 1,
  (32, '\x88'): 1,
  (32, '\x89'): 1,
  (32, '\x8a'): 1,
  (32, '\x8b'): 1,
  (32, '\x8c'): 1,
  (32, '\x8d'): 1,
  (32, '\x8e'): 1,
  (32, '\x8f'): 1,
  (32, '\x90'): 1,
  (32, '\x91'): 1,
  (32, '\x92'): 1,
  (32, '\x93'): 1,
  (32, '\x94'): 1,
  (32, '\x95'): 1,
  (32, '\x96'): 1,
  (32, '\x97'): 1,
  (32, '\x98'): 1,
  (32, '\x99'): 1,
  (32, '\x9a'): 1,
  (32, '\x9b'): 1,
  (32, '\x9c'): 1,
  (32, '\x9d'): 1,
  (32, '\x9e'): 1,
  (32, '\xa0'): 1,
  (32, '\xa1'): 1,
  (32, '\xa2'): 1,
  (32, '\xa3'): 1,
  (32, '\xa4'): 1,
  (32, '\xa5'): 1,
  (32, '\xa6'): 1,
  (32, '\xa7'): 1,
  (32, '\xa8'): 1,
  (32, '\xa9'): 1,
  (32, '\xac'): 1,
  (32, '\xad'): 1,
  (32, '\xae'): 1,
  (32, '\xaf'): 1,
  (32, '\xb0'): 1,
  (32, '\xb1'): 1,
  (32, '\xb2'): 1,
  (32, '\xb3'): 1,
  (32, '\xb4'): 1,
  (32, '\xb5'): 1,
  (32, '\xb6'): 1,
  (32, '\xb7'): 1,
  (32, '\xb8'): 1,
  (32, '\xb9'): 1,
  (32, '\xba'): 1,
  (32, '\xbb'): 1,
  (32, '\xbc'): 1,
  (32, '\xbd'): 1,
  (32, '\xbe'): 1,
  (32, '\xbf'): 1,
  (32, '\xc0'): 1,
  (32, '\xc1'): 1,
  (32, '\xc2'): 1,
  (32, '\xc3'): 1,
  (32, '\xc4'): 1,
  (32, '\xc5'): 1,
  (32, '\xc6'): 1,
  (32, '\xc7'): 1,
  (32, '\xc8'): 1,
  (32, '\xc9'): 1,
  (32, '\xca'): 1,
  (32, '\xcb'): 1,
  (32, '\xcc'): 1,
  (32, '\xcd'): 1,
  (32, '\xce'): 1,
  (32, '\xcf'): 1,
  (32, '\xd0'): 1,
  (32, '\xd1'): 1,
  (32, '\xd2'): 1,
  (32, '\xd3'): 1,
  (32, '\xd4'): 1,
  (32, '\xd5'): 1,
  (32, '\xd6'): 1,
  (32, '\xd7'): 1,
  (32, '\xd8'): 1,
  (32, '\xd9'): 1,
  (32, '\xda'): 1,
  (32, '\xdb'): 1,
  (32, '\xdc'): 1,
  (32, '\xdd'): 1,
  (32, '\xde'): 1,
  (32, '\xdf'): 1,
  (32, '\xe0'): 1,
  (32, '\xe1'): 1,
  (32, '\xe3'): 1,
  (32, '\xe4'): 1,
  (32, '\xe5'): 1,
  (32, '\xe6'): 1,
  (32, '\xe7'): 1,
  (32, '\xe8'): 1,
  (32, '\xe9'): 1,
  (32, '\xea'): 1,
  (32, '\xeb'): 1,
  (32, '\xec'): 1,
  (32, '\xed'): 1,
  (32, '\xee'): 1,
  (32, '\xef'): 1,
  (32, '\xf0'): 1,
  (32, '\xf1'): 1,
  (32, '\xf2'): 1,
  (32, '\xf3'): 1,
  (32, '\xf4'): 1,
  (32, '\xf5'): 1,
  (32, '\xf6'): 1,
  (32, '\xf7'): 1,
  (32, '\xf8'): 1,
  (32, '\xf9'): 1,
  (32, '\xfa'): 1,
  (32, '\xfb'): 1,
  (32, '\xfc'): 1,
  (32, '\xfd'): 1,
  (32, '\xfe'): 1,
  (32, '\xff'): 1,
  (34, '\x00'): 1,
  (34, '\x01'): 1,
  (34, '\x02'): 1,
  (34, '\x03'): 1,
  (34, '\x04'): 1,
  (34, '\x05'): 1,
  (34, '\x06'): 1,
  (34, '\x07'): 1,
  (34, '\x08'): 1,
  (34, '\x0b'): 1,
  (34, '\x0e'): 1,
  (34, '\x0f'): 1,
  (34, '\x10'): 1,
  (34, '\x11'): 1,
  (34, '\x12'): 1,
  (34, '\x13'): 1,
  (34, '\x14'): 1,
  (34, '\x15'): 1,
  (34, '\x16'): 1,
  (34, '\x17'): 1,
  (34, '\x18'): 1,
  (34, '\x19'): 1,
  (34, '\x1a'): 1,
  (34, '\x1b'): 1,
  (34, '\x1c'): 1,
  (34, '\x1d'): 1,
  (34, '\x1e'): 1,
  (34, '\x1f'): 1,
  (34, '!'): 1,
  (34, '"'): 1,
  (34, '$'): 1,
  (34, '%'): 1,
  (34, '&'): 1,
  (34, "'"): 1,
  (34, '*'): 1,
  (34, '+'): 1,
  (34, '-'): 1,
  (34, '.'): 1,
  (34, '/'): 1,
  (34, '0'): 1,
  (34, '1'): 1,
  (34, '2'): 1,
  (34, '3'): 1,
  (34, '4'): 1,
  (34, '5'): 1,
  (34, '6'): 1,
  (34, '7'): 1,
  (34, '8'): 1,
  (34, '9'): 1,
  (34, ':'): 1,
  (34, ';'): 1,
  (34, '<'): 1,
  (34, '='): 1,
  (34, '>'): 1,
  (34, '?'): 1,
  (34, '@'): 1,
  (34, 'A'): 1,
  (34, 'B'): 1,
  (34, 'C'): 1,
  (34, 'D'): 1,
  (34, 'E'): 1,
  (34, 'F'): 1,
  (34, 'G'): 1,
  (34, 'H'): 1,
  (34, 'I'): 1,
  (34, 'J'): 1,
  (34, 'K'): 1,
  (34, 'L'): 1,
  (34, 'M'): 1,
  (34, 'N'): 1,
  (34, 'O'): 1,
  (34, 'P'): 1,
  (34, 'Q'): 1,
  (34, 'R'): 1,
  (34, 'S'): 1,
  (34, 'T'): 1,
  (34, 'U'): 1,
  (34, 'V'): 1,
  (34, 'W'): 1,
  (34, 'X'): 1,
  (34, 'Y'): 1,
  (34, 'Z'): 1,
  (34, '['): 1,
  (34, '\\'): 1,
  (34, ']'): 1,
  (34, '^'): 1,
  (34, '_'): 1,
  (34, '`'): 1,
  (34, 'a'): 1,
  (34, 'b'): 1,
  (34, 'c'): 1,
  (34, 'd'): 1,
  (34, 'e'): 1,
  (34, 'f'): 1,
  (34, 'g'): 1,
  (34, 'h'): 1,
  (34, 'i'): 1,
  (34, 'j'): 1,
  (34, 'k'): 1,
  (34, 'l'): 1,
  (34, 'm'): 1,
  (34, 'n'): 1,
  (34, 'o'): 1,
  (34, 'p'): 1,
  (34, 'q'): 1,
  (34, 'r'): 1,
  (34, 's'): 1,
  (34, 't'): 1,
  (34, 'u'): 1,
  (34, 'v'): 1,
  (34, 'w'): 1,
  (34, 'x'): 1,
  (34, 'y'): 1,
  (34, 'z'): 1,
  (34, '{'): 1,
  (34, '|'): 1,
  (34, '}'): 1,
  (34, '~'): 1,
  (34, '\x7f'): 1,
  (34, '\x80'): 1,
  (34, '\x81'): 1,
  (34, '\x82'): 1,
  (34, '\x83'): 1,
  (34, '\x84'): 1,
  (34, '\x85'): 1,
  (34, '\x86'): 1,
  (34, '\x87'): 1,
  (34, '\x88'): 1,
  (34, '\x89'): 1,
  (34, '\x8a'): 1,
  (34, '\x8b'): 1,
  (34, '\x8c'): 1,
  (34, '\x8d'): 1,
  (34, '\x8e'): 1,
  (34, '\x8f'): 1,
  (34, '\x90'): 1,
  (34, '\x91'): 1,
  (34, '\x92'): 1,
  (34, '\x93'): 1,
  (34, '\x94'): 1,
  (34, '\x95'): 1,
  (34, '\x96'): 1,
  (34, '\x97'): 1,
  (34, '\x98'): 1,
  (34, '\x99'): 1,
  (34, '\x9a'): 1,
  (34, '\x9b'): 1,
  (34, '\x9c'): 1,
  (34, '\x9d'): 1,
  (34, '\x9e'): 1,
  (34, '\xa0'): 1,
  (34, '\xa1'): 1,
  (34, '\xa2'): 1,
  (34, '\xa3'): 1,
  (34, '\xa4'): 1,
  (34, '\xa5'): 1,
  (34, '\xa6'): 1,
  (34, '\xa7'): 1,
  (34, '\xa8'): 1,
  (34, '\xa9'): 1,
  (34, '\xac'): 1,
  (34, '\xad'): 1,
  (34, '\xae'): 1,
  (34, '\xaf'): 1,
  (34, '\xb0'): 1,
  (34, '\xb1'): 1,
  (34, '\xb2'): 1,
  (34, '\xb3'): 1,
  (34, '\xb4'): 1,
  (34, '\xb5'): 1,
  (34, '\xb6'): 1,
  (34, '\xb7'): 1,
  (34, '\xb8'): 1,
  (34, '\xb9'): 1,
  (34, '\xba'): 1,
  (34, '\xbb'): 1,
  (34, '\xbc'): 1,
  (34, '\xbd'): 1,
  (34, '\xbe'): 1,
  (34, '\xbf'): 1,
  (34, '\xc0'): 1,
  (34, '\xc1'): 1,
  (34, '\xc2'): 1,
  (34, '\xc3'): 1,
  (34, '\xc4'): 1,
  (34, '\xc5'): 1,
  (34, '\xc6'): 1,
  (34, '\xc7'): 1,
  (34, '\xc8'): 1,
  (34, '\xc9'): 1,
  (34, '\xca'): 1,
  (34, '\xcb'): 1,
  (34, '\xcc'): 1,
  (34, '\xcd'): 1,
  (34, '\xce'): 1,
  (34, '\xcf'): 1,
  (34, '\xd0'): 1,
  (34, '\xd1'): 1,
  (34, '\xd2'): 1,
  (34, '\xd3'): 1,
  (34, '\xd4'): 1,
  (34, '\xd5'): 1,
  (34, '\xd6'): 1,
  (34, '\xd7'): 1,
  (34, '\xd8'): 1,
  (34, '\xd9'): 1,
  (34, '\xda'): 1,
  (34, '\xdb'): 1,
  (34, '\xdc'): 1,
  (34, '\xdd'): 1,
  (34, '\xde'): 1,
  (34, '\xdf'): 1,
  (34, '\xe0'): 1,
  (34, '\xe1'): 1,
  (34, '\xe3'): 1,
  (34, '\xe4'): 1,
  (34, '\xe5'): 1,
  (34, '\xe6'): 1,
  (34, '\xe7'): 1,
  (34, '\xe8'): 1,
  (34, '\xe9'): 1,
  (34, '\xea'): 1,
  (34, '\xeb'): 1,
  (34, '\xec'): 1,
  (34, '\xed'): 1,
  (34, '\xee'): 1,
  (34, '\xef'): 1,
  (34, '\xf0'): 1,
  (34, '\xf1'): 1,
  (34, '\xf2'): 1,
  (34, '\xf3'): 1,
  (34, '\xf4'): 1,
  (34, '\xf5'): 1,
  (34, '\xf6'): 1,
  (34, '\xf7'): 1,
  (34, '\xf8'): 1,
  (34, '\xf9'): 1,
  (34, '\xfa'): 1,
  (34, '\xfb'): 1,
  (34, '\xfc'): 1,
  (34, '\xfd'): 1,
  (34, '\xfe'): 1,
  (34, '\xff'): 1,
  (36, '\x00'): 1,
  (36, '\x01'): 1,
  (36, '\x02'): 1,
  (36, '\x03'): 1,
  (36, '\x04'): 1,
  (36, '\x05'): 1,
  (36, '\x06'): 1,
  (36, '\x07'): 1,
  (36, '\x08'): 1,
  (36, '\x0b'): 1,
  (36, '\x0e'): 1,
  (36, '\x0f'): 1,
  (36, '\x10'): 1,
  (36, '\x11'): 1,
  (36, '\x12'): 1,
  (36, '\x13'): 1,
  (36, '\x14'): 1,
  (36, '\x15'): 1,
  (36, '\x16'): 1,
  (36, '\x17'): 1,
  (36, '\x18'): 1,
  (36, '\x19'): 1,
  (36, '\x1a'): 1,
  (36, '\x1b'): 1,
  (36, '\x1c'): 1,
  (36, '\x1d'): 1,
  (36, '\x1e'): 1,
  (36, '\x1f'): 1,
  (36, '!'): 1,
  (36, '"'): 1,
  (36, '$'): 1,
  (36, '%'): 1,
  (36, '&'): 1,
  (36, "'"): 1,
  (36, '*'): 1,
  (36, '+'): 1,
  (36, '-'): 1,
  (36, '.'): 1,
  (36, '/'): 1,
  (36, '0'): 36,
  (36, '1'): 36,
  (36, '2'): 36,
  (36, '3'): 36,
  (36, '4'): 36,
  (36, '5'): 36,
  (36, '6'): 36,
  (36, '7'): 36,
  (36, '8'): 36,
  (36, '9'): 36,
  (36, ':'): 1,
  (36, ';'): 1,
  (36, '<'): 1,
  (36, '='): 1,
  (36, '>'): 1,
  (36, '?'): 1,
  (36, '@'): 1,
  (36, 'A'): 1,
  (36, 'B'): 1,
  (36, 'C'): 1,
  (36, 'D'): 1,
  (36, 'E'): 1,
  (36, 'F'): 1,
  (36, 'G'): 1,
  (36, 'H'): 1,
  (36, 'I'): 1,
  (36, 'J'): 1,
  (36, 'K'): 1,
  (36, 'L'): 1,
  (36, 'M'): 1,
  (36, 'N'): 1,
  (36, 'O'): 1,
  (36, 'P'): 1,
  (36, 'Q'): 1,
  (36, 'R'): 1,
  (36, 'S'): 1,
  (36, 'T'): 1,
  (36, 'U'): 1,
  (36, 'V'): 1,
  (36, 'W'): 1,
  (36, 'X'): 1,
  (36, 'Y'): 1,
  (36, 'Z'): 1,
  (36, '['): 1,
  (36, '\\'): 1,
  (36, ']'): 1,
  (36, '^'): 1,
  (36, '_'): 1,
  (36, '`'): 1,
  (36, 'a'): 1,
  (36, 'b'): 1,
  (36, 'c'): 1,
  (36, 'd'): 1,
  (36, 'e'): 1,
  (36, 'f'): 1,
  (36, 'g'): 1,
  (36, 'h'): 1,
  (36, 'i'): 1,
  (36, 'j'): 1,
  (36, 'k'): 1,
  (36, 'l'): 1,
  (36, 'm'): 1,
  (36, 'n'): 1,
  (36, 'o'): 1,
  (36, 'p'): 1,
  (36, 'q'): 1,
  (36, 'r'): 1,
  (36, 's'): 1,
  (36, 't'): 1,
  (36, 'u'): 1,
  (36, 'v'): 1,
  (36, 'w'): 1,
  (36, 'x'): 1,
  (36, 'y'): 1,
  (36, 'z'): 1,
  (36, '{'): 1,
  (36, '|'): 1,
  (36, '}'): 1,
  (36, '~'): 1,
  (36, '\x7f'): 1,
  (36, '\x80'): 1,
  (36, '\x81'): 1,
  (36, '\x82'): 1,
  (36, '\x83'): 1,
  (36, '\x84'): 1,
  (36, '\x85'): 1,
  (36, '\x86'): 1,
  (36, '\x87'): 1,
  (36, '\x88'): 1,
  (36, '\x89'): 1,
  (36, '\x8a'): 1,
  (36, '\x8b'): 1,
  (36, '\x8c'): 1,
  (36, '\x8d'): 1,
  (36, '\x8e'): 1,
  (36, '\x8f'): 1,
  (36, '\x90'): 1,
  (36, '\x91'): 1,
  (36, '\x92'): 1,
  (36, '\x93'): 1,
  (36, '\x94'): 1,
  (36, '\x95'): 1,
  (36, '\x96'): 1,
  (36, '\x97'): 1,
  (36, '\x98'): 1,
  (36, '\x99'): 1,
  (36, '\x9a'): 1,
  (36, '\x9b'): 1,
  (36, '\x9c'): 1,
  (36, '\x9d'): 1,
  (36, '\x9e'): 1,
  (36, '\xa0'): 1,
  (36, '\xa1'): 1,
  (36, '\xa2'): 1,
  (36, '\xa3'): 1,
  (36, '\xa4'): 1,
  (36, '\xa5'): 1,
  (36, '\xa6'): 1,
  (36, '\xa7'): 1,
  (36, '\xa8'): 1,
  (36, '\xa9'): 1,
  (36, '\xac'): 1,
  (36, '\xad'): 1,
  (36, '\xae'): 1,
  (36, '\xaf'): 1,
  (36, '\xb0'): 1,
  (36, '\xb1'): 1,
  (36, '\xb2'): 1,
  (36, '\xb3'): 1,
  (36, '\xb4'): 1,
  (36, '\xb5'): 1,
  (36, '\xb6'): 1,
  (36, '\xb7'): 1,
  (36, '\xb8'): 1,
  (36, '\xb9'): 1,
  (36, '\xba'): 1,
  (36, '\xbb'): 1,
  (36, '\xbc'): 1,
  (36, '\xbd'): 1,
  (36, '\xbe'): 1,
  (36, '\xbf'): 1,
  (36, '\xc0'): 1,
  (36, '\xc1'): 1,
  (36, '\xc2'): 1,
  (36, '\xc3'): 1,
  (36, '\xc4'): 1,
  (36, '\xc5'): 1,
  (36, '\xc6'): 1,
  (36, '\xc7'): 1,
  (36, '\xc8'): 1,
  (36, '\xc9'): 1,
  (36, '\xca'): 1,
  (36, '\xcb'): 1,
  (36, '\xcc'): 1,
  (36, '\xcd'): 1,
  (36, '\xce'): 1,
  (36, '\xcf'): 1,
  (36, '\xd0'): 1,
  (36, '\xd1'): 1,
  (36, '\xd2'): 1,
  (36, '\xd3'): 1,
  (36, '\xd4'): 1,
  (36, '\xd5'): 1,
  (36, '\xd6'): 1,
  (36, '\xd7'): 1,
  (36, '\xd8'): 1,
  (36, '\xd9'): 1,
  (36, '\xda'): 1,
  (36, '\xdb'): 1,
  (36, '\xdc'): 1,
  (36, '\xdd'): 1,
  (36, '\xde'): 1,
  (36, '\xdf'): 1,
  (36, '\xe0'): 1,
  (36, '\xe1'): 1,
  (36, '\xe3'): 1,
  (36, '\xe4'): 1,
  (36, '\xe5'): 1,
  (36, '\xe6'): 1,
  (36, '\xe7'): 1,
  (36, '\xe8'): 1,
  (36, '\xe9'): 1,
  (36, '\xea'): 1,
  (36, '\xeb'): 1,
  (36, '\xec'): 1,
  (36, '\xed'): 1,
  (36, '\xee'): 1,
  (36, '\xef'): 1,
  (36, '\xf0'): 1,
  (36, '\xf1'): 1,
  (36, '\xf2'): 1,
  (36, '\xf3'): 1,
  (36, '\xf4'): 1,
  (36, '\xf5'): 1,
  (36, '\xf6'): 1,
  (36, '\xf7'): 1,
  (36, '\xf8'): 1,
  (36, '\xf9'): 1,
  (36, '\xfa'): 1,
  (36, '\xfb'): 1,
  (36, '\xfc'): 1,
  (36, '\xfd'): 1,
  (36, '\xfe'): 1,
  (36, '\xff'): 1,
  (37, '\x00'): 1,
  (37, '\x01'): 1,
  (37, '\x02'): 1,
  (37, '\x03'): 1,
  (37, '\x04'): 1,
  (37, '\x05'): 1,
  (37, '\x06'): 1,
  (37, '\x07'): 1,
  (37, '\x08'): 1,
  (37, '\x0b'): 1,
  (37, '\x0e'): 1,
  (37, '\x0f'): 1,
  (37, '\x10'): 1,
  (37, '\x11'): 1,
  (37, '\x12'): 1,
  (37, '\x13'): 1,
  (37, '\x14'): 1,
  (37, '\x15'): 1,
  (37, '\x16'): 1,
  (37, '\x17'): 1,
  (37, '\x18'): 1,
  (37, '\x19'): 1,
  (37, '\x1a'): 1,
  (37, '\x1b'): 1,
  (37, '\x1c'): 1,
  (37, '\x1d'): 1,
  (37, '\x1e'): 1,
  (37, '\x1f'): 1,
  (37, '!'): 1,
  (37, '"'): 1,
  (37, '$'): 1,
  (37, '%'): 1,
  (37, '&'): 1,
  (37, "'"): 1,
  (37, '*'): 1,
  (37, '+'): 1,
  (37, '-'): 1,
  (37, '.'): 38,
  (37, '/'): 1,
  (37, '0'): 37,
  (37, '1'): 37,
  (37, '2'): 37,
  (37, '3'): 37,
  (37, '4'): 37,
  (37, '5'): 37,
  (37, '6'): 37,
  (37, '7'): 37,
  (37, '8'): 37,
  (37, '9'): 37,
  (37, ':'): 1,
  (37, ';'): 1,
  (37, '<'): 1,
  (37, '='): 1,
  (37, '>'): 1,
  (37, '?'): 1,
  (37, '@'): 1,
  (37, 'A'): 1,
  (37, 'B'): 1,
  (37, 'C'): 1,
  (37, 'D'): 1,
  (37, 'E'): 1,
  (37, 'F'): 1,
  (37, 'G'): 1,
  (37, 'H'): 1,
  (37, 'I'): 1,
  (37, 'J'): 1,
  (37, 'K'): 1,
  (37, 'L'): 1,
  (37, 'M'): 1,
  (37, 'N'): 1,
  (37, 'O'): 1,
  (37, 'P'): 1,
  (37, 'Q'): 1,
  (37, 'R'): 1,
  (37, 'S'): 1,
  (37, 'T'): 1,
  (37, 'U'): 1,
  (37, 'V'): 1,
  (37, 'W'): 1,
  (37, 'X'): 1,
  (37, 'Y'): 1,
  (37, 'Z'): 1,
  (37, '['): 1,
  (37, '\\'): 1,
  (37, ']'): 1,
  (37, '^'): 1,
  (37, '_'): 1,
  (37, '`'): 1,
  (37, 'a'): 1,
  (37, 'b'): 1,
  (37, 'c'): 1,
  (37, 'd'): 1,
  (37, 'e'): 1,
  (37, 'f'): 1,
  (37, 'g'): 1,
  (37, 'h'): 1,
  (37, 'i'): 1,
  (37, 'j'): 1,
  (37, 'k'): 1,
  (37, 'l'): 1,
  (37, 'm'): 1,
  (37, 'n'): 1,
  (37, 'o'): 1,
  (37, 'p'): 1,
  (37, 'q'): 1,
  (37, 'r'): 1,
  (37, 's'): 1,
  (37, 't'): 1,
  (37, 'u'): 1,
  (37, 'v'): 1,
  (37, 'w'): 1,
  (37, 'x'): 1,
  (37, 'y'): 1,
  (37, 'z'): 1,
  (37, '{'): 1,
  (37, '|'): 1,
  (37, '}'): 1,
  (37, '~'): 1,
  (37, '\x7f'): 1,
  (37, '\x80'): 1,
  (37, '\x81'): 1,
  (37, '\x82'): 1,
  (37, '\x83'): 1,
  (37, '\x84'): 1,
  (37, '\x85'): 1,
  (37, '\x86'): 1,
  (37, '\x87'): 1,
  (37, '\x88'): 1,
  (37, '\x89'): 1,
  (37, '\x8a'): 1,
  (37, '\x8b'): 1,
  (37, '\x8c'): 1,
  (37, '\x8d'): 1,
  (37, '\x8e'): 1,
  (37, '\x8f'): 1,
  (37, '\x90'): 1,
  (37, '\x91'): 1,
  (37, '\x92'): 1,
  (37, '\x93'): 1,
  (37, '\x94'): 1,
  (37, '\x95'): 1,
  (37, '\x96'): 1,
  (37, '\x97'): 1,
  (37, '\x98'): 1,
  (37, '\x99'): 1,
  (37, '\x9a'): 1,
  (37, '\x9b'): 1,
  (37, '\x9c'): 1,
  (37, '\x9d'): 1,
  (37, '\x9e'): 1,
  (37, '\xa0'): 1,
  (37, '\xa1'): 1,
  (37, '\xa2'): 1,
  (37, '\xa3'): 1,
  (37, '\xa4'): 1,
  (37, '\xa5'): 1,
  (37, '\xa6'): 1,
  (37, '\xa7'): 1,
  (37, '\xa8'): 1,
  (37, '\xa9'): 1,
  (37, '\xac'): 1,
  (37, '\xad'): 1,
  (37, '\xae'): 1,
  (37, '\xaf'): 1,
  (37, '\xb0'): 1,
  (37, '\xb1'): 1,
  (37, '\xb2'): 1,
  (37, '\xb3'): 1,
  (37, '\xb4'): 1,
  (37, '\xb5'): 1,
  (37, '\xb6'): 1,
  (37, '\xb7'): 1,
  (37, '\xb8'): 1,
  (37, '\xb9'): 1,
  (37, '\xba'): 1,
  (37, '\xbb'): 1,
  (37, '\xbc'): 1,
  (37, '\xbd'): 1,
  (37, '\xbe'): 1,
  (37, '\xbf'): 1,
  (37, '\xc0'): 1,
  (37, '\xc1'): 1,
  (37, '\xc2'): 1,
  (37, '\xc3'): 1,
  (37, '\xc4'): 1,
  (37, '\xc5'): 1,
  (37, '\xc6'): 1,
  (37, '\xc7'): 1,
  (37, '\xc8'): 1,
  (37, '\xc9'): 1,
  (37, '\xca'): 1,
  (37, '\xcb'): 1,
  (37, '\xcc'): 1,
  (37, '\xcd'): 1,
  (37, '\xce'): 1,
  (37, '\xcf'): 1,
  (37, '\xd0'): 1,
  (37, '\xd1'): 1,
  (37, '\xd2'): 1,
  (37, '\xd3'): 1,
  (37, '\xd4'): 1,
  (37, '\xd5'): 1,
  (37, '\xd6'): 1,
  (37, '\xd7'): 1,
  (37, '\xd8'): 1,
  (37, '\xd9'): 1,
  (37, '\xda'): 1,
  (37, '\xdb'): 1,
  (37, '\xdc'): 1,
  (37, '\xdd'): 1,
  (37, '\xde'): 1,
  (37, '\xdf'): 1,
  (37, '\xe0'): 1,
  (37, '\xe1'): 1,
  (37, '\xe3'): 1,
  (37, '\xe4'): 1,
  (37, '\xe5'): 1,
  (37, '\xe6'): 1,
  (37, '\xe7'): 1,
  (37, '\xe8'): 1,
  (37, '\xe9'): 1,
  (37, '\xea'): 1,
  (37, '\xeb'): 1,
  (37, '\xec'): 1,
  (37, '\xed'): 1,
  (37, '\xee'): 1,
  (37, '\xef'): 1,
  (37, '\xf0'): 1,
  (37, '\xf1'): 1,
  (37, '\xf2'): 1,
  (37, '\xf3'): 1,
  (37, '\xf4'): 1,
  (37, '\xf5'): 1,
  (37, '\xf6'): 1,
  (37, '\xf7'): 1,
  (37, '\xf8'): 1,
  (37, '\xf9'): 1,
  (37, '\xfa'): 1,
  (37, '\xfb'): 1,
  (37, '\xfc'): 1,
  (37, '\xfd'): 1,
  (37, '\xfe'): 1,
  (37, '\xff'): 1,
  (38, '\x00'): 1,
  (38, '\x01'): 1,
  (38, '\x02'): 1,
  (38, '\x03'): 1,
  (38, '\x04'): 1,
  (38, '\x05'): 1,
  (38, '\x06'): 1,
  (38, '\x07'): 1,
  (38, '\x08'): 1,
  (38, '\x0b'): 1,
  (38, '\x0e'): 1,
  (38, '\x0f'): 1,
  (38, '\x10'): 1,
  (38, '\x11'): 1,
  (38, '\x12'): 1,
  (38, '\x13'): 1,
  (38, '\x14'): 1,
  (38, '\x15'): 1,
  (38, '\x16'): 1,
  (38, '\x17'): 1,
  (38, '\x18'): 1,
  (38, '\x19'): 1,
  (38, '\x1a'): 1,
  (38, '\x1b'): 1,
  (38, '\x1c'): 1,
  (38, '\x1d'): 1,
  (38, '\x1e'): 1,
  (38, '\x1f'): 1,
  (38, '!'): 1,
  (38, '"'): 1,
  (38, '$'): 1,
  (38, '%'): 1,
  (38, '&'): 1,
  (38, "'"): 1,
  (38, '*'): 1,
  (38, '+'): 1,
  (38, '-'): 1,
  (38, '.'): 1,
  (38, '/'): 1,
  (38, '0'): 36,
  (38, '1'): 36,
  (38, '2'): 36,
  (38, '3'): 36,
  (38, '4'): 36,
  (38, '5'): 36,
  (38, '6'): 36,
  (38, '7'): 36,
  (38, '8'): 36,
  (38, '9'): 36,
  (38, ':'): 1,
  (38, ';'): 1,
  (38, '<'): 1,
  (38, '='): 1,
  (38, '>'): 1,
  (38, '?'): 1,
  (38, '@'): 1,
  (38, 'A'): 1,
  (38, 'B'): 1,
  (38, 'C'): 1,
  (38, 'D'): 1,
  (38, 'E'): 1,
  (38, 'F'): 1,
  (38, 'G'): 1,
  (38, 'H'): 1,
  (38, 'I'): 1,
  (38, 'J'): 1,
  (38, 'K'): 1,
  (38, 'L'): 1,
  (38, 'M'): 1,
  (38, 'N'): 1,
  (38, 'O'): 1,
  (38, 'P'): 1,
  (38, 'Q'): 1,
  (38, 'R'): 1,
  (38, 'S'): 1,
  (38, 'T'): 1,
  (38, 'U'): 1,
  (38, 'V'): 1,
  (38, 'W'): 1,
  (38, 'X'): 1,
  (38, 'Y'): 1,
  (38, 'Z'): 1,
  (38, '['): 1,
  (38, '\\'): 1,
  (38, ']'): 1,
  (38, '^'): 1,
  (38, '_'): 1,
  (38, '`'): 1,
  (38, 'a'): 1,
  (38, 'b'): 1,
  (38, 'c'): 1,
  (38, 'd'): 1,
  (38, 'e'): 1,
  (38, 'f'): 1,
  (38, 'g'): 1,
  (38, 'h'): 1,
  (38, 'i'): 1,
  (38, 'j'): 1,
  (38, 'k'): 1,
  (38, 'l'): 1,
  (38, 'm'): 1,
  (38, 'n'): 1,
  (38, 'o'): 1,
  (38, 'p'): 1,
  (38, 'q'): 1,
  (38, 'r'): 1,
  (38, 's'): 1,
  (38, 't'): 1,
  (38, 'u'): 1,
  (38, 'v'): 1,
  (38, 'w'): 1,
  (38, 'x'): 1,
  (38, 'y'): 1,
  (38, 'z'): 1,
  (38, '{'): 1,
  (38, '|'): 1,
  (38, '}'): 1,
  (38, '~'): 1,
  (38, '\x7f'): 1,
  (38, '\x80'): 1,
  (38, '\x81'): 1,
  (38, '\x82'): 1,
  (38, '\x83'): 1,
  (38, '\x84'): 1,
  (38, '\x85'): 1,
  (38, '\x86'): 1,
  (38, '\x87'): 1,
  (38, '\x88'): 1,
  (38, '\x89'): 1,
  (38, '\x8a'): 1,
  (38, '\x8b'): 1,
  (38, '\x8c'): 1,
  (38, '\x8d'): 1,
  (38, '\x8e'): 1,
  (38, '\x8f'): 1,
  (38, '\x90'): 1,
  (38, '\x91'): 1,
  (38, '\x92'): 1,
  (38, '\x93'): 1,
  (38, '\x94'): 1,
  (38, '\x95'): 1,
  (38, '\x96'): 1,
  (38, '\x97'): 1,
  (38, '\x98'): 1,
  (38, '\x99'): 1,
  (38, '\x9a'): 1,
  (38, '\x9b'): 1,
  (38, '\x9c'): 1,
  (38, '\x9d'): 1,
  (38, '\x9e'): 1,
  (38, '\xa0'): 1,
  (38, '\xa1'): 1,
  (38, '\xa2'): 1,
  (38, '\xa3'): 1,
  (38, '\xa4'): 1,
  (38, '\xa5'): 1,
  (38, '\xa6'): 1,
  (38, '\xa7'): 1,
  (38, '\xa8'): 1,
  (38, '\xa9'): 1,
  (38, '\xac'): 1,
  (38, '\xad'): 1,
  (38, '\xae'): 1,
  (38, '\xaf'): 1,
  (38, '\xb0'): 1,
  (38, '\xb1'): 1,
  (38, '\xb2'): 1,
  (38, '\xb3'): 1,
  (38, '\xb4'): 1,
  (38, '\xb5'): 1,
  (38, '\xb6'): 1,
  (38, '\xb7'): 1,
  (38, '\xb8'): 1,
  (38, '\xb9'): 1,
  (38, '\xba'): 1,
  (38, '\xbb'): 1,
  (38, '\xbc'): 1,
  (38, '\xbd'): 1,
  (38, '\xbe'): 1,
  (38, '\xbf'): 1,
  (38, '\xc0'): 1,
  (38, '\xc1'): 1,
  (38, '\xc2'): 1,
  (38, '\xc3'): 1,
  (38, '\xc4'): 1,
  (38, '\xc5'): 1,
  (38, '\xc6'): 1,
  (38, '\xc7'): 1,
  (38, '\xc8'): 1,
  (38, '\xc9'): 1,
  (38, '\xca'): 1,
  (38, '\xcb'): 1,
  (38, '\xcc'): 1,
  (38, '\xcd'): 1,
  (38, '\xce'): 1,
  (38, '\xcf'): 1,
  (38, '\xd0'): 1,
  (38, '\xd1'): 1,
  (38, '\xd2'): 1,
  (38, '\xd3'): 1,
  (38, '\xd4'): 1,
  (38, '\xd5'): 1,
  (38, '\xd6'): 1,
  (38, '\xd7'): 1,
  (38, '\xd8'): 1,
  (38, '\xd9'): 1,
  (38, '\xda'): 1,
  (38, '\xdb'): 1,
  (38, '\xdc'): 1,
  (38, '\xdd'): 1,
  (38, '\xde'): 1,
  (38, '\xdf'): 1,
  (38, '\xe0'): 1,
  (38, '\xe1'): 1,
  (38, '\xe3'): 1,
  (38, '\xe4'): 1,
  (38, '\xe5'): 1,
  (38, '\xe6'): 1,
  (38, '\xe7'): 1,
  (38, '\xe8'): 1,
  (38, '\xe9'): 1,
  (38, '\xea'): 1,
  (38, '\xeb'): 1,
  (38, '\xec'): 1,
  (38, '\xed'): 1,
  (38, '\xee'): 1,
  (38, '\xef'): 1,
  (38, '\xf0'): 1,
  (38, '\xf1'): 1,
  (38, '\xf2'): 1,
  (38, '\xf3'): 1,
  (38, '\xf4'): 1,
  (38, '\xf5'): 1,
  (38, '\xf6'): 1,
  (38, '\xf7'): 1,
  (38, '\xf8'): 1,
  (38, '\xf9'): 1,
  (38, '\xfa'): 1,
  (38, '\xfb'): 1,
  (38, '\xfc'): 1,
  (38, '\xfd'): 1,
  (38, '\xfe'): 1,
  (38, '\xff'): 1,
  (39, '0'): 40,
  (39, '1'): 40,
  (39, '2'): 40,
  (39, '3'): 40,
  (39, '4'): 40,
  (39, '5'): 40,
  (39, '6'): 40,
  (39, '7'): 40,
  (39, '8'): 40,
  (39, '9'): 40,
  (40, '0'): 40,
  (40, '1'): 40,
  (40, '2'): 40,
  (40, '3'): 40,
  (40, '4'): 40,
  (40, '5'): 40,
  (40, '6'): 40,
  (40, '7'): 40,
  (40, '8'): 40,
  (40, '9'): 40},
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
      11,
      17,
      18,
      19,
      24,
      27,
      28,
      29,
      30,
      31,
      32,
      33,
      34,
      35,
      36,
      37,
      38,
      40]),
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
      11,
      17,
      18,
      19,
      24,
      27,
      28,
      29,
      30,
      31,
      32,
      33,
      34,
      35,
      36,
      37,
      38,
      40]),
 ['IGNORE',
  'NAME',
  'IGNORE',
  'LEFT_PARENTHESIS',
  '__0_,',
  'INTEGER',
  'IGNORE',
  'NAME',
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
  'NAME',
  'MU',
  'LAMBDA',
  'LAMBDA',
  'ULAMBDA',
  'ULAMBDA',
  'FLOAT',
  'INTEGER',
  'NAME',
  'final*, 1, 0',
  'FLOAT']), {'IGNORE': None})
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
    f.write(newcontent.encode("utf-8"), mode="wb")
