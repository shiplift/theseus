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
from rpython.rlib.objectmodel import we_are_translated, not_rpython
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
    def __enter__(self):
        self.parser.bindings_stack.append({})
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
    def error(self, reason):
        raise ParseError(self._node.getsourcepos(), reason)


# A small token
no_result = model.W_Object()
#   
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

    def innermost_bindings(self):
        return self.bindings_stack[-1]

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

    def define(self, key, value, bindings=None):
        if bindings is None:
            bindings = self.innermost_bindings()
        bindings[key] = value

    def define_lambda(self, inbox):
        "Named lambdas only makes sense in the toplevel currently"
        bindings = self.toplevel_bindings()
        box = bindings.get(inbox.name, None)
        if box is not None:
            box.update(inbox)
        else:
            bindings[inbox.name] = inbox

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

    def make_lambda(self, name=""):
        return model.W_Lambda(rules=[], name=name)

    def fill_lambda(self, node, w_lambda):
        rules = self.handle_all(node.children)
        assert isinstance(rules, list)
        # lets show the annotator that these all are indeed rules
        w_lambda._rules = [None] * len(rules)
        for i, r in enumerate(rules):
            assert isinstance(r, expression.Rule)
            w_lambda._rules[i] = r
        return w_lambda

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

    def visit_value_definition(self, node):
        assert len(node.children) == 2
        name = self.get_name(node)
        definee = self.dispatch(node.children[1])[0]
        self.define(name, definee, self.toplevel_bindings())
        return [no_result]

    def visit_lambda_definition(self, node):
        assert len(node.children) == 2
        name = self.get_name(node)
        w_lambda = self.make_lambda(name)
        self.define_lambda(expression.LambdaBox(
            LambdaInfo(node), name, w_lambda))
        definee = self.fill_lambda(node.children[1],  w_lambda)
        self.define_lambda(expression.LambdaBox(
            LambdaInfo(node), name, definee))
        return [no_result]

    def visit_lambda_forward(self, node):
        "Forward-define a lambda, for co-recursion"
        assert len(node.children) >= 1
        name = self.get_name(node)
        w_lambda = self.make_lambda(name)
        self.define_lambda(expression.LambdaBox(
            LambdaInfo(node),name, w_lambda))
        return [no_result]

    def visit_lambda(self, node):
        return [self.fill_lambda(node, self.make_lambda())]

    def visit_rule(self, node):
        if len(node.children) == 1:
            patterns_ = None
            effect_   = node.children[0]
        else:
            patterns_ = node.children[0]
            effect_   = node.children[1]

        with Scope(self):
            with RulePatterns(self):
                current_patterns = self.dispatch(patterns_) if patterns_ else []
            with RuleEffects(self):
                current_effect = self.dispatch(effect_)[0]

        return [expression.Rule(current_patterns, current_effect)]

    def visit_continuation(self, node):
        assert False, "Continuation sohuld not reach here"
    
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
                reason = "Value bound to %s in pattern" % name
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
        # print node              
        return self.handle_all(node.children)

    # @not_rpython
    # def general_symbol_visit(self, node):
    #     print "g_s_v:\t", type(node), node
    #     assert False, node.additional_info
    #     return self.make_string(node, strip=False)

    # @not_rpython
    # def general_visit(self, node):
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
    def visit__maybe_symbol6(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol7(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit_application(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 4:
            children = []
            children.extend(self.visit_expression(node.children[2]))
            return [Nonterminal(node.symbol, children)]
        if length == 5:
            if node.children[2].symbol == '_maybe_symbol7':
                children = []
                expr = self.visit__maybe_symbol7(node.children[2])
                assert len(expr) == 1
                children.extend(expr[0].children)
                children.extend(self.visit_expression(node.children[3]))
                return [Nonterminal(node.symbol, children)]
            children = []
            children.extend(self.visit_expression(node.children[2]))
            children.extend(self.visit_application_args(node.children[3]))
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol6(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        children.extend(self.visit_expression(node.children[3]))
        children.extend(self.visit_application_args(node.children[4]))
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol8(self, node):
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
            if node.children[1].symbol == '_maybe_symbol8':
                children = []
                expr = self.visit__maybe_symbol8(node.children[1])
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
        expr = self.visit__maybe_symbol8(node.children[1])
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
    def visit__maybe_symbol9(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit_lambda(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit_lambda_content(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol9(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit_lambda_content(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_lambda_content(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if node.children[0].symbol == 'rule':
            children = []
            children.extend(self.visit_rule(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit_rules(node.children[0])
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
    def visit__maybe_symbol10(self, node):
        #auto-generated code, don't edit
        children = []
        expr = self.visit__plus_symbol2(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit_rules(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_rules(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 3:
            children = []
            children.extend(self.visit_rule(node.children[2]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_rule(node.children[2]))
        expr = self.visit__maybe_symbol10(node.children[3])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol11(self, node):
        #auto-generated code, don't edit
        children = []
        children.extend(self.visit_patterns(node.children[0]))
        return [Nonterminal(node.symbol, children)]
    def visit_rule(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit_body(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol11(node.children[0])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit_body(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit_body(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if node.children[0].symbol == 'continuation':
            children = []
            children.extend(self.visit_continuation(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_expression(node.children[0]))
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol12(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit_continuation(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 3:
            children = []
            children.extend(self.visit_expression(node.children[0]))
            children.extend(self.visit_lambda_content(node.children[2]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_expression(node.children[0]))
        expr = self.visit__maybe_symbol12(node.children[2])
        assert len(expr) == 1
        children.extend(expr[0].children)
        children.extend(self.visit_lambda_content(node.children[3]))
        return [Nonterminal(node.symbol, children)]
    def visit__maybe_symbol13(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol14(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit____star_symbol14_rest_0_0(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol13(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit____star_symbol14_rest_0_0(node.children[2])
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
        expr = self.visit__star_symbol14(node.children[1])
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
    def visit__maybe_symbol15(self, node):
        #auto-generated code, don't edit
        children = []
        return [Nonterminal(node.symbol, children)]
    def visit__star_symbol16(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 2:
            children = []
            expr = self.visit____star_symbol16_rest_0_0(node.children[1])
            assert len(expr) == 1
            children.extend(expr[0].children)
            return [Nonterminal(node.symbol, children)]
        children = []
        expr = self.visit__maybe_symbol15(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        expr = self.visit____star_symbol16_rest_0_0(node.children[2])
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
        expr = self.visit__star_symbol16(node.children[1])
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
    def visit____star_symbol14_rest_0_0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_pattern(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_pattern(node.children[0]))
        expr = self.visit__star_symbol14(node.children[1])
        assert len(expr) == 1
        children.extend(expr[0].children)
        return [Nonterminal(node.symbol, children)]
    def visit____star_symbol16_rest_0_0(self, node):
        #auto-generated code, don't edit
        length = len(node.children)
        if length == 1:
            children = []
            children.extend(self.visit_pattern(node.children[0]))
            return [Nonterminal(node.symbol, children)]
        children = []
        children.extend(self.visit_pattern(node.children[0]))
        expr = self.visit__star_symbol16(node.children[1])
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
  Rule('_maybe_symbol6', [['NEWLINE']]),
  Rule('_maybe_symbol7', [['NEWLINE']]),
  Rule('application', [['MU', 'LEFT_PARENTHESIS', '_maybe_symbol6', 'expression', 'application_args', 'RIGHT_PARENTHESIS'], ['MU', 'LEFT_PARENTHESIS', 'expression', 'application_args', 'RIGHT_PARENTHESIS'], ['MU', 'LEFT_PARENTHESIS', '_maybe_symbol7', 'expression', 'RIGHT_PARENTHESIS'], ['MU', 'LEFT_PARENTHESIS', 'expression', 'RIGHT_PARENTHESIS']]),
  Rule('_maybe_symbol8', [['NEWLINE']]),
  Rule('_plus_symbol1', [['__0_,', '_maybe_symbol8', 'expression', '_plus_symbol1'], ['__0_,', 'expression', '_plus_symbol1'], ['__0_,', '_maybe_symbol8', 'expression'], ['__0_,', 'expression']]),
  Rule('application_args', [['_plus_symbol1']]),
  Rule('_maybe_symbol9', [['NEWLINE']]),
  Rule('lambda', [['LAMBDA', '_maybe_symbol9', 'lambda_content'], ['LAMBDA', 'lambda_content']]),
  Rule('lambda_content', [['rules'], ['rule']]),
  Rule('_plus_symbol2', [['NEWLINE', '_plus_symbol2'], ['NEWLINE']]),
  Rule('_maybe_symbol10', [['_plus_symbol2', 'rules']]),
  Rule('rules', [['INTEGER', '__1_.', 'rule', '_maybe_symbol10'], ['INTEGER', '__1_.', 'rule']]),
  Rule('_maybe_symbol11', [['patterns']]),
  Rule('rule', [['_maybe_symbol11', 'MAPSTO', 'body'], ['MAPSTO', 'body']]),
  Rule('body', [['continuation'], ['expression']]),
  Rule('_maybe_symbol12', [['NEWLINE']]),
  Rule('continuation', [['expression', 'RIGHTWARDS_DOUBLE_ARROW', '_maybe_symbol12', 'lambda_content'], ['expression', 'RIGHTWARDS_DOUBLE_ARROW', 'lambda_content']]),
  Rule('_maybe_symbol13', [['NEWLINE']]),
  Rule('_star_symbol14', [['__0_,', '_maybe_symbol13', '___star_symbol14_rest_0_0'], ['__0_,', '___star_symbol14_rest_0_0']]),
  Rule('patterns', [['pattern', '_star_symbol14'], ['pattern']]),
  Rule('pattern', [['constructor_pattern'], ['variable_pattern'], ['primary_pattern']]),
  Rule('variable_pattern', [['variable']]),
  Rule('primary_pattern', [['primary']]),
  Rule('constructor_pattern', [['NAME', 'constructor_pattern_args']]),
  Rule('constructor_pattern_args', [['LEFT_PARENTHESIS', 'pattern_arglist', 'RIGHT_PARENTHESIS'], ['LEFT_PARENTHESIS', 'RIGHT_PARENTHESIS']]),
  Rule('_maybe_symbol15', [['NEWLINE']]),
  Rule('_star_symbol16', [['__0_,', '_maybe_symbol15', '___star_symbol16_rest_0_0'], ['__0_,', '___star_symbol16_rest_0_0']]),
  Rule('pattern_arglist', [['pattern', '_star_symbol16'], ['pattern']]),
  Rule('primitive', [['LEFT_DOUBLE_ANGLE', 'NAME', 'RIGHT_DOUBLE_ANGLE']]),
  Rule('__lamb_source_rest_0_0', [['_maybe_symbol1', 'EOF'], ['EOF']]),
  Rule('__toplevel_expressions_rest_0_0', [['_star_symbol3'], []]),
  Rule('___star_symbol5_rest_0_0', [['expression', '_star_symbol5'], ['expression']]),
  Rule('___star_symbol14_rest_0_0', [['pattern', '_star_symbol14'], ['pattern']]),
  Rule('___star_symbol16_rest_0_0', [['pattern', '_star_symbol16'], ['pattern']])],
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
            if char == '.':
                state = 1
            elif char == ',':
                state = 2
            elif char == '\n':
                state = 3
            elif char == '\r':
                state = 3
            elif char == '\xce':
                state = 4
            elif char == '\xe2':
                state = 5
            elif char == '(':
                state = 6
            elif char == ')':
                state = 7
            elif char == '+':
                state = 8
            elif char == '-':
                state = 8
            elif '0' <= char <= '9':
                state = 9
            elif ':' <= char <= '\x9e':
                state = 10
            elif '\xac' <= char <= '\xcd':
                state = 10
            elif '\xe3' <= char <= '\xff':
                state = 10
            elif '\xcf' <= char <= '\xe1':
                state = 10
            elif '\x0e' <= char <= '\x1f':
                state = 10
            elif '\xa0' <= char <= '\xa9':
                state = 10
            elif '\x00' <= char <= '\x08':
                state = 10
            elif '$' <= char <= "'":
                state = 10
            elif char == '!':
                state = 10
            elif char == '"':
                state = 10
            elif char == '\x0b':
                state = 10
            elif char == '*':
                state = 10
            elif char == '/':
                state = 10
            elif char == '#':
                state = 11
            elif char == '\t':
                state = 12
            elif char == '\x0c':
                state = 12
            elif char == ' ':
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
            if '0' <= char <= '9':
                state = 17
            elif ':' <= char <= '\x9e':
                state = 10
            elif '\xac' <= char <= '\xe1':
                state = 10
            elif '\xe3' <= char <= '\xff':
                state = 10
            elif '\x0e' <= char <= '\x1f':
                state = 10
            elif '\xa0' <= char <= '\xa9':
                state = 10
            elif '\x00' <= char <= '\x08':
                state = 10
            elif '$' <= char <= "'":
                state = 10
            elif '-' <= char <= '/':
                state = 10
            elif char == '!':
                state = 10
            elif char == '"':
                state = 10
            elif char == '*':
                state = 10
            elif char == '+':
                state = 10
            elif char == '\x0b':
                state = 10
            else:
                break
        if state == 4:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 4
                return i
            if char == '\xbb':
                state = 36
            elif char == '\x9b':
                state = 37
            elif char == '\xbc':
                state = 38
            elif '-' <= char <= '\x9a':
                state = 10
            elif '\xbd' <= char <= '\xe1':
                state = 10
            elif '\xe3' <= char <= '\xff':
                state = 10
            elif '\x0e' <= char <= '\x1f':
                state = 10
            elif '\xac' <= char <= '\xba':
                state = 10
            elif '\xa0' <= char <= '\xa9':
                state = 10
            elif '\x00' <= char <= '\x08':
                state = 10
            elif '$' <= char <= "'":
                state = 10
            elif '\x9c' <= char <= '\x9e':
                state = 10
            elif char == '!':
                state = 10
            elif char == '"':
                state = 10
            elif char == '*':
                state = 10
            elif char == '+':
                state = 10
            elif char == '\x0b':
                state = 10
            else:
                break
        if state == 5:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 5
                return ~i
            if char == '\x86':
                state = 18
            elif char == '\x87':
                state = 19
            elif char == '\x89':
                state = 20
            elif char == '\x9f':
                state = 21
            elif char == '\x80':
                state = 22
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
            if '0' <= char <= '9':
                state = 15
            elif char == '.':
                state = 16
            elif ':' <= char <= '\x9e':
                state = 10
            elif '\xac' <= char <= '\xe1':
                state = 10
            elif '\xe3' <= char <= '\xff':
                state = 10
            elif '\x0e' <= char <= '\x1f':
                state = 10
            elif '\xa0' <= char <= '\xa9':
                state = 10
            elif '\x00' <= char <= '\x08':
                state = 10
            elif '$' <= char <= "'":
                state = 10
            elif char == '!':
                state = 10
            elif char == '"':
                state = 10
            elif char == '*':
                state = 10
            elif char == '+':
                state = 10
            elif char == '\x0b':
                state = 10
            elif char == '-':
                state = 10
            elif char == '/':
                state = 10
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
            if '0' <= char <= '9':
                state = 9
                continue
            elif char == '.':
                state = 13
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
                state = 10
                continue
            elif '\xac' <= char <= '\xe1':
                state = 10
                continue
            elif '\xe3' <= char <= '\xff':
                state = 10
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 10
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 10
                continue
            elif '\x00' <= char <= '\x08':
                state = 10
                continue
            elif '$' <= char <= "'":
                state = 10
                continue
            elif char == '!':
                state = 10
                continue
            elif char == '"':
                state = 10
                continue
            elif char == '*':
                state = 10
                continue
            elif char == '+':
                state = 10
                continue
            elif char == '\x0b':
                state = 10
                continue
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
            if '\x0b' <= char <= '\xff':
                state = 11
                continue
            elif '\x00' <= char <= '\t':
                state = 11
                continue
            else:
                break
        if state == 12:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 12
                return i
            if char == '\t':
                state = 12
                continue
            elif char == '\x0c':
                state = 12
                continue
            elif char == ' ':
                state = 12
                continue
            else:
                break
        if state == 13:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 13
                return ~i
            if '0' <= char <= '9':
                state = 14
            else:
                break
        if state == 14:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 14
                return i
            if '0' <= char <= '9':
                state = 14
                continue
            else:
                break
        if state == 15:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 15
                return i
            if '0' <= char <= '9':
                state = 15
                continue
            elif char == '.':
                state = 16
            elif ':' <= char <= '\x9e':
                state = 10
                continue
            elif '\xac' <= char <= '\xe1':
                state = 10
                continue
            elif '\xe3' <= char <= '\xff':
                state = 10
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 10
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 10
                continue
            elif '\x00' <= char <= '\x08':
                state = 10
                continue
            elif '$' <= char <= "'":
                state = 10
                continue
            elif char == '!':
                state = 10
                continue
            elif char == '"':
                state = 10
                continue
            elif char == '*':
                state = 10
                continue
            elif char == '+':
                state = 10
                continue
            elif char == '\x0b':
                state = 10
                continue
            elif char == '-':
                state = 10
                continue
            elif char == '/':
                state = 10
                continue
            else:
                break
        if state == 16:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 16
                return i
            if '0' <= char <= '9':
                state = 17
            elif ':' <= char <= '\x9e':
                state = 10
                continue
            elif '\xac' <= char <= '\xe1':
                state = 10
                continue
            elif '\xe3' <= char <= '\xff':
                state = 10
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 10
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 10
                continue
            elif '\x00' <= char <= '\x08':
                state = 10
                continue
            elif '$' <= char <= "'":
                state = 10
                continue
            elif '-' <= char <= '/':
                state = 10
                continue
            elif char == '!':
                state = 10
                continue
            elif char == '"':
                state = 10
                continue
            elif char == '*':
                state = 10
                continue
            elif char == '+':
                state = 10
                continue
            elif char == '\x0b':
                state = 10
                continue
            else:
                break
        if state == 17:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 17
                return i
            if '0' <= char <= '9':
                state = 17
                continue
            elif ':' <= char <= '\x9e':
                state = 10
                continue
            elif '\xac' <= char <= '\xe1':
                state = 10
                continue
            elif '\xe3' <= char <= '\xff':
                state = 10
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 10
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 10
                continue
            elif '\x00' <= char <= '\x08':
                state = 10
                continue
            elif '$' <= char <= "'":
                state = 10
                continue
            elif '-' <= char <= '/':
                state = 10
                continue
            elif char == '!':
                state = 10
                continue
            elif char == '"':
                state = 10
                continue
            elif char == '*':
                state = 10
                continue
            elif char == '+':
                state = 10
                continue
            elif char == '\x0b':
                state = 10
                continue
            else:
                break
        if state == 18:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 18
                return ~i
            if char == '\xa6':
                state = 35
            else:
                break
        if state == 19:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 19
                return ~i
            if char == '\x92':
                state = 34
            else:
                break
        if state == 20:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 20
                return ~i
            if char == '\x94':
                state = 33
            else:
                break
        if state == 21:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 21
                return ~i
            if char == '\xaa':
                state = 31
            elif char == '\xab':
                state = 32
            else:
                break
        if state == 22:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 22
                return ~i
            if char == '\x98':
                state = 23
            elif char == '\x9c':
                state = 24
            else:
                break
        if state == 23:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 23
                return ~i
            if char == '\xe2':
                state = 28
            elif '\x00' <= char <= '\x7f':
                state = 23
                continue
            elif '\x9a' <= char <= '\xe1':
                state = 23
                continue
            elif '\xe3' <= char <= '\xff':
                state = 23
                continue
            elif '\x81' <= char <= '\x98':
                state = 23
                continue
            else:
                break
        if state == 24:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 24
                return ~i
            if char == '\xe2':
                state = 25
            elif '\x00' <= char <= '\x7f':
                state = 24
                continue
            elif '\x9e' <= char <= '\xe1':
                state = 24
                continue
            elif '\xe3' <= char <= '\xff':
                state = 24
                continue
            elif '\x81' <= char <= '\x9c':
                state = 24
                continue
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
            if char == '\x9d':
                state = 27
            else:
                break
        if state == 28:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 28
                return ~i
            if char == '\x80':
                state = 29
            else:
                break
        if state == 29:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 29
                return ~i
            if char == '\x99':
                state = 30
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
            if '-' <= char <= '\x9e':
                state = 41
            elif '\xac' <= char <= '\xe1':
                state = 41
            elif '\xe3' <= char <= '\xff':
                state = 41
            elif '\x0e' <= char <= '\x1f':
                state = 41
            elif '\xa0' <= char <= '\xa9':
                state = 41
            elif '\x00' <= char <= '\x08':
                state = 41
            elif '$' <= char <= "'":
                state = 41
            elif char == '!':
                state = 41
            elif char == '"':
                state = 41
            elif char == '*':
                state = 41
            elif char == '+':
                state = 41
            elif char == '\x0b':
                state = 41
            elif char == '\t':
                state = 42
            elif char == '\n':
                state = 42
            elif char == '\x0c':
                state = 42
            elif char == '\r':
                state = 42
            elif char == '(':
                state = 42
            elif char == ')':
                state = 42
            elif char == '\xaa':
                state = 42
            elif char == '\xab':
                state = 42
            elif char == ' ':
                state = 42
            elif char == '#':
                state = 42
            elif char == ',':
                state = 42
            elif char == '\x9f':
                state = 42
            elif char == '\xe2':
                state = 42
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
            if '-' <= char <= '\x9e':
                state = 39
            elif '\xac' <= char <= '\xe1':
                state = 39
            elif '\xe3' <= char <= '\xff':
                state = 39
            elif '\x0e' <= char <= '\x1f':
                state = 39
            elif '\xa0' <= char <= '\xa9':
                state = 39
            elif '\x00' <= char <= '\x08':
                state = 39
            elif '$' <= char <= "'":
                state = 39
            elif char == '!':
                state = 39
            elif char == '"':
                state = 39
            elif char == '*':
                state = 39
            elif char == '+':
                state = 39
            elif char == '\x0b':
                state = 39
            elif char == '\t':
                state = 40
            elif char == '\n':
                state = 40
            elif char == '\x0c':
                state = 40
            elif char == '\r':
                state = 40
            elif char == '(':
                state = 40
            elif char == ')':
                state = 40
            elif char == '\xaa':
                state = 40
            elif char == '\xab':
                state = 40
            elif char == ' ':
                state = 40
            elif char == '#':
                state = 40
            elif char == ',':
                state = 40
            elif char == '\x9f':
                state = 40
            elif char == '\xe2':
                state = 40
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
            if '-' <= char <= '\x9e':
                state = 10
                continue
            elif '\xac' <= char <= '\xe1':
                state = 10
                continue
            elif '\xe3' <= char <= '\xff':
                state = 10
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 10
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 10
                continue
            elif '\x00' <= char <= '\x08':
                state = 10
                continue
            elif '$' <= char <= "'":
                state = 10
                continue
            elif char == '!':
                state = 10
                continue
            elif char == '"':
                state = 10
                continue
            elif char == '*':
                state = 10
                continue
            elif char == '+':
                state = 10
                continue
            elif char == '\x0b':
                state = 10
                continue
            else:
                break
        if state == 39:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 39
                return i
            if '-' <= char <= '\x9e':
                state = 10
                continue
            elif '\xac' <= char <= '\xe1':
                state = 10
                continue
            elif '\xe3' <= char <= '\xff':
                state = 10
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 10
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 10
                continue
            elif '\x00' <= char <= '\x08':
                state = 10
                continue
            elif '$' <= char <= "'":
                state = 10
                continue
            elif char == '!':
                state = 10
                continue
            elif char == '"':
                state = 10
                continue
            elif char == '*':
                state = 10
                continue
            elif char == '+':
                state = 10
                continue
            elif char == '\x0b':
                state = 10
                continue
            else:
                break
        if state == 41:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 41
                return i
            if '-' <= char <= '\x9e':
                state = 10
                continue
            elif '\xac' <= char <= '\xe1':
                state = 10
                continue
            elif '\xe3' <= char <= '\xff':
                state = 10
                continue
            elif '\x0e' <= char <= '\x1f':
                state = 10
                continue
            elif '\xa0' <= char <= '\xa9':
                state = 10
                continue
            elif '\x00' <= char <= '\x08':
                state = 10
                continue
            elif '$' <= char <= "'":
                state = 10
                continue
            elif char == '!':
                state = 10
                continue
            elif char == '"':
                state = 10
                continue
            elif char == '*':
                state = 10
                continue
            elif char == '+':
                state = 10
                continue
            elif char == '\x0b':
                state = 10
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
lexer = DummyLexer(recognize, DFA(43,
 {(0, '\x00'): 10,
  (0, '\x01'): 10,
  (0, '\x02'): 10,
  (0, '\x03'): 10,
  (0, '\x04'): 10,
  (0, '\x05'): 10,
  (0, '\x06'): 10,
  (0, '\x07'): 10,
  (0, '\x08'): 10,
  (0, '\t'): 12,
  (0, '\n'): 3,
  (0, '\x0b'): 10,
  (0, '\x0c'): 12,
  (0, '\r'): 3,
  (0, '\x0e'): 10,
  (0, '\x0f'): 10,
  (0, '\x10'): 10,
  (0, '\x11'): 10,
  (0, '\x12'): 10,
  (0, '\x13'): 10,
  (0, '\x14'): 10,
  (0, '\x15'): 10,
  (0, '\x16'): 10,
  (0, '\x17'): 10,
  (0, '\x18'): 10,
  (0, '\x19'): 10,
  (0, '\x1a'): 10,
  (0, '\x1b'): 10,
  (0, '\x1c'): 10,
  (0, '\x1d'): 10,
  (0, '\x1e'): 10,
  (0, '\x1f'): 10,
  (0, ' '): 12,
  (0, '!'): 10,
  (0, '"'): 10,
  (0, '#'): 11,
  (0, '$'): 10,
  (0, '%'): 10,
  (0, '&'): 10,
  (0, "'"): 10,
  (0, '('): 6,
  (0, ')'): 7,
  (0, '*'): 10,
  (0, '+'): 8,
  (0, ','): 2,
  (0, '-'): 8,
  (0, '.'): 1,
  (0, '/'): 10,
  (0, '0'): 9,
  (0, '1'): 9,
  (0, '2'): 9,
  (0, '3'): 9,
  (0, '4'): 9,
  (0, '5'): 9,
  (0, '6'): 9,
  (0, '7'): 9,
  (0, '8'): 9,
  (0, '9'): 9,
  (0, ':'): 10,
  (0, ';'): 10,
  (0, '<'): 10,
  (0, '='): 10,
  (0, '>'): 10,
  (0, '?'): 10,
  (0, '@'): 10,
  (0, 'A'): 10,
  (0, 'B'): 10,
  (0, 'C'): 10,
  (0, 'D'): 10,
  (0, 'E'): 10,
  (0, 'F'): 10,
  (0, 'G'): 10,
  (0, 'H'): 10,
  (0, 'I'): 10,
  (0, 'J'): 10,
  (0, 'K'): 10,
  (0, 'L'): 10,
  (0, 'M'): 10,
  (0, 'N'): 10,
  (0, 'O'): 10,
  (0, 'P'): 10,
  (0, 'Q'): 10,
  (0, 'R'): 10,
  (0, 'S'): 10,
  (0, 'T'): 10,
  (0, 'U'): 10,
  (0, 'V'): 10,
  (0, 'W'): 10,
  (0, 'X'): 10,
  (0, 'Y'): 10,
  (0, 'Z'): 10,
  (0, '['): 10,
  (0, '\\'): 10,
  (0, ']'): 10,
  (0, '^'): 10,
  (0, '_'): 10,
  (0, '`'): 10,
  (0, 'a'): 10,
  (0, 'b'): 10,
  (0, 'c'): 10,
  (0, 'd'): 10,
  (0, 'e'): 10,
  (0, 'f'): 10,
  (0, 'g'): 10,
  (0, 'h'): 10,
  (0, 'i'): 10,
  (0, 'j'): 10,
  (0, 'k'): 10,
  (0, 'l'): 10,
  (0, 'm'): 10,
  (0, 'n'): 10,
  (0, 'o'): 10,
  (0, 'p'): 10,
  (0, 'q'): 10,
  (0, 'r'): 10,
  (0, 's'): 10,
  (0, 't'): 10,
  (0, 'u'): 10,
  (0, 'v'): 10,
  (0, 'w'): 10,
  (0, 'x'): 10,
  (0, 'y'): 10,
  (0, 'z'): 10,
  (0, '{'): 10,
  (0, '|'): 10,
  (0, '}'): 10,
  (0, '~'): 10,
  (0, '\x7f'): 10,
  (0, '\x80'): 10,
  (0, '\x81'): 10,
  (0, '\x82'): 10,
  (0, '\x83'): 10,
  (0, '\x84'): 10,
  (0, '\x85'): 10,
  (0, '\x86'): 10,
  (0, '\x87'): 10,
  (0, '\x88'): 10,
  (0, '\x89'): 10,
  (0, '\x8a'): 10,
  (0, '\x8b'): 10,
  (0, '\x8c'): 10,
  (0, '\x8d'): 10,
  (0, '\x8e'): 10,
  (0, '\x8f'): 10,
  (0, '\x90'): 10,
  (0, '\x91'): 10,
  (0, '\x92'): 10,
  (0, '\x93'): 10,
  (0, '\x94'): 10,
  (0, '\x95'): 10,
  (0, '\x96'): 10,
  (0, '\x97'): 10,
  (0, '\x98'): 10,
  (0, '\x99'): 10,
  (0, '\x9a'): 10,
  (0, '\x9b'): 10,
  (0, '\x9c'): 10,
  (0, '\x9d'): 10,
  (0, '\x9e'): 10,
  (0, '\xa0'): 10,
  (0, '\xa1'): 10,
  (0, '\xa2'): 10,
  (0, '\xa3'): 10,
  (0, '\xa4'): 10,
  (0, '\xa5'): 10,
  (0, '\xa6'): 10,
  (0, '\xa7'): 10,
  (0, '\xa8'): 10,
  (0, '\xa9'): 10,
  (0, '\xac'): 10,
  (0, '\xad'): 10,
  (0, '\xae'): 10,
  (0, '\xaf'): 10,
  (0, '\xb0'): 10,
  (0, '\xb1'): 10,
  (0, '\xb2'): 10,
  (0, '\xb3'): 10,
  (0, '\xb4'): 10,
  (0, '\xb5'): 10,
  (0, '\xb6'): 10,
  (0, '\xb7'): 10,
  (0, '\xb8'): 10,
  (0, '\xb9'): 10,
  (0, '\xba'): 10,
  (0, '\xbb'): 10,
  (0, '\xbc'): 10,
  (0, '\xbd'): 10,
  (0, '\xbe'): 10,
  (0, '\xbf'): 10,
  (0, '\xc0'): 10,
  (0, '\xc1'): 10,
  (0, '\xc2'): 10,
  (0, '\xc3'): 10,
  (0, '\xc4'): 10,
  (0, '\xc5'): 10,
  (0, '\xc6'): 10,
  (0, '\xc7'): 10,
  (0, '\xc8'): 10,
  (0, '\xc9'): 10,
  (0, '\xca'): 10,
  (0, '\xcb'): 10,
  (0, '\xcc'): 10,
  (0, '\xcd'): 10,
  (0, '\xce'): 4,
  (0, '\xcf'): 10,
  (0, '\xd0'): 10,
  (0, '\xd1'): 10,
  (0, '\xd2'): 10,
  (0, '\xd3'): 10,
  (0, '\xd4'): 10,
  (0, '\xd5'): 10,
  (0, '\xd6'): 10,
  (0, '\xd7'): 10,
  (0, '\xd8'): 10,
  (0, '\xd9'): 10,
  (0, '\xda'): 10,
  (0, '\xdb'): 10,
  (0, '\xdc'): 10,
  (0, '\xdd'): 10,
  (0, '\xde'): 10,
  (0, '\xdf'): 10,
  (0, '\xe0'): 10,
  (0, '\xe1'): 10,
  (0, '\xe2'): 5,
  (0, '\xe3'): 10,
  (0, '\xe4'): 10,
  (0, '\xe5'): 10,
  (0, '\xe6'): 10,
  (0, '\xe7'): 10,
  (0, '\xe8'): 10,
  (0, '\xe9'): 10,
  (0, '\xea'): 10,
  (0, '\xeb'): 10,
  (0, '\xec'): 10,
  (0, '\xed'): 10,
  (0, '\xee'): 10,
  (0, '\xef'): 10,
  (0, '\xf0'): 10,
  (0, '\xf1'): 10,
  (0, '\xf2'): 10,
  (0, '\xf3'): 10,
  (0, '\xf4'): 10,
  (0, '\xf5'): 10,
  (0, '\xf6'): 10,
  (0, '\xf7'): 10,
  (0, '\xf8'): 10,
  (0, '\xf9'): 10,
  (0, '\xfa'): 10,
  (0, '\xfb'): 10,
  (0, '\xfc'): 10,
  (0, '\xfd'): 10,
  (0, '\xfe'): 10,
  (0, '\xff'): 10,
  (1, '\x00'): 10,
  (1, '\x01'): 10,
  (1, '\x02'): 10,
  (1, '\x03'): 10,
  (1, '\x04'): 10,
  (1, '\x05'): 10,
  (1, '\x06'): 10,
  (1, '\x07'): 10,
  (1, '\x08'): 10,
  (1, '\x0b'): 10,
  (1, '\x0e'): 10,
  (1, '\x0f'): 10,
  (1, '\x10'): 10,
  (1, '\x11'): 10,
  (1, '\x12'): 10,
  (1, '\x13'): 10,
  (1, '\x14'): 10,
  (1, '\x15'): 10,
  (1, '\x16'): 10,
  (1, '\x17'): 10,
  (1, '\x18'): 10,
  (1, '\x19'): 10,
  (1, '\x1a'): 10,
  (1, '\x1b'): 10,
  (1, '\x1c'): 10,
  (1, '\x1d'): 10,
  (1, '\x1e'): 10,
  (1, '\x1f'): 10,
  (1, '!'): 10,
  (1, '"'): 10,
  (1, '$'): 10,
  (1, '%'): 10,
  (1, '&'): 10,
  (1, "'"): 10,
  (1, '*'): 10,
  (1, '+'): 10,
  (1, '-'): 10,
  (1, '.'): 10,
  (1, '/'): 10,
  (1, '0'): 17,
  (1, '1'): 17,
  (1, '2'): 17,
  (1, '3'): 17,
  (1, '4'): 17,
  (1, '5'): 17,
  (1, '6'): 17,
  (1, '7'): 17,
  (1, '8'): 17,
  (1, '9'): 17,
  (1, ':'): 10,
  (1, ';'): 10,
  (1, '<'): 10,
  (1, '='): 10,
  (1, '>'): 10,
  (1, '?'): 10,
  (1, '@'): 10,
  (1, 'A'): 10,
  (1, 'B'): 10,
  (1, 'C'): 10,
  (1, 'D'): 10,
  (1, 'E'): 10,
  (1, 'F'): 10,
  (1, 'G'): 10,
  (1, 'H'): 10,
  (1, 'I'): 10,
  (1, 'J'): 10,
  (1, 'K'): 10,
  (1, 'L'): 10,
  (1, 'M'): 10,
  (1, 'N'): 10,
  (1, 'O'): 10,
  (1, 'P'): 10,
  (1, 'Q'): 10,
  (1, 'R'): 10,
  (1, 'S'): 10,
  (1, 'T'): 10,
  (1, 'U'): 10,
  (1, 'V'): 10,
  (1, 'W'): 10,
  (1, 'X'): 10,
  (1, 'Y'): 10,
  (1, 'Z'): 10,
  (1, '['): 10,
  (1, '\\'): 10,
  (1, ']'): 10,
  (1, '^'): 10,
  (1, '_'): 10,
  (1, '`'): 10,
  (1, 'a'): 10,
  (1, 'b'): 10,
  (1, 'c'): 10,
  (1, 'd'): 10,
  (1, 'e'): 10,
  (1, 'f'): 10,
  (1, 'g'): 10,
  (1, 'h'): 10,
  (1, 'i'): 10,
  (1, 'j'): 10,
  (1, 'k'): 10,
  (1, 'l'): 10,
  (1, 'm'): 10,
  (1, 'n'): 10,
  (1, 'o'): 10,
  (1, 'p'): 10,
  (1, 'q'): 10,
  (1, 'r'): 10,
  (1, 's'): 10,
  (1, 't'): 10,
  (1, 'u'): 10,
  (1, 'v'): 10,
  (1, 'w'): 10,
  (1, 'x'): 10,
  (1, 'y'): 10,
  (1, 'z'): 10,
  (1, '{'): 10,
  (1, '|'): 10,
  (1, '}'): 10,
  (1, '~'): 10,
  (1, '\x7f'): 10,
  (1, '\x80'): 10,
  (1, '\x81'): 10,
  (1, '\x82'): 10,
  (1, '\x83'): 10,
  (1, '\x84'): 10,
  (1, '\x85'): 10,
  (1, '\x86'): 10,
  (1, '\x87'): 10,
  (1, '\x88'): 10,
  (1, '\x89'): 10,
  (1, '\x8a'): 10,
  (1, '\x8b'): 10,
  (1, '\x8c'): 10,
  (1, '\x8d'): 10,
  (1, '\x8e'): 10,
  (1, '\x8f'): 10,
  (1, '\x90'): 10,
  (1, '\x91'): 10,
  (1, '\x92'): 10,
  (1, '\x93'): 10,
  (1, '\x94'): 10,
  (1, '\x95'): 10,
  (1, '\x96'): 10,
  (1, '\x97'): 10,
  (1, '\x98'): 10,
  (1, '\x99'): 10,
  (1, '\x9a'): 10,
  (1, '\x9b'): 10,
  (1, '\x9c'): 10,
  (1, '\x9d'): 10,
  (1, '\x9e'): 10,
  (1, '\xa0'): 10,
  (1, '\xa1'): 10,
  (1, '\xa2'): 10,
  (1, '\xa3'): 10,
  (1, '\xa4'): 10,
  (1, '\xa5'): 10,
  (1, '\xa6'): 10,
  (1, '\xa7'): 10,
  (1, '\xa8'): 10,
  (1, '\xa9'): 10,
  (1, '\xac'): 10,
  (1, '\xad'): 10,
  (1, '\xae'): 10,
  (1, '\xaf'): 10,
  (1, '\xb0'): 10,
  (1, '\xb1'): 10,
  (1, '\xb2'): 10,
  (1, '\xb3'): 10,
  (1, '\xb4'): 10,
  (1, '\xb5'): 10,
  (1, '\xb6'): 10,
  (1, '\xb7'): 10,
  (1, '\xb8'): 10,
  (1, '\xb9'): 10,
  (1, '\xba'): 10,
  (1, '\xbb'): 10,
  (1, '\xbc'): 10,
  (1, '\xbd'): 10,
  (1, '\xbe'): 10,
  (1, '\xbf'): 10,
  (1, '\xc0'): 10,
  (1, '\xc1'): 10,
  (1, '\xc2'): 10,
  (1, '\xc3'): 10,
  (1, '\xc4'): 10,
  (1, '\xc5'): 10,
  (1, '\xc6'): 10,
  (1, '\xc7'): 10,
  (1, '\xc8'): 10,
  (1, '\xc9'): 10,
  (1, '\xca'): 10,
  (1, '\xcb'): 10,
  (1, '\xcc'): 10,
  (1, '\xcd'): 10,
  (1, '\xce'): 10,
  (1, '\xcf'): 10,
  (1, '\xd0'): 10,
  (1, '\xd1'): 10,
  (1, '\xd2'): 10,
  (1, '\xd3'): 10,
  (1, '\xd4'): 10,
  (1, '\xd5'): 10,
  (1, '\xd6'): 10,
  (1, '\xd7'): 10,
  (1, '\xd8'): 10,
  (1, '\xd9'): 10,
  (1, '\xda'): 10,
  (1, '\xdb'): 10,
  (1, '\xdc'): 10,
  (1, '\xdd'): 10,
  (1, '\xde'): 10,
  (1, '\xdf'): 10,
  (1, '\xe0'): 10,
  (1, '\xe1'): 10,
  (1, '\xe3'): 10,
  (1, '\xe4'): 10,
  (1, '\xe5'): 10,
  (1, '\xe6'): 10,
  (1, '\xe7'): 10,
  (1, '\xe8'): 10,
  (1, '\xe9'): 10,
  (1, '\xea'): 10,
  (1, '\xeb'): 10,
  (1, '\xec'): 10,
  (1, '\xed'): 10,
  (1, '\xee'): 10,
  (1, '\xef'): 10,
  (1, '\xf0'): 10,
  (1, '\xf1'): 10,
  (1, '\xf2'): 10,
  (1, '\xf3'): 10,
  (1, '\xf4'): 10,
  (1, '\xf5'): 10,
  (1, '\xf6'): 10,
  (1, '\xf7'): 10,
  (1, '\xf8'): 10,
  (1, '\xf9'): 10,
  (1, '\xfa'): 10,
  (1, '\xfb'): 10,
  (1, '\xfc'): 10,
  (1, '\xfd'): 10,
  (1, '\xfe'): 10,
  (1, '\xff'): 10,
  (4, '\x00'): 10,
  (4, '\x01'): 10,
  (4, '\x02'): 10,
  (4, '\x03'): 10,
  (4, '\x04'): 10,
  (4, '\x05'): 10,
  (4, '\x06'): 10,
  (4, '\x07'): 10,
  (4, '\x08'): 10,
  (4, '\x0b'): 10,
  (4, '\x0e'): 10,
  (4, '\x0f'): 10,
  (4, '\x10'): 10,
  (4, '\x11'): 10,
  (4, '\x12'): 10,
  (4, '\x13'): 10,
  (4, '\x14'): 10,
  (4, '\x15'): 10,
  (4, '\x16'): 10,
  (4, '\x17'): 10,
  (4, '\x18'): 10,
  (4, '\x19'): 10,
  (4, '\x1a'): 10,
  (4, '\x1b'): 10,
  (4, '\x1c'): 10,
  (4, '\x1d'): 10,
  (4, '\x1e'): 10,
  (4, '\x1f'): 10,
  (4, '!'): 10,
  (4, '"'): 10,
  (4, '$'): 10,
  (4, '%'): 10,
  (4, '&'): 10,
  (4, "'"): 10,
  (4, '*'): 10,
  (4, '+'): 10,
  (4, '-'): 10,
  (4, '.'): 10,
  (4, '/'): 10,
  (4, '0'): 10,
  (4, '1'): 10,
  (4, '2'): 10,
  (4, '3'): 10,
  (4, '4'): 10,
  (4, '5'): 10,
  (4, '6'): 10,
  (4, '7'): 10,
  (4, '8'): 10,
  (4, '9'): 10,
  (4, ':'): 10,
  (4, ';'): 10,
  (4, '<'): 10,
  (4, '='): 10,
  (4, '>'): 10,
  (4, '?'): 10,
  (4, '@'): 10,
  (4, 'A'): 10,
  (4, 'B'): 10,
  (4, 'C'): 10,
  (4, 'D'): 10,
  (4, 'E'): 10,
  (4, 'F'): 10,
  (4, 'G'): 10,
  (4, 'H'): 10,
  (4, 'I'): 10,
  (4, 'J'): 10,
  (4, 'K'): 10,
  (4, 'L'): 10,
  (4, 'M'): 10,
  (4, 'N'): 10,
  (4, 'O'): 10,
  (4, 'P'): 10,
  (4, 'Q'): 10,
  (4, 'R'): 10,
  (4, 'S'): 10,
  (4, 'T'): 10,
  (4, 'U'): 10,
  (4, 'V'): 10,
  (4, 'W'): 10,
  (4, 'X'): 10,
  (4, 'Y'): 10,
  (4, 'Z'): 10,
  (4, '['): 10,
  (4, '\\'): 10,
  (4, ']'): 10,
  (4, '^'): 10,
  (4, '_'): 10,
  (4, '`'): 10,
  (4, 'a'): 10,
  (4, 'b'): 10,
  (4, 'c'): 10,
  (4, 'd'): 10,
  (4, 'e'): 10,
  (4, 'f'): 10,
  (4, 'g'): 10,
  (4, 'h'): 10,
  (4, 'i'): 10,
  (4, 'j'): 10,
  (4, 'k'): 10,
  (4, 'l'): 10,
  (4, 'm'): 10,
  (4, 'n'): 10,
  (4, 'o'): 10,
  (4, 'p'): 10,
  (4, 'q'): 10,
  (4, 'r'): 10,
  (4, 's'): 10,
  (4, 't'): 10,
  (4, 'u'): 10,
  (4, 'v'): 10,
  (4, 'w'): 10,
  (4, 'x'): 10,
  (4, 'y'): 10,
  (4, 'z'): 10,
  (4, '{'): 10,
  (4, '|'): 10,
  (4, '}'): 10,
  (4, '~'): 10,
  (4, '\x7f'): 10,
  (4, '\x80'): 10,
  (4, '\x81'): 10,
  (4, '\x82'): 10,
  (4, '\x83'): 10,
  (4, '\x84'): 10,
  (4, '\x85'): 10,
  (4, '\x86'): 10,
  (4, '\x87'): 10,
  (4, '\x88'): 10,
  (4, '\x89'): 10,
  (4, '\x8a'): 10,
  (4, '\x8b'): 10,
  (4, '\x8c'): 10,
  (4, '\x8d'): 10,
  (4, '\x8e'): 10,
  (4, '\x8f'): 10,
  (4, '\x90'): 10,
  (4, '\x91'): 10,
  (4, '\x92'): 10,
  (4, '\x93'): 10,
  (4, '\x94'): 10,
  (4, '\x95'): 10,
  (4, '\x96'): 10,
  (4, '\x97'): 10,
  (4, '\x98'): 10,
  (4, '\x99'): 10,
  (4, '\x9a'): 10,
  (4, '\x9b'): 37,
  (4, '\x9c'): 10,
  (4, '\x9d'): 10,
  (4, '\x9e'): 10,
  (4, '\xa0'): 10,
  (4, '\xa1'): 10,
  (4, '\xa2'): 10,
  (4, '\xa3'): 10,
  (4, '\xa4'): 10,
  (4, '\xa5'): 10,
  (4, '\xa6'): 10,
  (4, '\xa7'): 10,
  (4, '\xa8'): 10,
  (4, '\xa9'): 10,
  (4, '\xac'): 10,
  (4, '\xad'): 10,
  (4, '\xae'): 10,
  (4, '\xaf'): 10,
  (4, '\xb0'): 10,
  (4, '\xb1'): 10,
  (4, '\xb2'): 10,
  (4, '\xb3'): 10,
  (4, '\xb4'): 10,
  (4, '\xb5'): 10,
  (4, '\xb6'): 10,
  (4, '\xb7'): 10,
  (4, '\xb8'): 10,
  (4, '\xb9'): 10,
  (4, '\xba'): 10,
  (4, '\xbb'): 36,
  (4, '\xbc'): 38,
  (4, '\xbd'): 10,
  (4, '\xbe'): 10,
  (4, '\xbf'): 10,
  (4, '\xc0'): 10,
  (4, '\xc1'): 10,
  (4, '\xc2'): 10,
  (4, '\xc3'): 10,
  (4, '\xc4'): 10,
  (4, '\xc5'): 10,
  (4, '\xc6'): 10,
  (4, '\xc7'): 10,
  (4, '\xc8'): 10,
  (4, '\xc9'): 10,
  (4, '\xca'): 10,
  (4, '\xcb'): 10,
  (4, '\xcc'): 10,
  (4, '\xcd'): 10,
  (4, '\xce'): 10,
  (4, '\xcf'): 10,
  (4, '\xd0'): 10,
  (4, '\xd1'): 10,
  (4, '\xd2'): 10,
  (4, '\xd3'): 10,
  (4, '\xd4'): 10,
  (4, '\xd5'): 10,
  (4, '\xd6'): 10,
  (4, '\xd7'): 10,
  (4, '\xd8'): 10,
  (4, '\xd9'): 10,
  (4, '\xda'): 10,
  (4, '\xdb'): 10,
  (4, '\xdc'): 10,
  (4, '\xdd'): 10,
  (4, '\xde'): 10,
  (4, '\xdf'): 10,
  (4, '\xe0'): 10,
  (4, '\xe1'): 10,
  (4, '\xe3'): 10,
  (4, '\xe4'): 10,
  (4, '\xe5'): 10,
  (4, '\xe6'): 10,
  (4, '\xe7'): 10,
  (4, '\xe8'): 10,
  (4, '\xe9'): 10,
  (4, '\xea'): 10,
  (4, '\xeb'): 10,
  (4, '\xec'): 10,
  (4, '\xed'): 10,
  (4, '\xee'): 10,
  (4, '\xef'): 10,
  (4, '\xf0'): 10,
  (4, '\xf1'): 10,
  (4, '\xf2'): 10,
  (4, '\xf3'): 10,
  (4, '\xf4'): 10,
  (4, '\xf5'): 10,
  (4, '\xf6'): 10,
  (4, '\xf7'): 10,
  (4, '\xf8'): 10,
  (4, '\xf9'): 10,
  (4, '\xfa'): 10,
  (4, '\xfb'): 10,
  (4, '\xfc'): 10,
  (4, '\xfd'): 10,
  (4, '\xfe'): 10,
  (4, '\xff'): 10,
  (5, '\x80'): 22,
  (5, '\x86'): 18,
  (5, '\x87'): 19,
  (5, '\x89'): 20,
  (5, '\x9f'): 21,
  (8, '\x00'): 10,
  (8, '\x01'): 10,
  (8, '\x02'): 10,
  (8, '\x03'): 10,
  (8, '\x04'): 10,
  (8, '\x05'): 10,
  (8, '\x06'): 10,
  (8, '\x07'): 10,
  (8, '\x08'): 10,
  (8, '\x0b'): 10,
  (8, '\x0e'): 10,
  (8, '\x0f'): 10,
  (8, '\x10'): 10,
  (8, '\x11'): 10,
  (8, '\x12'): 10,
  (8, '\x13'): 10,
  (8, '\x14'): 10,
  (8, '\x15'): 10,
  (8, '\x16'): 10,
  (8, '\x17'): 10,
  (8, '\x18'): 10,
  (8, '\x19'): 10,
  (8, '\x1a'): 10,
  (8, '\x1b'): 10,
  (8, '\x1c'): 10,
  (8, '\x1d'): 10,
  (8, '\x1e'): 10,
  (8, '\x1f'): 10,
  (8, '!'): 10,
  (8, '"'): 10,
  (8, '$'): 10,
  (8, '%'): 10,
  (8, '&'): 10,
  (8, "'"): 10,
  (8, '*'): 10,
  (8, '+'): 10,
  (8, '-'): 10,
  (8, '.'): 16,
  (8, '/'): 10,
  (8, '0'): 15,
  (8, '1'): 15,
  (8, '2'): 15,
  (8, '3'): 15,
  (8, '4'): 15,
  (8, '5'): 15,
  (8, '6'): 15,
  (8, '7'): 15,
  (8, '8'): 15,
  (8, '9'): 15,
  (8, ':'): 10,
  (8, ';'): 10,
  (8, '<'): 10,
  (8, '='): 10,
  (8, '>'): 10,
  (8, '?'): 10,
  (8, '@'): 10,
  (8, 'A'): 10,
  (8, 'B'): 10,
  (8, 'C'): 10,
  (8, 'D'): 10,
  (8, 'E'): 10,
  (8, 'F'): 10,
  (8, 'G'): 10,
  (8, 'H'): 10,
  (8, 'I'): 10,
  (8, 'J'): 10,
  (8, 'K'): 10,
  (8, 'L'): 10,
  (8, 'M'): 10,
  (8, 'N'): 10,
  (8, 'O'): 10,
  (8, 'P'): 10,
  (8, 'Q'): 10,
  (8, 'R'): 10,
  (8, 'S'): 10,
  (8, 'T'): 10,
  (8, 'U'): 10,
  (8, 'V'): 10,
  (8, 'W'): 10,
  (8, 'X'): 10,
  (8, 'Y'): 10,
  (8, 'Z'): 10,
  (8, '['): 10,
  (8, '\\'): 10,
  (8, ']'): 10,
  (8, '^'): 10,
  (8, '_'): 10,
  (8, '`'): 10,
  (8, 'a'): 10,
  (8, 'b'): 10,
  (8, 'c'): 10,
  (8, 'd'): 10,
  (8, 'e'): 10,
  (8, 'f'): 10,
  (8, 'g'): 10,
  (8, 'h'): 10,
  (8, 'i'): 10,
  (8, 'j'): 10,
  (8, 'k'): 10,
  (8, 'l'): 10,
  (8, 'm'): 10,
  (8, 'n'): 10,
  (8, 'o'): 10,
  (8, 'p'): 10,
  (8, 'q'): 10,
  (8, 'r'): 10,
  (8, 's'): 10,
  (8, 't'): 10,
  (8, 'u'): 10,
  (8, 'v'): 10,
  (8, 'w'): 10,
  (8, 'x'): 10,
  (8, 'y'): 10,
  (8, 'z'): 10,
  (8, '{'): 10,
  (8, '|'): 10,
  (8, '}'): 10,
  (8, '~'): 10,
  (8, '\x7f'): 10,
  (8, '\x80'): 10,
  (8, '\x81'): 10,
  (8, '\x82'): 10,
  (8, '\x83'): 10,
  (8, '\x84'): 10,
  (8, '\x85'): 10,
  (8, '\x86'): 10,
  (8, '\x87'): 10,
  (8, '\x88'): 10,
  (8, '\x89'): 10,
  (8, '\x8a'): 10,
  (8, '\x8b'): 10,
  (8, '\x8c'): 10,
  (8, '\x8d'): 10,
  (8, '\x8e'): 10,
  (8, '\x8f'): 10,
  (8, '\x90'): 10,
  (8, '\x91'): 10,
  (8, '\x92'): 10,
  (8, '\x93'): 10,
  (8, '\x94'): 10,
  (8, '\x95'): 10,
  (8, '\x96'): 10,
  (8, '\x97'): 10,
  (8, '\x98'): 10,
  (8, '\x99'): 10,
  (8, '\x9a'): 10,
  (8, '\x9b'): 10,
  (8, '\x9c'): 10,
  (8, '\x9d'): 10,
  (8, '\x9e'): 10,
  (8, '\xa0'): 10,
  (8, '\xa1'): 10,
  (8, '\xa2'): 10,
  (8, '\xa3'): 10,
  (8, '\xa4'): 10,
  (8, '\xa5'): 10,
  (8, '\xa6'): 10,
  (8, '\xa7'): 10,
  (8, '\xa8'): 10,
  (8, '\xa9'): 10,
  (8, '\xac'): 10,
  (8, '\xad'): 10,
  (8, '\xae'): 10,
  (8, '\xaf'): 10,
  (8, '\xb0'): 10,
  (8, '\xb1'): 10,
  (8, '\xb2'): 10,
  (8, '\xb3'): 10,
  (8, '\xb4'): 10,
  (8, '\xb5'): 10,
  (8, '\xb6'): 10,
  (8, '\xb7'): 10,
  (8, '\xb8'): 10,
  (8, '\xb9'): 10,
  (8, '\xba'): 10,
  (8, '\xbb'): 10,
  (8, '\xbc'): 10,
  (8, '\xbd'): 10,
  (8, '\xbe'): 10,
  (8, '\xbf'): 10,
  (8, '\xc0'): 10,
  (8, '\xc1'): 10,
  (8, '\xc2'): 10,
  (8, '\xc3'): 10,
  (8, '\xc4'): 10,
  (8, '\xc5'): 10,
  (8, '\xc6'): 10,
  (8, '\xc7'): 10,
  (8, '\xc8'): 10,
  (8, '\xc9'): 10,
  (8, '\xca'): 10,
  (8, '\xcb'): 10,
  (8, '\xcc'): 10,
  (8, '\xcd'): 10,
  (8, '\xce'): 10,
  (8, '\xcf'): 10,
  (8, '\xd0'): 10,
  (8, '\xd1'): 10,
  (8, '\xd2'): 10,
  (8, '\xd3'): 10,
  (8, '\xd4'): 10,
  (8, '\xd5'): 10,
  (8, '\xd6'): 10,
  (8, '\xd7'): 10,
  (8, '\xd8'): 10,
  (8, '\xd9'): 10,
  (8, '\xda'): 10,
  (8, '\xdb'): 10,
  (8, '\xdc'): 10,
  (8, '\xdd'): 10,
  (8, '\xde'): 10,
  (8, '\xdf'): 10,
  (8, '\xe0'): 10,
  (8, '\xe1'): 10,
  (8, '\xe3'): 10,
  (8, '\xe4'): 10,
  (8, '\xe5'): 10,
  (8, '\xe6'): 10,
  (8, '\xe7'): 10,
  (8, '\xe8'): 10,
  (8, '\xe9'): 10,
  (8, '\xea'): 10,
  (8, '\xeb'): 10,
  (8, '\xec'): 10,
  (8, '\xed'): 10,
  (8, '\xee'): 10,
  (8, '\xef'): 10,
  (8, '\xf0'): 10,
  (8, '\xf1'): 10,
  (8, '\xf2'): 10,
  (8, '\xf3'): 10,
  (8, '\xf4'): 10,
  (8, '\xf5'): 10,
  (8, '\xf6'): 10,
  (8, '\xf7'): 10,
  (8, '\xf8'): 10,
  (8, '\xf9'): 10,
  (8, '\xfa'): 10,
  (8, '\xfb'): 10,
  (8, '\xfc'): 10,
  (8, '\xfd'): 10,
  (8, '\xfe'): 10,
  (8, '\xff'): 10,
  (9, '.'): 13,
  (9, '0'): 9,
  (9, '1'): 9,
  (9, '2'): 9,
  (9, '3'): 9,
  (9, '4'): 9,
  (9, '5'): 9,
  (9, '6'): 9,
  (9, '7'): 9,
  (9, '8'): 9,
  (9, '9'): 9,
  (10, '\x00'): 10,
  (10, '\x01'): 10,
  (10, '\x02'): 10,
  (10, '\x03'): 10,
  (10, '\x04'): 10,
  (10, '\x05'): 10,
  (10, '\x06'): 10,
  (10, '\x07'): 10,
  (10, '\x08'): 10,
  (10, '\x0b'): 10,
  (10, '\x0e'): 10,
  (10, '\x0f'): 10,
  (10, '\x10'): 10,
  (10, '\x11'): 10,
  (10, '\x12'): 10,
  (10, '\x13'): 10,
  (10, '\x14'): 10,
  (10, '\x15'): 10,
  (10, '\x16'): 10,
  (10, '\x17'): 10,
  (10, '\x18'): 10,
  (10, '\x19'): 10,
  (10, '\x1a'): 10,
  (10, '\x1b'): 10,
  (10, '\x1c'): 10,
  (10, '\x1d'): 10,
  (10, '\x1e'): 10,
  (10, '\x1f'): 10,
  (10, '!'): 10,
  (10, '"'): 10,
  (10, '$'): 10,
  (10, '%'): 10,
  (10, '&'): 10,
  (10, "'"): 10,
  (10, '*'): 10,
  (10, '+'): 10,
  (10, '-'): 10,
  (10, '.'): 10,
  (10, '/'): 10,
  (10, '0'): 10,
  (10, '1'): 10,
  (10, '2'): 10,
  (10, '3'): 10,
  (10, '4'): 10,
  (10, '5'): 10,
  (10, '6'): 10,
  (10, '7'): 10,
  (10, '8'): 10,
  (10, '9'): 10,
  (10, ':'): 10,
  (10, ';'): 10,
  (10, '<'): 10,
  (10, '='): 10,
  (10, '>'): 10,
  (10, '?'): 10,
  (10, '@'): 10,
  (10, 'A'): 10,
  (10, 'B'): 10,
  (10, 'C'): 10,
  (10, 'D'): 10,
  (10, 'E'): 10,
  (10, 'F'): 10,
  (10, 'G'): 10,
  (10, 'H'): 10,
  (10, 'I'): 10,
  (10, 'J'): 10,
  (10, 'K'): 10,
  (10, 'L'): 10,
  (10, 'M'): 10,
  (10, 'N'): 10,
  (10, 'O'): 10,
  (10, 'P'): 10,
  (10, 'Q'): 10,
  (10, 'R'): 10,
  (10, 'S'): 10,
  (10, 'T'): 10,
  (10, 'U'): 10,
  (10, 'V'): 10,
  (10, 'W'): 10,
  (10, 'X'): 10,
  (10, 'Y'): 10,
  (10, 'Z'): 10,
  (10, '['): 10,
  (10, '\\'): 10,
  (10, ']'): 10,
  (10, '^'): 10,
  (10, '_'): 10,
  (10, '`'): 10,
  (10, 'a'): 10,
  (10, 'b'): 10,
  (10, 'c'): 10,
  (10, 'd'): 10,
  (10, 'e'): 10,
  (10, 'f'): 10,
  (10, 'g'): 10,
  (10, 'h'): 10,
  (10, 'i'): 10,
  (10, 'j'): 10,
  (10, 'k'): 10,
  (10, 'l'): 10,
  (10, 'm'): 10,
  (10, 'n'): 10,
  (10, 'o'): 10,
  (10, 'p'): 10,
  (10, 'q'): 10,
  (10, 'r'): 10,
  (10, 's'): 10,
  (10, 't'): 10,
  (10, 'u'): 10,
  (10, 'v'): 10,
  (10, 'w'): 10,
  (10, 'x'): 10,
  (10, 'y'): 10,
  (10, 'z'): 10,
  (10, '{'): 10,
  (10, '|'): 10,
  (10, '}'): 10,
  (10, '~'): 10,
  (10, '\x7f'): 10,
  (10, '\x80'): 10,
  (10, '\x81'): 10,
  (10, '\x82'): 10,
  (10, '\x83'): 10,
  (10, '\x84'): 10,
  (10, '\x85'): 10,
  (10, '\x86'): 10,
  (10, '\x87'): 10,
  (10, '\x88'): 10,
  (10, '\x89'): 10,
  (10, '\x8a'): 10,
  (10, '\x8b'): 10,
  (10, '\x8c'): 10,
  (10, '\x8d'): 10,
  (10, '\x8e'): 10,
  (10, '\x8f'): 10,
  (10, '\x90'): 10,
  (10, '\x91'): 10,
  (10, '\x92'): 10,
  (10, '\x93'): 10,
  (10, '\x94'): 10,
  (10, '\x95'): 10,
  (10, '\x96'): 10,
  (10, '\x97'): 10,
  (10, '\x98'): 10,
  (10, '\x99'): 10,
  (10, '\x9a'): 10,
  (10, '\x9b'): 10,
  (10, '\x9c'): 10,
  (10, '\x9d'): 10,
  (10, '\x9e'): 10,
  (10, '\xa0'): 10,
  (10, '\xa1'): 10,
  (10, '\xa2'): 10,
  (10, '\xa3'): 10,
  (10, '\xa4'): 10,
  (10, '\xa5'): 10,
  (10, '\xa6'): 10,
  (10, '\xa7'): 10,
  (10, '\xa8'): 10,
  (10, '\xa9'): 10,
  (10, '\xac'): 10,
  (10, '\xad'): 10,
  (10, '\xae'): 10,
  (10, '\xaf'): 10,
  (10, '\xb0'): 10,
  (10, '\xb1'): 10,
  (10, '\xb2'): 10,
  (10, '\xb3'): 10,
  (10, '\xb4'): 10,
  (10, '\xb5'): 10,
  (10, '\xb6'): 10,
  (10, '\xb7'): 10,
  (10, '\xb8'): 10,
  (10, '\xb9'): 10,
  (10, '\xba'): 10,
  (10, '\xbb'): 10,
  (10, '\xbc'): 10,
  (10, '\xbd'): 10,
  (10, '\xbe'): 10,
  (10, '\xbf'): 10,
  (10, '\xc0'): 10,
  (10, '\xc1'): 10,
  (10, '\xc2'): 10,
  (10, '\xc3'): 10,
  (10, '\xc4'): 10,
  (10, '\xc5'): 10,
  (10, '\xc6'): 10,
  (10, '\xc7'): 10,
  (10, '\xc8'): 10,
  (10, '\xc9'): 10,
  (10, '\xca'): 10,
  (10, '\xcb'): 10,
  (10, '\xcc'): 10,
  (10, '\xcd'): 10,
  (10, '\xce'): 10,
  (10, '\xcf'): 10,
  (10, '\xd0'): 10,
  (10, '\xd1'): 10,
  (10, '\xd2'): 10,
  (10, '\xd3'): 10,
  (10, '\xd4'): 10,
  (10, '\xd5'): 10,
  (10, '\xd6'): 10,
  (10, '\xd7'): 10,
  (10, '\xd8'): 10,
  (10, '\xd9'): 10,
  (10, '\xda'): 10,
  (10, '\xdb'): 10,
  (10, '\xdc'): 10,
  (10, '\xdd'): 10,
  (10, '\xde'): 10,
  (10, '\xdf'): 10,
  (10, '\xe0'): 10,
  (10, '\xe1'): 10,
  (10, '\xe3'): 10,
  (10, '\xe4'): 10,
  (10, '\xe5'): 10,
  (10, '\xe6'): 10,
  (10, '\xe7'): 10,
  (10, '\xe8'): 10,
  (10, '\xe9'): 10,
  (10, '\xea'): 10,
  (10, '\xeb'): 10,
  (10, '\xec'): 10,
  (10, '\xed'): 10,
  (10, '\xee'): 10,
  (10, '\xef'): 10,
  (10, '\xf0'): 10,
  (10, '\xf1'): 10,
  (10, '\xf2'): 10,
  (10, '\xf3'): 10,
  (10, '\xf4'): 10,
  (10, '\xf5'): 10,
  (10, '\xf6'): 10,
  (10, '\xf7'): 10,
  (10, '\xf8'): 10,
  (10, '\xf9'): 10,
  (10, '\xfa'): 10,
  (10, '\xfb'): 10,
  (10, '\xfc'): 10,
  (10, '\xfd'): 10,
  (10, '\xfe'): 10,
  (10, '\xff'): 10,
  (11, '\x00'): 11,
  (11, '\x01'): 11,
  (11, '\x02'): 11,
  (11, '\x03'): 11,
  (11, '\x04'): 11,
  (11, '\x05'): 11,
  (11, '\x06'): 11,
  (11, '\x07'): 11,
  (11, '\x08'): 11,
  (11, '\t'): 11,
  (11, '\x0b'): 11,
  (11, '\x0c'): 11,
  (11, '\r'): 11,
  (11, '\x0e'): 11,
  (11, '\x0f'): 11,
  (11, '\x10'): 11,
  (11, '\x11'): 11,
  (11, '\x12'): 11,
  (11, '\x13'): 11,
  (11, '\x14'): 11,
  (11, '\x15'): 11,
  (11, '\x16'): 11,
  (11, '\x17'): 11,
  (11, '\x18'): 11,
  (11, '\x19'): 11,
  (11, '\x1a'): 11,
  (11, '\x1b'): 11,
  (11, '\x1c'): 11,
  (11, '\x1d'): 11,
  (11, '\x1e'): 11,
  (11, '\x1f'): 11,
  (11, ' '): 11,
  (11, '!'): 11,
  (11, '"'): 11,
  (11, '#'): 11,
  (11, '$'): 11,
  (11, '%'): 11,
  (11, '&'): 11,
  (11, "'"): 11,
  (11, '('): 11,
  (11, ')'): 11,
  (11, '*'): 11,
  (11, '+'): 11,
  (11, ','): 11,
  (11, '-'): 11,
  (11, '.'): 11,
  (11, '/'): 11,
  (11, '0'): 11,
  (11, '1'): 11,
  (11, '2'): 11,
  (11, '3'): 11,
  (11, '4'): 11,
  (11, '5'): 11,
  (11, '6'): 11,
  (11, '7'): 11,
  (11, '8'): 11,
  (11, '9'): 11,
  (11, ':'): 11,
  (11, ';'): 11,
  (11, '<'): 11,
  (11, '='): 11,
  (11, '>'): 11,
  (11, '?'): 11,
  (11, '@'): 11,
  (11, 'A'): 11,
  (11, 'B'): 11,
  (11, 'C'): 11,
  (11, 'D'): 11,
  (11, 'E'): 11,
  (11, 'F'): 11,
  (11, 'G'): 11,
  (11, 'H'): 11,
  (11, 'I'): 11,
  (11, 'J'): 11,
  (11, 'K'): 11,
  (11, 'L'): 11,
  (11, 'M'): 11,
  (11, 'N'): 11,
  (11, 'O'): 11,
  (11, 'P'): 11,
  (11, 'Q'): 11,
  (11, 'R'): 11,
  (11, 'S'): 11,
  (11, 'T'): 11,
  (11, 'U'): 11,
  (11, 'V'): 11,
  (11, 'W'): 11,
  (11, 'X'): 11,
  (11, 'Y'): 11,
  (11, 'Z'): 11,
  (11, '['): 11,
  (11, '\\'): 11,
  (11, ']'): 11,
  (11, '^'): 11,
  (11, '_'): 11,
  (11, '`'): 11,
  (11, 'a'): 11,
  (11, 'b'): 11,
  (11, 'c'): 11,
  (11, 'd'): 11,
  (11, 'e'): 11,
  (11, 'f'): 11,
  (11, 'g'): 11,
  (11, 'h'): 11,
  (11, 'i'): 11,
  (11, 'j'): 11,
  (11, 'k'): 11,
  (11, 'l'): 11,
  (11, 'm'): 11,
  (11, 'n'): 11,
  (11, 'o'): 11,
  (11, 'p'): 11,
  (11, 'q'): 11,
  (11, 'r'): 11,
  (11, 's'): 11,
  (11, 't'): 11,
  (11, 'u'): 11,
  (11, 'v'): 11,
  (11, 'w'): 11,
  (11, 'x'): 11,
  (11, 'y'): 11,
  (11, 'z'): 11,
  (11, '{'): 11,
  (11, '|'): 11,
  (11, '}'): 11,
  (11, '~'): 11,
  (11, '\x7f'): 11,
  (11, '\x80'): 11,
  (11, '\x81'): 11,
  (11, '\x82'): 11,
  (11, '\x83'): 11,
  (11, '\x84'): 11,
  (11, '\x85'): 11,
  (11, '\x86'): 11,
  (11, '\x87'): 11,
  (11, '\x88'): 11,
  (11, '\x89'): 11,
  (11, '\x8a'): 11,
  (11, '\x8b'): 11,
  (11, '\x8c'): 11,
  (11, '\x8d'): 11,
  (11, '\x8e'): 11,
  (11, '\x8f'): 11,
  (11, '\x90'): 11,
  (11, '\x91'): 11,
  (11, '\x92'): 11,
  (11, '\x93'): 11,
  (11, '\x94'): 11,
  (11, '\x95'): 11,
  (11, '\x96'): 11,
  (11, '\x97'): 11,
  (11, '\x98'): 11,
  (11, '\x99'): 11,
  (11, '\x9a'): 11,
  (11, '\x9b'): 11,
  (11, '\x9c'): 11,
  (11, '\x9d'): 11,
  (11, '\x9e'): 11,
  (11, '\x9f'): 11,
  (11, '\xa0'): 11,
  (11, '\xa1'): 11,
  (11, '\xa2'): 11,
  (11, '\xa3'): 11,
  (11, '\xa4'): 11,
  (11, '\xa5'): 11,
  (11, '\xa6'): 11,
  (11, '\xa7'): 11,
  (11, '\xa8'): 11,
  (11, '\xa9'): 11,
  (11, '\xaa'): 11,
  (11, '\xab'): 11,
  (11, '\xac'): 11,
  (11, '\xad'): 11,
  (11, '\xae'): 11,
  (11, '\xaf'): 11,
  (11, '\xb0'): 11,
  (11, '\xb1'): 11,
  (11, '\xb2'): 11,
  (11, '\xb3'): 11,
  (11, '\xb4'): 11,
  (11, '\xb5'): 11,
  (11, '\xb6'): 11,
  (11, '\xb7'): 11,
  (11, '\xb8'): 11,
  (11, '\xb9'): 11,
  (11, '\xba'): 11,
  (11, '\xbb'): 11,
  (11, '\xbc'): 11,
  (11, '\xbd'): 11,
  (11, '\xbe'): 11,
  (11, '\xbf'): 11,
  (11, '\xc0'): 11,
  (11, '\xc1'): 11,
  (11, '\xc2'): 11,
  (11, '\xc3'): 11,
  (11, '\xc4'): 11,
  (11, '\xc5'): 11,
  (11, '\xc6'): 11,
  (11, '\xc7'): 11,
  (11, '\xc8'): 11,
  (11, '\xc9'): 11,
  (11, '\xca'): 11,
  (11, '\xcb'): 11,
  (11, '\xcc'): 11,
  (11, '\xcd'): 11,
  (11, '\xce'): 11,
  (11, '\xcf'): 11,
  (11, '\xd0'): 11,
  (11, '\xd1'): 11,
  (11, '\xd2'): 11,
  (11, '\xd3'): 11,
  (11, '\xd4'): 11,
  (11, '\xd5'): 11,
  (11, '\xd6'): 11,
  (11, '\xd7'): 11,
  (11, '\xd8'): 11,
  (11, '\xd9'): 11,
  (11, '\xda'): 11,
  (11, '\xdb'): 11,
  (11, '\xdc'): 11,
  (11, '\xdd'): 11,
  (11, '\xde'): 11,
  (11, '\xdf'): 11,
  (11, '\xe0'): 11,
  (11, '\xe1'): 11,
  (11, '\xe2'): 11,
  (11, '\xe3'): 11,
  (11, '\xe4'): 11,
  (11, '\xe5'): 11,
  (11, '\xe6'): 11,
  (11, '\xe7'): 11,
  (11, '\xe8'): 11,
  (11, '\xe9'): 11,
  (11, '\xea'): 11,
  (11, '\xeb'): 11,
  (11, '\xec'): 11,
  (11, '\xed'): 11,
  (11, '\xee'): 11,
  (11, '\xef'): 11,
  (11, '\xf0'): 11,
  (11, '\xf1'): 11,
  (11, '\xf2'): 11,
  (11, '\xf3'): 11,
  (11, '\xf4'): 11,
  (11, '\xf5'): 11,
  (11, '\xf6'): 11,
  (11, '\xf7'): 11,
  (11, '\xf8'): 11,
  (11, '\xf9'): 11,
  (11, '\xfa'): 11,
  (11, '\xfb'): 11,
  (11, '\xfc'): 11,
  (11, '\xfd'): 11,
  (11, '\xfe'): 11,
  (11, '\xff'): 11,
  (12, '\t'): 12,
  (12, '\x0c'): 12,
  (12, ' '): 12,
  (13, '0'): 14,
  (13, '1'): 14,
  (13, '2'): 14,
  (13, '3'): 14,
  (13, '4'): 14,
  (13, '5'): 14,
  (13, '6'): 14,
  (13, '7'): 14,
  (13, '8'): 14,
  (13, '9'): 14,
  (14, '0'): 14,
  (14, '1'): 14,
  (14, '2'): 14,
  (14, '3'): 14,
  (14, '4'): 14,
  (14, '5'): 14,
  (14, '6'): 14,
  (14, '7'): 14,
  (14, '8'): 14,
  (14, '9'): 14,
  (15, '\x00'): 10,
  (15, '\x01'): 10,
  (15, '\x02'): 10,
  (15, '\x03'): 10,
  (15, '\x04'): 10,
  (15, '\x05'): 10,
  (15, '\x06'): 10,
  (15, '\x07'): 10,
  (15, '\x08'): 10,
  (15, '\x0b'): 10,
  (15, '\x0e'): 10,
  (15, '\x0f'): 10,
  (15, '\x10'): 10,
  (15, '\x11'): 10,
  (15, '\x12'): 10,
  (15, '\x13'): 10,
  (15, '\x14'): 10,
  (15, '\x15'): 10,
  (15, '\x16'): 10,
  (15, '\x17'): 10,
  (15, '\x18'): 10,
  (15, '\x19'): 10,
  (15, '\x1a'): 10,
  (15, '\x1b'): 10,
  (15, '\x1c'): 10,
  (15, '\x1d'): 10,
  (15, '\x1e'): 10,
  (15, '\x1f'): 10,
  (15, '!'): 10,
  (15, '"'): 10,
  (15, '$'): 10,
  (15, '%'): 10,
  (15, '&'): 10,
  (15, "'"): 10,
  (15, '*'): 10,
  (15, '+'): 10,
  (15, '-'): 10,
  (15, '.'): 16,
  (15, '/'): 10,
  (15, '0'): 15,
  (15, '1'): 15,
  (15, '2'): 15,
  (15, '3'): 15,
  (15, '4'): 15,
  (15, '5'): 15,
  (15, '6'): 15,
  (15, '7'): 15,
  (15, '8'): 15,
  (15, '9'): 15,
  (15, ':'): 10,
  (15, ';'): 10,
  (15, '<'): 10,
  (15, '='): 10,
  (15, '>'): 10,
  (15, '?'): 10,
  (15, '@'): 10,
  (15, 'A'): 10,
  (15, 'B'): 10,
  (15, 'C'): 10,
  (15, 'D'): 10,
  (15, 'E'): 10,
  (15, 'F'): 10,
  (15, 'G'): 10,
  (15, 'H'): 10,
  (15, 'I'): 10,
  (15, 'J'): 10,
  (15, 'K'): 10,
  (15, 'L'): 10,
  (15, 'M'): 10,
  (15, 'N'): 10,
  (15, 'O'): 10,
  (15, 'P'): 10,
  (15, 'Q'): 10,
  (15, 'R'): 10,
  (15, 'S'): 10,
  (15, 'T'): 10,
  (15, 'U'): 10,
  (15, 'V'): 10,
  (15, 'W'): 10,
  (15, 'X'): 10,
  (15, 'Y'): 10,
  (15, 'Z'): 10,
  (15, '['): 10,
  (15, '\\'): 10,
  (15, ']'): 10,
  (15, '^'): 10,
  (15, '_'): 10,
  (15, '`'): 10,
  (15, 'a'): 10,
  (15, 'b'): 10,
  (15, 'c'): 10,
  (15, 'd'): 10,
  (15, 'e'): 10,
  (15, 'f'): 10,
  (15, 'g'): 10,
  (15, 'h'): 10,
  (15, 'i'): 10,
  (15, 'j'): 10,
  (15, 'k'): 10,
  (15, 'l'): 10,
  (15, 'm'): 10,
  (15, 'n'): 10,
  (15, 'o'): 10,
  (15, 'p'): 10,
  (15, 'q'): 10,
  (15, 'r'): 10,
  (15, 's'): 10,
  (15, 't'): 10,
  (15, 'u'): 10,
  (15, 'v'): 10,
  (15, 'w'): 10,
  (15, 'x'): 10,
  (15, 'y'): 10,
  (15, 'z'): 10,
  (15, '{'): 10,
  (15, '|'): 10,
  (15, '}'): 10,
  (15, '~'): 10,
  (15, '\x7f'): 10,
  (15, '\x80'): 10,
  (15, '\x81'): 10,
  (15, '\x82'): 10,
  (15, '\x83'): 10,
  (15, '\x84'): 10,
  (15, '\x85'): 10,
  (15, '\x86'): 10,
  (15, '\x87'): 10,
  (15, '\x88'): 10,
  (15, '\x89'): 10,
  (15, '\x8a'): 10,
  (15, '\x8b'): 10,
  (15, '\x8c'): 10,
  (15, '\x8d'): 10,
  (15, '\x8e'): 10,
  (15, '\x8f'): 10,
  (15, '\x90'): 10,
  (15, '\x91'): 10,
  (15, '\x92'): 10,
  (15, '\x93'): 10,
  (15, '\x94'): 10,
  (15, '\x95'): 10,
  (15, '\x96'): 10,
  (15, '\x97'): 10,
  (15, '\x98'): 10,
  (15, '\x99'): 10,
  (15, '\x9a'): 10,
  (15, '\x9b'): 10,
  (15, '\x9c'): 10,
  (15, '\x9d'): 10,
  (15, '\x9e'): 10,
  (15, '\xa0'): 10,
  (15, '\xa1'): 10,
  (15, '\xa2'): 10,
  (15, '\xa3'): 10,
  (15, '\xa4'): 10,
  (15, '\xa5'): 10,
  (15, '\xa6'): 10,
  (15, '\xa7'): 10,
  (15, '\xa8'): 10,
  (15, '\xa9'): 10,
  (15, '\xac'): 10,
  (15, '\xad'): 10,
  (15, '\xae'): 10,
  (15, '\xaf'): 10,
  (15, '\xb0'): 10,
  (15, '\xb1'): 10,
  (15, '\xb2'): 10,
  (15, '\xb3'): 10,
  (15, '\xb4'): 10,
  (15, '\xb5'): 10,
  (15, '\xb6'): 10,
  (15, '\xb7'): 10,
  (15, '\xb8'): 10,
  (15, '\xb9'): 10,
  (15, '\xba'): 10,
  (15, '\xbb'): 10,
  (15, '\xbc'): 10,
  (15, '\xbd'): 10,
  (15, '\xbe'): 10,
  (15, '\xbf'): 10,
  (15, '\xc0'): 10,
  (15, '\xc1'): 10,
  (15, '\xc2'): 10,
  (15, '\xc3'): 10,
  (15, '\xc4'): 10,
  (15, '\xc5'): 10,
  (15, '\xc6'): 10,
  (15, '\xc7'): 10,
  (15, '\xc8'): 10,
  (15, '\xc9'): 10,
  (15, '\xca'): 10,
  (15, '\xcb'): 10,
  (15, '\xcc'): 10,
  (15, '\xcd'): 10,
  (15, '\xce'): 10,
  (15, '\xcf'): 10,
  (15, '\xd0'): 10,
  (15, '\xd1'): 10,
  (15, '\xd2'): 10,
  (15, '\xd3'): 10,
  (15, '\xd4'): 10,
  (15, '\xd5'): 10,
  (15, '\xd6'): 10,
  (15, '\xd7'): 10,
  (15, '\xd8'): 10,
  (15, '\xd9'): 10,
  (15, '\xda'): 10,
  (15, '\xdb'): 10,
  (15, '\xdc'): 10,
  (15, '\xdd'): 10,
  (15, '\xde'): 10,
  (15, '\xdf'): 10,
  (15, '\xe0'): 10,
  (15, '\xe1'): 10,
  (15, '\xe3'): 10,
  (15, '\xe4'): 10,
  (15, '\xe5'): 10,
  (15, '\xe6'): 10,
  (15, '\xe7'): 10,
  (15, '\xe8'): 10,
  (15, '\xe9'): 10,
  (15, '\xea'): 10,
  (15, '\xeb'): 10,
  (15, '\xec'): 10,
  (15, '\xed'): 10,
  (15, '\xee'): 10,
  (15, '\xef'): 10,
  (15, '\xf0'): 10,
  (15, '\xf1'): 10,
  (15, '\xf2'): 10,
  (15, '\xf3'): 10,
  (15, '\xf4'): 10,
  (15, '\xf5'): 10,
  (15, '\xf6'): 10,
  (15, '\xf7'): 10,
  (15, '\xf8'): 10,
  (15, '\xf9'): 10,
  (15, '\xfa'): 10,
  (15, '\xfb'): 10,
  (15, '\xfc'): 10,
  (15, '\xfd'): 10,
  (15, '\xfe'): 10,
  (15, '\xff'): 10,
  (16, '\x00'): 10,
  (16, '\x01'): 10,
  (16, '\x02'): 10,
  (16, '\x03'): 10,
  (16, '\x04'): 10,
  (16, '\x05'): 10,
  (16, '\x06'): 10,
  (16, '\x07'): 10,
  (16, '\x08'): 10,
  (16, '\x0b'): 10,
  (16, '\x0e'): 10,
  (16, '\x0f'): 10,
  (16, '\x10'): 10,
  (16, '\x11'): 10,
  (16, '\x12'): 10,
  (16, '\x13'): 10,
  (16, '\x14'): 10,
  (16, '\x15'): 10,
  (16, '\x16'): 10,
  (16, '\x17'): 10,
  (16, '\x18'): 10,
  (16, '\x19'): 10,
  (16, '\x1a'): 10,
  (16, '\x1b'): 10,
  (16, '\x1c'): 10,
  (16, '\x1d'): 10,
  (16, '\x1e'): 10,
  (16, '\x1f'): 10,
  (16, '!'): 10,
  (16, '"'): 10,
  (16, '$'): 10,
  (16, '%'): 10,
  (16, '&'): 10,
  (16, "'"): 10,
  (16, '*'): 10,
  (16, '+'): 10,
  (16, '-'): 10,
  (16, '.'): 10,
  (16, '/'): 10,
  (16, '0'): 17,
  (16, '1'): 17,
  (16, '2'): 17,
  (16, '3'): 17,
  (16, '4'): 17,
  (16, '5'): 17,
  (16, '6'): 17,
  (16, '7'): 17,
  (16, '8'): 17,
  (16, '9'): 17,
  (16, ':'): 10,
  (16, ';'): 10,
  (16, '<'): 10,
  (16, '='): 10,
  (16, '>'): 10,
  (16, '?'): 10,
  (16, '@'): 10,
  (16, 'A'): 10,
  (16, 'B'): 10,
  (16, 'C'): 10,
  (16, 'D'): 10,
  (16, 'E'): 10,
  (16, 'F'): 10,
  (16, 'G'): 10,
  (16, 'H'): 10,
  (16, 'I'): 10,
  (16, 'J'): 10,
  (16, 'K'): 10,
  (16, 'L'): 10,
  (16, 'M'): 10,
  (16, 'N'): 10,
  (16, 'O'): 10,
  (16, 'P'): 10,
  (16, 'Q'): 10,
  (16, 'R'): 10,
  (16, 'S'): 10,
  (16, 'T'): 10,
  (16, 'U'): 10,
  (16, 'V'): 10,
  (16, 'W'): 10,
  (16, 'X'): 10,
  (16, 'Y'): 10,
  (16, 'Z'): 10,
  (16, '['): 10,
  (16, '\\'): 10,
  (16, ']'): 10,
  (16, '^'): 10,
  (16, '_'): 10,
  (16, '`'): 10,
  (16, 'a'): 10,
  (16, 'b'): 10,
  (16, 'c'): 10,
  (16, 'd'): 10,
  (16, 'e'): 10,
  (16, 'f'): 10,
  (16, 'g'): 10,
  (16, 'h'): 10,
  (16, 'i'): 10,
  (16, 'j'): 10,
  (16, 'k'): 10,
  (16, 'l'): 10,
  (16, 'm'): 10,
  (16, 'n'): 10,
  (16, 'o'): 10,
  (16, 'p'): 10,
  (16, 'q'): 10,
  (16, 'r'): 10,
  (16, 's'): 10,
  (16, 't'): 10,
  (16, 'u'): 10,
  (16, 'v'): 10,
  (16, 'w'): 10,
  (16, 'x'): 10,
  (16, 'y'): 10,
  (16, 'z'): 10,
  (16, '{'): 10,
  (16, '|'): 10,
  (16, '}'): 10,
  (16, '~'): 10,
  (16, '\x7f'): 10,
  (16, '\x80'): 10,
  (16, '\x81'): 10,
  (16, '\x82'): 10,
  (16, '\x83'): 10,
  (16, '\x84'): 10,
  (16, '\x85'): 10,
  (16, '\x86'): 10,
  (16, '\x87'): 10,
  (16, '\x88'): 10,
  (16, '\x89'): 10,
  (16, '\x8a'): 10,
  (16, '\x8b'): 10,
  (16, '\x8c'): 10,
  (16, '\x8d'): 10,
  (16, '\x8e'): 10,
  (16, '\x8f'): 10,
  (16, '\x90'): 10,
  (16, '\x91'): 10,
  (16, '\x92'): 10,
  (16, '\x93'): 10,
  (16, '\x94'): 10,
  (16, '\x95'): 10,
  (16, '\x96'): 10,
  (16, '\x97'): 10,
  (16, '\x98'): 10,
  (16, '\x99'): 10,
  (16, '\x9a'): 10,
  (16, '\x9b'): 10,
  (16, '\x9c'): 10,
  (16, '\x9d'): 10,
  (16, '\x9e'): 10,
  (16, '\xa0'): 10,
  (16, '\xa1'): 10,
  (16, '\xa2'): 10,
  (16, '\xa3'): 10,
  (16, '\xa4'): 10,
  (16, '\xa5'): 10,
  (16, '\xa6'): 10,
  (16, '\xa7'): 10,
  (16, '\xa8'): 10,
  (16, '\xa9'): 10,
  (16, '\xac'): 10,
  (16, '\xad'): 10,
  (16, '\xae'): 10,
  (16, '\xaf'): 10,
  (16, '\xb0'): 10,
  (16, '\xb1'): 10,
  (16, '\xb2'): 10,
  (16, '\xb3'): 10,
  (16, '\xb4'): 10,
  (16, '\xb5'): 10,
  (16, '\xb6'): 10,
  (16, '\xb7'): 10,
  (16, '\xb8'): 10,
  (16, '\xb9'): 10,
  (16, '\xba'): 10,
  (16, '\xbb'): 10,
  (16, '\xbc'): 10,
  (16, '\xbd'): 10,
  (16, '\xbe'): 10,
  (16, '\xbf'): 10,
  (16, '\xc0'): 10,
  (16, '\xc1'): 10,
  (16, '\xc2'): 10,
  (16, '\xc3'): 10,
  (16, '\xc4'): 10,
  (16, '\xc5'): 10,
  (16, '\xc6'): 10,
  (16, '\xc7'): 10,
  (16, '\xc8'): 10,
  (16, '\xc9'): 10,
  (16, '\xca'): 10,
  (16, '\xcb'): 10,
  (16, '\xcc'): 10,
  (16, '\xcd'): 10,
  (16, '\xce'): 10,
  (16, '\xcf'): 10,
  (16, '\xd0'): 10,
  (16, '\xd1'): 10,
  (16, '\xd2'): 10,
  (16, '\xd3'): 10,
  (16, '\xd4'): 10,
  (16, '\xd5'): 10,
  (16, '\xd6'): 10,
  (16, '\xd7'): 10,
  (16, '\xd8'): 10,
  (16, '\xd9'): 10,
  (16, '\xda'): 10,
  (16, '\xdb'): 10,
  (16, '\xdc'): 10,
  (16, '\xdd'): 10,
  (16, '\xde'): 10,
  (16, '\xdf'): 10,
  (16, '\xe0'): 10,
  (16, '\xe1'): 10,
  (16, '\xe3'): 10,
  (16, '\xe4'): 10,
  (16, '\xe5'): 10,
  (16, '\xe6'): 10,
  (16, '\xe7'): 10,
  (16, '\xe8'): 10,
  (16, '\xe9'): 10,
  (16, '\xea'): 10,
  (16, '\xeb'): 10,
  (16, '\xec'): 10,
  (16, '\xed'): 10,
  (16, '\xee'): 10,
  (16, '\xef'): 10,
  (16, '\xf0'): 10,
  (16, '\xf1'): 10,
  (16, '\xf2'): 10,
  (16, '\xf3'): 10,
  (16, '\xf4'): 10,
  (16, '\xf5'): 10,
  (16, '\xf6'): 10,
  (16, '\xf7'): 10,
  (16, '\xf8'): 10,
  (16, '\xf9'): 10,
  (16, '\xfa'): 10,
  (16, '\xfb'): 10,
  (16, '\xfc'): 10,
  (16, '\xfd'): 10,
  (16, '\xfe'): 10,
  (16, '\xff'): 10,
  (17, '\x00'): 10,
  (17, '\x01'): 10,
  (17, '\x02'): 10,
  (17, '\x03'): 10,
  (17, '\x04'): 10,
  (17, '\x05'): 10,
  (17, '\x06'): 10,
  (17, '\x07'): 10,
  (17, '\x08'): 10,
  (17, '\x0b'): 10,
  (17, '\x0e'): 10,
  (17, '\x0f'): 10,
  (17, '\x10'): 10,
  (17, '\x11'): 10,
  (17, '\x12'): 10,
  (17, '\x13'): 10,
  (17, '\x14'): 10,
  (17, '\x15'): 10,
  (17, '\x16'): 10,
  (17, '\x17'): 10,
  (17, '\x18'): 10,
  (17, '\x19'): 10,
  (17, '\x1a'): 10,
  (17, '\x1b'): 10,
  (17, '\x1c'): 10,
  (17, '\x1d'): 10,
  (17, '\x1e'): 10,
  (17, '\x1f'): 10,
  (17, '!'): 10,
  (17, '"'): 10,
  (17, '$'): 10,
  (17, '%'): 10,
  (17, '&'): 10,
  (17, "'"): 10,
  (17, '*'): 10,
  (17, '+'): 10,
  (17, '-'): 10,
  (17, '.'): 10,
  (17, '/'): 10,
  (17, '0'): 17,
  (17, '1'): 17,
  (17, '2'): 17,
  (17, '3'): 17,
  (17, '4'): 17,
  (17, '5'): 17,
  (17, '6'): 17,
  (17, '7'): 17,
  (17, '8'): 17,
  (17, '9'): 17,
  (17, ':'): 10,
  (17, ';'): 10,
  (17, '<'): 10,
  (17, '='): 10,
  (17, '>'): 10,
  (17, '?'): 10,
  (17, '@'): 10,
  (17, 'A'): 10,
  (17, 'B'): 10,
  (17, 'C'): 10,
  (17, 'D'): 10,
  (17, 'E'): 10,
  (17, 'F'): 10,
  (17, 'G'): 10,
  (17, 'H'): 10,
  (17, 'I'): 10,
  (17, 'J'): 10,
  (17, 'K'): 10,
  (17, 'L'): 10,
  (17, 'M'): 10,
  (17, 'N'): 10,
  (17, 'O'): 10,
  (17, 'P'): 10,
  (17, 'Q'): 10,
  (17, 'R'): 10,
  (17, 'S'): 10,
  (17, 'T'): 10,
  (17, 'U'): 10,
  (17, 'V'): 10,
  (17, 'W'): 10,
  (17, 'X'): 10,
  (17, 'Y'): 10,
  (17, 'Z'): 10,
  (17, '['): 10,
  (17, '\\'): 10,
  (17, ']'): 10,
  (17, '^'): 10,
  (17, '_'): 10,
  (17, '`'): 10,
  (17, 'a'): 10,
  (17, 'b'): 10,
  (17, 'c'): 10,
  (17, 'd'): 10,
  (17, 'e'): 10,
  (17, 'f'): 10,
  (17, 'g'): 10,
  (17, 'h'): 10,
  (17, 'i'): 10,
  (17, 'j'): 10,
  (17, 'k'): 10,
  (17, 'l'): 10,
  (17, 'm'): 10,
  (17, 'n'): 10,
  (17, 'o'): 10,
  (17, 'p'): 10,
  (17, 'q'): 10,
  (17, 'r'): 10,
  (17, 's'): 10,
  (17, 't'): 10,
  (17, 'u'): 10,
  (17, 'v'): 10,
  (17, 'w'): 10,
  (17, 'x'): 10,
  (17, 'y'): 10,
  (17, 'z'): 10,
  (17, '{'): 10,
  (17, '|'): 10,
  (17, '}'): 10,
  (17, '~'): 10,
  (17, '\x7f'): 10,
  (17, '\x80'): 10,
  (17, '\x81'): 10,
  (17, '\x82'): 10,
  (17, '\x83'): 10,
  (17, '\x84'): 10,
  (17, '\x85'): 10,
  (17, '\x86'): 10,
  (17, '\x87'): 10,
  (17, '\x88'): 10,
  (17, '\x89'): 10,
  (17, '\x8a'): 10,
  (17, '\x8b'): 10,
  (17, '\x8c'): 10,
  (17, '\x8d'): 10,
  (17, '\x8e'): 10,
  (17, '\x8f'): 10,
  (17, '\x90'): 10,
  (17, '\x91'): 10,
  (17, '\x92'): 10,
  (17, '\x93'): 10,
  (17, '\x94'): 10,
  (17, '\x95'): 10,
  (17, '\x96'): 10,
  (17, '\x97'): 10,
  (17, '\x98'): 10,
  (17, '\x99'): 10,
  (17, '\x9a'): 10,
  (17, '\x9b'): 10,
  (17, '\x9c'): 10,
  (17, '\x9d'): 10,
  (17, '\x9e'): 10,
  (17, '\xa0'): 10,
  (17, '\xa1'): 10,
  (17, '\xa2'): 10,
  (17, '\xa3'): 10,
  (17, '\xa4'): 10,
  (17, '\xa5'): 10,
  (17, '\xa6'): 10,
  (17, '\xa7'): 10,
  (17, '\xa8'): 10,
  (17, '\xa9'): 10,
  (17, '\xac'): 10,
  (17, '\xad'): 10,
  (17, '\xae'): 10,
  (17, '\xaf'): 10,
  (17, '\xb0'): 10,
  (17, '\xb1'): 10,
  (17, '\xb2'): 10,
  (17, '\xb3'): 10,
  (17, '\xb4'): 10,
  (17, '\xb5'): 10,
  (17, '\xb6'): 10,
  (17, '\xb7'): 10,
  (17, '\xb8'): 10,
  (17, '\xb9'): 10,
  (17, '\xba'): 10,
  (17, '\xbb'): 10,
  (17, '\xbc'): 10,
  (17, '\xbd'): 10,
  (17, '\xbe'): 10,
  (17, '\xbf'): 10,
  (17, '\xc0'): 10,
  (17, '\xc1'): 10,
  (17, '\xc2'): 10,
  (17, '\xc3'): 10,
  (17, '\xc4'): 10,
  (17, '\xc5'): 10,
  (17, '\xc6'): 10,
  (17, '\xc7'): 10,
  (17, '\xc8'): 10,
  (17, '\xc9'): 10,
  (17, '\xca'): 10,
  (17, '\xcb'): 10,
  (17, '\xcc'): 10,
  (17, '\xcd'): 10,
  (17, '\xce'): 10,
  (17, '\xcf'): 10,
  (17, '\xd0'): 10,
  (17, '\xd1'): 10,
  (17, '\xd2'): 10,
  (17, '\xd3'): 10,
  (17, '\xd4'): 10,
  (17, '\xd5'): 10,
  (17, '\xd6'): 10,
  (17, '\xd7'): 10,
  (17, '\xd8'): 10,
  (17, '\xd9'): 10,
  (17, '\xda'): 10,
  (17, '\xdb'): 10,
  (17, '\xdc'): 10,
  (17, '\xdd'): 10,
  (17, '\xde'): 10,
  (17, '\xdf'): 10,
  (17, '\xe0'): 10,
  (17, '\xe1'): 10,
  (17, '\xe3'): 10,
  (17, '\xe4'): 10,
  (17, '\xe5'): 10,
  (17, '\xe6'): 10,
  (17, '\xe7'): 10,
  (17, '\xe8'): 10,
  (17, '\xe9'): 10,
  (17, '\xea'): 10,
  (17, '\xeb'): 10,
  (17, '\xec'): 10,
  (17, '\xed'): 10,
  (17, '\xee'): 10,
  (17, '\xef'): 10,
  (17, '\xf0'): 10,
  (17, '\xf1'): 10,
  (17, '\xf2'): 10,
  (17, '\xf3'): 10,
  (17, '\xf4'): 10,
  (17, '\xf5'): 10,
  (17, '\xf6'): 10,
  (17, '\xf7'): 10,
  (17, '\xf8'): 10,
  (17, '\xf9'): 10,
  (17, '\xfa'): 10,
  (17, '\xfb'): 10,
  (17, '\xfc'): 10,
  (17, '\xfd'): 10,
  (17, '\xfe'): 10,
  (17, '\xff'): 10,
  (18, '\xa6'): 35,
  (19, '\x92'): 34,
  (20, '\x94'): 33,
  (21, '\xaa'): 31,
  (21, '\xab'): 32,
  (22, '\x98'): 23,
  (22, '\x9c'): 24,
  (23, '\x00'): 23,
  (23, '\x01'): 23,
  (23, '\x02'): 23,
  (23, '\x03'): 23,
  (23, '\x04'): 23,
  (23, '\x05'): 23,
  (23, '\x06'): 23,
  (23, '\x07'): 23,
  (23, '\x08'): 23,
  (23, '\t'): 23,
  (23, '\n'): 23,
  (23, '\x0b'): 23,
  (23, '\x0c'): 23,
  (23, '\r'): 23,
  (23, '\x0e'): 23,
  (23, '\x0f'): 23,
  (23, '\x10'): 23,
  (23, '\x11'): 23,
  (23, '\x12'): 23,
  (23, '\x13'): 23,
  (23, '\x14'): 23,
  (23, '\x15'): 23,
  (23, '\x16'): 23,
  (23, '\x17'): 23,
  (23, '\x18'): 23,
  (23, '\x19'): 23,
  (23, '\x1a'): 23,
  (23, '\x1b'): 23,
  (23, '\x1c'): 23,
  (23, '\x1d'): 23,
  (23, '\x1e'): 23,
  (23, '\x1f'): 23,
  (23, ' '): 23,
  (23, '!'): 23,
  (23, '"'): 23,
  (23, '#'): 23,
  (23, '$'): 23,
  (23, '%'): 23,
  (23, '&'): 23,
  (23, "'"): 23,
  (23, '('): 23,
  (23, ')'): 23,
  (23, '*'): 23,
  (23, '+'): 23,
  (23, ','): 23,
  (23, '-'): 23,
  (23, '.'): 23,
  (23, '/'): 23,
  (23, '0'): 23,
  (23, '1'): 23,
  (23, '2'): 23,
  (23, '3'): 23,
  (23, '4'): 23,
  (23, '5'): 23,
  (23, '6'): 23,
  (23, '7'): 23,
  (23, '8'): 23,
  (23, '9'): 23,
  (23, ':'): 23,
  (23, ';'): 23,
  (23, '<'): 23,
  (23, '='): 23,
  (23, '>'): 23,
  (23, '?'): 23,
  (23, '@'): 23,
  (23, 'A'): 23,
  (23, 'B'): 23,
  (23, 'C'): 23,
  (23, 'D'): 23,
  (23, 'E'): 23,
  (23, 'F'): 23,
  (23, 'G'): 23,
  (23, 'H'): 23,
  (23, 'I'): 23,
  (23, 'J'): 23,
  (23, 'K'): 23,
  (23, 'L'): 23,
  (23, 'M'): 23,
  (23, 'N'): 23,
  (23, 'O'): 23,
  (23, 'P'): 23,
  (23, 'Q'): 23,
  (23, 'R'): 23,
  (23, 'S'): 23,
  (23, 'T'): 23,
  (23, 'U'): 23,
  (23, 'V'): 23,
  (23, 'W'): 23,
  (23, 'X'): 23,
  (23, 'Y'): 23,
  (23, 'Z'): 23,
  (23, '['): 23,
  (23, '\\'): 23,
  (23, ']'): 23,
  (23, '^'): 23,
  (23, '_'): 23,
  (23, '`'): 23,
  (23, 'a'): 23,
  (23, 'b'): 23,
  (23, 'c'): 23,
  (23, 'd'): 23,
  (23, 'e'): 23,
  (23, 'f'): 23,
  (23, 'g'): 23,
  (23, 'h'): 23,
  (23, 'i'): 23,
  (23, 'j'): 23,
  (23, 'k'): 23,
  (23, 'l'): 23,
  (23, 'm'): 23,
  (23, 'n'): 23,
  (23, 'o'): 23,
  (23, 'p'): 23,
  (23, 'q'): 23,
  (23, 'r'): 23,
  (23, 's'): 23,
  (23, 't'): 23,
  (23, 'u'): 23,
  (23, 'v'): 23,
  (23, 'w'): 23,
  (23, 'x'): 23,
  (23, 'y'): 23,
  (23, 'z'): 23,
  (23, '{'): 23,
  (23, '|'): 23,
  (23, '}'): 23,
  (23, '~'): 23,
  (23, '\x7f'): 23,
  (23, '\x81'): 23,
  (23, '\x82'): 23,
  (23, '\x83'): 23,
  (23, '\x84'): 23,
  (23, '\x85'): 23,
  (23, '\x86'): 23,
  (23, '\x87'): 23,
  (23, '\x88'): 23,
  (23, '\x89'): 23,
  (23, '\x8a'): 23,
  (23, '\x8b'): 23,
  (23, '\x8c'): 23,
  (23, '\x8d'): 23,
  (23, '\x8e'): 23,
  (23, '\x8f'): 23,
  (23, '\x90'): 23,
  (23, '\x91'): 23,
  (23, '\x92'): 23,
  (23, '\x93'): 23,
  (23, '\x94'): 23,
  (23, '\x95'): 23,
  (23, '\x96'): 23,
  (23, '\x97'): 23,
  (23, '\x98'): 23,
  (23, '\x9a'): 23,
  (23, '\x9b'): 23,
  (23, '\x9c'): 23,
  (23, '\x9d'): 23,
  (23, '\x9e'): 23,
  (23, '\x9f'): 23,
  (23, '\xa0'): 23,
  (23, '\xa1'): 23,
  (23, '\xa2'): 23,
  (23, '\xa3'): 23,
  (23, '\xa4'): 23,
  (23, '\xa5'): 23,
  (23, '\xa6'): 23,
  (23, '\xa7'): 23,
  (23, '\xa8'): 23,
  (23, '\xa9'): 23,
  (23, '\xaa'): 23,
  (23, '\xab'): 23,
  (23, '\xac'): 23,
  (23, '\xad'): 23,
  (23, '\xae'): 23,
  (23, '\xaf'): 23,
  (23, '\xb0'): 23,
  (23, '\xb1'): 23,
  (23, '\xb2'): 23,
  (23, '\xb3'): 23,
  (23, '\xb4'): 23,
  (23, '\xb5'): 23,
  (23, '\xb6'): 23,
  (23, '\xb7'): 23,
  (23, '\xb8'): 23,
  (23, '\xb9'): 23,
  (23, '\xba'): 23,
  (23, '\xbb'): 23,
  (23, '\xbc'): 23,
  (23, '\xbd'): 23,
  (23, '\xbe'): 23,
  (23, '\xbf'): 23,
  (23, '\xc0'): 23,
  (23, '\xc1'): 23,
  (23, '\xc2'): 23,
  (23, '\xc3'): 23,
  (23, '\xc4'): 23,
  (23, '\xc5'): 23,
  (23, '\xc6'): 23,
  (23, '\xc7'): 23,
  (23, '\xc8'): 23,
  (23, '\xc9'): 23,
  (23, '\xca'): 23,
  (23, '\xcb'): 23,
  (23, '\xcc'): 23,
  (23, '\xcd'): 23,
  (23, '\xce'): 23,
  (23, '\xcf'): 23,
  (23, '\xd0'): 23,
  (23, '\xd1'): 23,
  (23, '\xd2'): 23,
  (23, '\xd3'): 23,
  (23, '\xd4'): 23,
  (23, '\xd5'): 23,
  (23, '\xd6'): 23,
  (23, '\xd7'): 23,
  (23, '\xd8'): 23,
  (23, '\xd9'): 23,
  (23, '\xda'): 23,
  (23, '\xdb'): 23,
  (23, '\xdc'): 23,
  (23, '\xdd'): 23,
  (23, '\xde'): 23,
  (23, '\xdf'): 23,
  (23, '\xe0'): 23,
  (23, '\xe1'): 23,
  (23, '\xe2'): 28,
  (23, '\xe3'): 23,
  (23, '\xe4'): 23,
  (23, '\xe5'): 23,
  (23, '\xe6'): 23,
  (23, '\xe7'): 23,
  (23, '\xe8'): 23,
  (23, '\xe9'): 23,
  (23, '\xea'): 23,
  (23, '\xeb'): 23,
  (23, '\xec'): 23,
  (23, '\xed'): 23,
  (23, '\xee'): 23,
  (23, '\xef'): 23,
  (23, '\xf0'): 23,
  (23, '\xf1'): 23,
  (23, '\xf2'): 23,
  (23, '\xf3'): 23,
  (23, '\xf4'): 23,
  (23, '\xf5'): 23,
  (23, '\xf6'): 23,
  (23, '\xf7'): 23,
  (23, '\xf8'): 23,
  (23, '\xf9'): 23,
  (23, '\xfa'): 23,
  (23, '\xfb'): 23,
  (23, '\xfc'): 23,
  (23, '\xfd'): 23,
  (23, '\xfe'): 23,
  (23, '\xff'): 23,
  (24, '\x00'): 24,
  (24, '\x01'): 24,
  (24, '\x02'): 24,
  (24, '\x03'): 24,
  (24, '\x04'): 24,
  (24, '\x05'): 24,
  (24, '\x06'): 24,
  (24, '\x07'): 24,
  (24, '\x08'): 24,
  (24, '\t'): 24,
  (24, '\n'): 24,
  (24, '\x0b'): 24,
  (24, '\x0c'): 24,
  (24, '\r'): 24,
  (24, '\x0e'): 24,
  (24, '\x0f'): 24,
  (24, '\x10'): 24,
  (24, '\x11'): 24,
  (24, '\x12'): 24,
  (24, '\x13'): 24,
  (24, '\x14'): 24,
  (24, '\x15'): 24,
  (24, '\x16'): 24,
  (24, '\x17'): 24,
  (24, '\x18'): 24,
  (24, '\x19'): 24,
  (24, '\x1a'): 24,
  (24, '\x1b'): 24,
  (24, '\x1c'): 24,
  (24, '\x1d'): 24,
  (24, '\x1e'): 24,
  (24, '\x1f'): 24,
  (24, ' '): 24,
  (24, '!'): 24,
  (24, '"'): 24,
  (24, '#'): 24,
  (24, '$'): 24,
  (24, '%'): 24,
  (24, '&'): 24,
  (24, "'"): 24,
  (24, '('): 24,
  (24, ')'): 24,
  (24, '*'): 24,
  (24, '+'): 24,
  (24, ','): 24,
  (24, '-'): 24,
  (24, '.'): 24,
  (24, '/'): 24,
  (24, '0'): 24,
  (24, '1'): 24,
  (24, '2'): 24,
  (24, '3'): 24,
  (24, '4'): 24,
  (24, '5'): 24,
  (24, '6'): 24,
  (24, '7'): 24,
  (24, '8'): 24,
  (24, '9'): 24,
  (24, ':'): 24,
  (24, ';'): 24,
  (24, '<'): 24,
  (24, '='): 24,
  (24, '>'): 24,
  (24, '?'): 24,
  (24, '@'): 24,
  (24, 'A'): 24,
  (24, 'B'): 24,
  (24, 'C'): 24,
  (24, 'D'): 24,
  (24, 'E'): 24,
  (24, 'F'): 24,
  (24, 'G'): 24,
  (24, 'H'): 24,
  (24, 'I'): 24,
  (24, 'J'): 24,
  (24, 'K'): 24,
  (24, 'L'): 24,
  (24, 'M'): 24,
  (24, 'N'): 24,
  (24, 'O'): 24,
  (24, 'P'): 24,
  (24, 'Q'): 24,
  (24, 'R'): 24,
  (24, 'S'): 24,
  (24, 'T'): 24,
  (24, 'U'): 24,
  (24, 'V'): 24,
  (24, 'W'): 24,
  (24, 'X'): 24,
  (24, 'Y'): 24,
  (24, 'Z'): 24,
  (24, '['): 24,
  (24, '\\'): 24,
  (24, ']'): 24,
  (24, '^'): 24,
  (24, '_'): 24,
  (24, '`'): 24,
  (24, 'a'): 24,
  (24, 'b'): 24,
  (24, 'c'): 24,
  (24, 'd'): 24,
  (24, 'e'): 24,
  (24, 'f'): 24,
  (24, 'g'): 24,
  (24, 'h'): 24,
  (24, 'i'): 24,
  (24, 'j'): 24,
  (24, 'k'): 24,
  (24, 'l'): 24,
  (24, 'm'): 24,
  (24, 'n'): 24,
  (24, 'o'): 24,
  (24, 'p'): 24,
  (24, 'q'): 24,
  (24, 'r'): 24,
  (24, 's'): 24,
  (24, 't'): 24,
  (24, 'u'): 24,
  (24, 'v'): 24,
  (24, 'w'): 24,
  (24, 'x'): 24,
  (24, 'y'): 24,
  (24, 'z'): 24,
  (24, '{'): 24,
  (24, '|'): 24,
  (24, '}'): 24,
  (24, '~'): 24,
  (24, '\x7f'): 24,
  (24, '\x81'): 24,
  (24, '\x82'): 24,
  (24, '\x83'): 24,
  (24, '\x84'): 24,
  (24, '\x85'): 24,
  (24, '\x86'): 24,
  (24, '\x87'): 24,
  (24, '\x88'): 24,
  (24, '\x89'): 24,
  (24, '\x8a'): 24,
  (24, '\x8b'): 24,
  (24, '\x8c'): 24,
  (24, '\x8d'): 24,
  (24, '\x8e'): 24,
  (24, '\x8f'): 24,
  (24, '\x90'): 24,
  (24, '\x91'): 24,
  (24, '\x92'): 24,
  (24, '\x93'): 24,
  (24, '\x94'): 24,
  (24, '\x95'): 24,
  (24, '\x96'): 24,
  (24, '\x97'): 24,
  (24, '\x98'): 24,
  (24, '\x99'): 24,
  (24, '\x9a'): 24,
  (24, '\x9b'): 24,
  (24, '\x9c'): 24,
  (24, '\x9e'): 24,
  (24, '\x9f'): 24,
  (24, '\xa0'): 24,
  (24, '\xa1'): 24,
  (24, '\xa2'): 24,
  (24, '\xa3'): 24,
  (24, '\xa4'): 24,
  (24, '\xa5'): 24,
  (24, '\xa6'): 24,
  (24, '\xa7'): 24,
  (24, '\xa8'): 24,
  (24, '\xa9'): 24,
  (24, '\xaa'): 24,
  (24, '\xab'): 24,
  (24, '\xac'): 24,
  (24, '\xad'): 24,
  (24, '\xae'): 24,
  (24, '\xaf'): 24,
  (24, '\xb0'): 24,
  (24, '\xb1'): 24,
  (24, '\xb2'): 24,
  (24, '\xb3'): 24,
  (24, '\xb4'): 24,
  (24, '\xb5'): 24,
  (24, '\xb6'): 24,
  (24, '\xb7'): 24,
  (24, '\xb8'): 24,
  (24, '\xb9'): 24,
  (24, '\xba'): 24,
  (24, '\xbb'): 24,
  (24, '\xbc'): 24,
  (24, '\xbd'): 24,
  (24, '\xbe'): 24,
  (24, '\xbf'): 24,
  (24, '\xc0'): 24,
  (24, '\xc1'): 24,
  (24, '\xc2'): 24,
  (24, '\xc3'): 24,
  (24, '\xc4'): 24,
  (24, '\xc5'): 24,
  (24, '\xc6'): 24,
  (24, '\xc7'): 24,
  (24, '\xc8'): 24,
  (24, '\xc9'): 24,
  (24, '\xca'): 24,
  (24, '\xcb'): 24,
  (24, '\xcc'): 24,
  (24, '\xcd'): 24,
  (24, '\xce'): 24,
  (24, '\xcf'): 24,
  (24, '\xd0'): 24,
  (24, '\xd1'): 24,
  (24, '\xd2'): 24,
  (24, '\xd3'): 24,
  (24, '\xd4'): 24,
  (24, '\xd5'): 24,
  (24, '\xd6'): 24,
  (24, '\xd7'): 24,
  (24, '\xd8'): 24,
  (24, '\xd9'): 24,
  (24, '\xda'): 24,
  (24, '\xdb'): 24,
  (24, '\xdc'): 24,
  (24, '\xdd'): 24,
  (24, '\xde'): 24,
  (24, '\xdf'): 24,
  (24, '\xe0'): 24,
  (24, '\xe1'): 24,
  (24, '\xe2'): 25,
  (24, '\xe3'): 24,
  (24, '\xe4'): 24,
  (24, '\xe5'): 24,
  (24, '\xe6'): 24,
  (24, '\xe7'): 24,
  (24, '\xe8'): 24,
  (24, '\xe9'): 24,
  (24, '\xea'): 24,
  (24, '\xeb'): 24,
  (24, '\xec'): 24,
  (24, '\xed'): 24,
  (24, '\xee'): 24,
  (24, '\xef'): 24,
  (24, '\xf0'): 24,
  (24, '\xf1'): 24,
  (24, '\xf2'): 24,
  (24, '\xf3'): 24,
  (24, '\xf4'): 24,
  (24, '\xf5'): 24,
  (24, '\xf6'): 24,
  (24, '\xf7'): 24,
  (24, '\xf8'): 24,
  (24, '\xf9'): 24,
  (24, '\xfa'): 24,
  (24, '\xfb'): 24,
  (24, '\xfc'): 24,
  (24, '\xfd'): 24,
  (24, '\xfe'): 24,
  (24, '\xff'): 24,
  (25, '\x80'): 26,
  (26, '\x9d'): 27,
  (28, '\x80'): 29,
  (29, '\x99'): 30,
  (36, '\x00'): 41,
  (36, '\x01'): 41,
  (36, '\x02'): 41,
  (36, '\x03'): 41,
  (36, '\x04'): 41,
  (36, '\x05'): 41,
  (36, '\x06'): 41,
  (36, '\x07'): 41,
  (36, '\x08'): 41,
  (36, '\t'): 42,
  (36, '\n'): 42,
  (36, '\x0b'): 41,
  (36, '\x0c'): 42,
  (36, '\r'): 42,
  (36, '\x0e'): 41,
  (36, '\x0f'): 41,
  (36, '\x10'): 41,
  (36, '\x11'): 41,
  (36, '\x12'): 41,
  (36, '\x13'): 41,
  (36, '\x14'): 41,
  (36, '\x15'): 41,
  (36, '\x16'): 41,
  (36, '\x17'): 41,
  (36, '\x18'): 41,
  (36, '\x19'): 41,
  (36, '\x1a'): 41,
  (36, '\x1b'): 41,
  (36, '\x1c'): 41,
  (36, '\x1d'): 41,
  (36, '\x1e'): 41,
  (36, '\x1f'): 41,
  (36, ' '): 42,
  (36, '!'): 41,
  (36, '"'): 41,
  (36, '#'): 42,
  (36, '$'): 41,
  (36, '%'): 41,
  (36, '&'): 41,
  (36, "'"): 41,
  (36, '('): 42,
  (36, ')'): 42,
  (36, '*'): 41,
  (36, '+'): 41,
  (36, ','): 42,
  (36, '-'): 41,
  (36, '.'): 41,
  (36, '/'): 41,
  (36, '0'): 41,
  (36, '1'): 41,
  (36, '2'): 41,
  (36, '3'): 41,
  (36, '4'): 41,
  (36, '5'): 41,
  (36, '6'): 41,
  (36, '7'): 41,
  (36, '8'): 41,
  (36, '9'): 41,
  (36, ':'): 41,
  (36, ';'): 41,
  (36, '<'): 41,
  (36, '='): 41,
  (36, '>'): 41,
  (36, '?'): 41,
  (36, '@'): 41,
  (36, 'A'): 41,
  (36, 'B'): 41,
  (36, 'C'): 41,
  (36, 'D'): 41,
  (36, 'E'): 41,
  (36, 'F'): 41,
  (36, 'G'): 41,
  (36, 'H'): 41,
  (36, 'I'): 41,
  (36, 'J'): 41,
  (36, 'K'): 41,
  (36, 'L'): 41,
  (36, 'M'): 41,
  (36, 'N'): 41,
  (36, 'O'): 41,
  (36, 'P'): 41,
  (36, 'Q'): 41,
  (36, 'R'): 41,
  (36, 'S'): 41,
  (36, 'T'): 41,
  (36, 'U'): 41,
  (36, 'V'): 41,
  (36, 'W'): 41,
  (36, 'X'): 41,
  (36, 'Y'): 41,
  (36, 'Z'): 41,
  (36, '['): 41,
  (36, '\\'): 41,
  (36, ']'): 41,
  (36, '^'): 41,
  (36, '_'): 41,
  (36, '`'): 41,
  (36, 'a'): 41,
  (36, 'b'): 41,
  (36, 'c'): 41,
  (36, 'd'): 41,
  (36, 'e'): 41,
  (36, 'f'): 41,
  (36, 'g'): 41,
  (36, 'h'): 41,
  (36, 'i'): 41,
  (36, 'j'): 41,
  (36, 'k'): 41,
  (36, 'l'): 41,
  (36, 'm'): 41,
  (36, 'n'): 41,
  (36, 'o'): 41,
  (36, 'p'): 41,
  (36, 'q'): 41,
  (36, 'r'): 41,
  (36, 's'): 41,
  (36, 't'): 41,
  (36, 'u'): 41,
  (36, 'v'): 41,
  (36, 'w'): 41,
  (36, 'x'): 41,
  (36, 'y'): 41,
  (36, 'z'): 41,
  (36, '{'): 41,
  (36, '|'): 41,
  (36, '}'): 41,
  (36, '~'): 41,
  (36, '\x7f'): 41,
  (36, '\x80'): 41,
  (36, '\x81'): 41,
  (36, '\x82'): 41,
  (36, '\x83'): 41,
  (36, '\x84'): 41,
  (36, '\x85'): 41,
  (36, '\x86'): 41,
  (36, '\x87'): 41,
  (36, '\x88'): 41,
  (36, '\x89'): 41,
  (36, '\x8a'): 41,
  (36, '\x8b'): 41,
  (36, '\x8c'): 41,
  (36, '\x8d'): 41,
  (36, '\x8e'): 41,
  (36, '\x8f'): 41,
  (36, '\x90'): 41,
  (36, '\x91'): 41,
  (36, '\x92'): 41,
  (36, '\x93'): 41,
  (36, '\x94'): 41,
  (36, '\x95'): 41,
  (36, '\x96'): 41,
  (36, '\x97'): 41,
  (36, '\x98'): 41,
  (36, '\x99'): 41,
  (36, '\x9a'): 41,
  (36, '\x9b'): 41,
  (36, '\x9c'): 41,
  (36, '\x9d'): 41,
  (36, '\x9e'): 41,
  (36, '\x9f'): 42,
  (36, '\xa0'): 41,
  (36, '\xa1'): 41,
  (36, '\xa2'): 41,
  (36, '\xa3'): 41,
  (36, '\xa4'): 41,
  (36, '\xa5'): 41,
  (36, '\xa6'): 41,
  (36, '\xa7'): 41,
  (36, '\xa8'): 41,
  (36, '\xa9'): 41,
  (36, '\xaa'): 42,
  (36, '\xab'): 42,
  (36, '\xac'): 41,
  (36, '\xad'): 41,
  (36, '\xae'): 41,
  (36, '\xaf'): 41,
  (36, '\xb0'): 41,
  (36, '\xb1'): 41,
  (36, '\xb2'): 41,
  (36, '\xb3'): 41,
  (36, '\xb4'): 41,
  (36, '\xb5'): 41,
  (36, '\xb6'): 41,
  (36, '\xb7'): 41,
  (36, '\xb8'): 41,
  (36, '\xb9'): 41,
  (36, '\xba'): 41,
  (36, '\xbb'): 41,
  (36, '\xbc'): 41,
  (36, '\xbd'): 41,
  (36, '\xbe'): 41,
  (36, '\xbf'): 41,
  (36, '\xc0'): 41,
  (36, '\xc1'): 41,
  (36, '\xc2'): 41,
  (36, '\xc3'): 41,
  (36, '\xc4'): 41,
  (36, '\xc5'): 41,
  (36, '\xc6'): 41,
  (36, '\xc7'): 41,
  (36, '\xc8'): 41,
  (36, '\xc9'): 41,
  (36, '\xca'): 41,
  (36, '\xcb'): 41,
  (36, '\xcc'): 41,
  (36, '\xcd'): 41,
  (36, '\xce'): 41,
  (36, '\xcf'): 41,
  (36, '\xd0'): 41,
  (36, '\xd1'): 41,
  (36, '\xd2'): 41,
  (36, '\xd3'): 41,
  (36, '\xd4'): 41,
  (36, '\xd5'): 41,
  (36, '\xd6'): 41,
  (36, '\xd7'): 41,
  (36, '\xd8'): 41,
  (36, '\xd9'): 41,
  (36, '\xda'): 41,
  (36, '\xdb'): 41,
  (36, '\xdc'): 41,
  (36, '\xdd'): 41,
  (36, '\xde'): 41,
  (36, '\xdf'): 41,
  (36, '\xe0'): 41,
  (36, '\xe1'): 41,
  (36, '\xe2'): 42,
  (36, '\xe3'): 41,
  (36, '\xe4'): 41,
  (36, '\xe5'): 41,
  (36, '\xe6'): 41,
  (36, '\xe7'): 41,
  (36, '\xe8'): 41,
  (36, '\xe9'): 41,
  (36, '\xea'): 41,
  (36, '\xeb'): 41,
  (36, '\xec'): 41,
  (36, '\xed'): 41,
  (36, '\xee'): 41,
  (36, '\xef'): 41,
  (36, '\xf0'): 41,
  (36, '\xf1'): 41,
  (36, '\xf2'): 41,
  (36, '\xf3'): 41,
  (36, '\xf4'): 41,
  (36, '\xf5'): 41,
  (36, '\xf6'): 41,
  (36, '\xf7'): 41,
  (36, '\xf8'): 41,
  (36, '\xf9'): 41,
  (36, '\xfa'): 41,
  (36, '\xfb'): 41,
  (36, '\xfc'): 41,
  (36, '\xfd'): 41,
  (36, '\xfe'): 41,
  (36, '\xff'): 41,
  (37, '\x00'): 39,
  (37, '\x01'): 39,
  (37, '\x02'): 39,
  (37, '\x03'): 39,
  (37, '\x04'): 39,
  (37, '\x05'): 39,
  (37, '\x06'): 39,
  (37, '\x07'): 39,
  (37, '\x08'): 39,
  (37, '\t'): 40,
  (37, '\n'): 40,
  (37, '\x0b'): 39,
  (37, '\x0c'): 40,
  (37, '\r'): 40,
  (37, '\x0e'): 39,
  (37, '\x0f'): 39,
  (37, '\x10'): 39,
  (37, '\x11'): 39,
  (37, '\x12'): 39,
  (37, '\x13'): 39,
  (37, '\x14'): 39,
  (37, '\x15'): 39,
  (37, '\x16'): 39,
  (37, '\x17'): 39,
  (37, '\x18'): 39,
  (37, '\x19'): 39,
  (37, '\x1a'): 39,
  (37, '\x1b'): 39,
  (37, '\x1c'): 39,
  (37, '\x1d'): 39,
  (37, '\x1e'): 39,
  (37, '\x1f'): 39,
  (37, ' '): 40,
  (37, '!'): 39,
  (37, '"'): 39,
  (37, '#'): 40,
  (37, '$'): 39,
  (37, '%'): 39,
  (37, '&'): 39,
  (37, "'"): 39,
  (37, '('): 40,
  (37, ')'): 40,
  (37, '*'): 39,
  (37, '+'): 39,
  (37, ','): 40,
  (37, '-'): 39,
  (37, '.'): 39,
  (37, '/'): 39,
  (37, '0'): 39,
  (37, '1'): 39,
  (37, '2'): 39,
  (37, '3'): 39,
  (37, '4'): 39,
  (37, '5'): 39,
  (37, '6'): 39,
  (37, '7'): 39,
  (37, '8'): 39,
  (37, '9'): 39,
  (37, ':'): 39,
  (37, ';'): 39,
  (37, '<'): 39,
  (37, '='): 39,
  (37, '>'): 39,
  (37, '?'): 39,
  (37, '@'): 39,
  (37, 'A'): 39,
  (37, 'B'): 39,
  (37, 'C'): 39,
  (37, 'D'): 39,
  (37, 'E'): 39,
  (37, 'F'): 39,
  (37, 'G'): 39,
  (37, 'H'): 39,
  (37, 'I'): 39,
  (37, 'J'): 39,
  (37, 'K'): 39,
  (37, 'L'): 39,
  (37, 'M'): 39,
  (37, 'N'): 39,
  (37, 'O'): 39,
  (37, 'P'): 39,
  (37, 'Q'): 39,
  (37, 'R'): 39,
  (37, 'S'): 39,
  (37, 'T'): 39,
  (37, 'U'): 39,
  (37, 'V'): 39,
  (37, 'W'): 39,
  (37, 'X'): 39,
  (37, 'Y'): 39,
  (37, 'Z'): 39,
  (37, '['): 39,
  (37, '\\'): 39,
  (37, ']'): 39,
  (37, '^'): 39,
  (37, '_'): 39,
  (37, '`'): 39,
  (37, 'a'): 39,
  (37, 'b'): 39,
  (37, 'c'): 39,
  (37, 'd'): 39,
  (37, 'e'): 39,
  (37, 'f'): 39,
  (37, 'g'): 39,
  (37, 'h'): 39,
  (37, 'i'): 39,
  (37, 'j'): 39,
  (37, 'k'): 39,
  (37, 'l'): 39,
  (37, 'm'): 39,
  (37, 'n'): 39,
  (37, 'o'): 39,
  (37, 'p'): 39,
  (37, 'q'): 39,
  (37, 'r'): 39,
  (37, 's'): 39,
  (37, 't'): 39,
  (37, 'u'): 39,
  (37, 'v'): 39,
  (37, 'w'): 39,
  (37, 'x'): 39,
  (37, 'y'): 39,
  (37, 'z'): 39,
  (37, '{'): 39,
  (37, '|'): 39,
  (37, '}'): 39,
  (37, '~'): 39,
  (37, '\x7f'): 39,
  (37, '\x80'): 39,
  (37, '\x81'): 39,
  (37, '\x82'): 39,
  (37, '\x83'): 39,
  (37, '\x84'): 39,
  (37, '\x85'): 39,
  (37, '\x86'): 39,
  (37, '\x87'): 39,
  (37, '\x88'): 39,
  (37, '\x89'): 39,
  (37, '\x8a'): 39,
  (37, '\x8b'): 39,
  (37, '\x8c'): 39,
  (37, '\x8d'): 39,
  (37, '\x8e'): 39,
  (37, '\x8f'): 39,
  (37, '\x90'): 39,
  (37, '\x91'): 39,
  (37, '\x92'): 39,
  (37, '\x93'): 39,
  (37, '\x94'): 39,
  (37, '\x95'): 39,
  (37, '\x96'): 39,
  (37, '\x97'): 39,
  (37, '\x98'): 39,
  (37, '\x99'): 39,
  (37, '\x9a'): 39,
  (37, '\x9b'): 39,
  (37, '\x9c'): 39,
  (37, '\x9d'): 39,
  (37, '\x9e'): 39,
  (37, '\x9f'): 40,
  (37, '\xa0'): 39,
  (37, '\xa1'): 39,
  (37, '\xa2'): 39,
  (37, '\xa3'): 39,
  (37, '\xa4'): 39,
  (37, '\xa5'): 39,
  (37, '\xa6'): 39,
  (37, '\xa7'): 39,
  (37, '\xa8'): 39,
  (37, '\xa9'): 39,
  (37, '\xaa'): 40,
  (37, '\xab'): 40,
  (37, '\xac'): 39,
  (37, '\xad'): 39,
  (37, '\xae'): 39,
  (37, '\xaf'): 39,
  (37, '\xb0'): 39,
  (37, '\xb1'): 39,
  (37, '\xb2'): 39,
  (37, '\xb3'): 39,
  (37, '\xb4'): 39,
  (37, '\xb5'): 39,
  (37, '\xb6'): 39,
  (37, '\xb7'): 39,
  (37, '\xb8'): 39,
  (37, '\xb9'): 39,
  (37, '\xba'): 39,
  (37, '\xbb'): 39,
  (37, '\xbc'): 39,
  (37, '\xbd'): 39,
  (37, '\xbe'): 39,
  (37, '\xbf'): 39,
  (37, '\xc0'): 39,
  (37, '\xc1'): 39,
  (37, '\xc2'): 39,
  (37, '\xc3'): 39,
  (37, '\xc4'): 39,
  (37, '\xc5'): 39,
  (37, '\xc6'): 39,
  (37, '\xc7'): 39,
  (37, '\xc8'): 39,
  (37, '\xc9'): 39,
  (37, '\xca'): 39,
  (37, '\xcb'): 39,
  (37, '\xcc'): 39,
  (37, '\xcd'): 39,
  (37, '\xce'): 39,
  (37, '\xcf'): 39,
  (37, '\xd0'): 39,
  (37, '\xd1'): 39,
  (37, '\xd2'): 39,
  (37, '\xd3'): 39,
  (37, '\xd4'): 39,
  (37, '\xd5'): 39,
  (37, '\xd6'): 39,
  (37, '\xd7'): 39,
  (37, '\xd8'): 39,
  (37, '\xd9'): 39,
  (37, '\xda'): 39,
  (37, '\xdb'): 39,
  (37, '\xdc'): 39,
  (37, '\xdd'): 39,
  (37, '\xde'): 39,
  (37, '\xdf'): 39,
  (37, '\xe0'): 39,
  (37, '\xe1'): 39,
  (37, '\xe2'): 40,
  (37, '\xe3'): 39,
  (37, '\xe4'): 39,
  (37, '\xe5'): 39,
  (37, '\xe6'): 39,
  (37, '\xe7'): 39,
  (37, '\xe8'): 39,
  (37, '\xe9'): 39,
  (37, '\xea'): 39,
  (37, '\xeb'): 39,
  (37, '\xec'): 39,
  (37, '\xed'): 39,
  (37, '\xee'): 39,
  (37, '\xef'): 39,
  (37, '\xf0'): 39,
  (37, '\xf1'): 39,
  (37, '\xf2'): 39,
  (37, '\xf3'): 39,
  (37, '\xf4'): 39,
  (37, '\xf5'): 39,
  (37, '\xf6'): 39,
  (37, '\xf7'): 39,
  (37, '\xf8'): 39,
  (37, '\xf9'): 39,
  (37, '\xfa'): 39,
  (37, '\xfb'): 39,
  (37, '\xfc'): 39,
  (37, '\xfd'): 39,
  (37, '\xfe'): 39,
  (37, '\xff'): 39,
  (38, '\x00'): 10,
  (38, '\x01'): 10,
  (38, '\x02'): 10,
  (38, '\x03'): 10,
  (38, '\x04'): 10,
  (38, '\x05'): 10,
  (38, '\x06'): 10,
  (38, '\x07'): 10,
  (38, '\x08'): 10,
  (38, '\x0b'): 10,
  (38, '\x0e'): 10,
  (38, '\x0f'): 10,
  (38, '\x10'): 10,
  (38, '\x11'): 10,
  (38, '\x12'): 10,
  (38, '\x13'): 10,
  (38, '\x14'): 10,
  (38, '\x15'): 10,
  (38, '\x16'): 10,
  (38, '\x17'): 10,
  (38, '\x18'): 10,
  (38, '\x19'): 10,
  (38, '\x1a'): 10,
  (38, '\x1b'): 10,
  (38, '\x1c'): 10,
  (38, '\x1d'): 10,
  (38, '\x1e'): 10,
  (38, '\x1f'): 10,
  (38, '!'): 10,
  (38, '"'): 10,
  (38, '$'): 10,
  (38, '%'): 10,
  (38, '&'): 10,
  (38, "'"): 10,
  (38, '*'): 10,
  (38, '+'): 10,
  (38, '-'): 10,
  (38, '.'): 10,
  (38, '/'): 10,
  (38, '0'): 10,
  (38, '1'): 10,
  (38, '2'): 10,
  (38, '3'): 10,
  (38, '4'): 10,
  (38, '5'): 10,
  (38, '6'): 10,
  (38, '7'): 10,
  (38, '8'): 10,
  (38, '9'): 10,
  (38, ':'): 10,
  (38, ';'): 10,
  (38, '<'): 10,
  (38, '='): 10,
  (38, '>'): 10,
  (38, '?'): 10,
  (38, '@'): 10,
  (38, 'A'): 10,
  (38, 'B'): 10,
  (38, 'C'): 10,
  (38, 'D'): 10,
  (38, 'E'): 10,
  (38, 'F'): 10,
  (38, 'G'): 10,
  (38, 'H'): 10,
  (38, 'I'): 10,
  (38, 'J'): 10,
  (38, 'K'): 10,
  (38, 'L'): 10,
  (38, 'M'): 10,
  (38, 'N'): 10,
  (38, 'O'): 10,
  (38, 'P'): 10,
  (38, 'Q'): 10,
  (38, 'R'): 10,
  (38, 'S'): 10,
  (38, 'T'): 10,
  (38, 'U'): 10,
  (38, 'V'): 10,
  (38, 'W'): 10,
  (38, 'X'): 10,
  (38, 'Y'): 10,
  (38, 'Z'): 10,
  (38, '['): 10,
  (38, '\\'): 10,
  (38, ']'): 10,
  (38, '^'): 10,
  (38, '_'): 10,
  (38, '`'): 10,
  (38, 'a'): 10,
  (38, 'b'): 10,
  (38, 'c'): 10,
  (38, 'd'): 10,
  (38, 'e'): 10,
  (38, 'f'): 10,
  (38, 'g'): 10,
  (38, 'h'): 10,
  (38, 'i'): 10,
  (38, 'j'): 10,
  (38, 'k'): 10,
  (38, 'l'): 10,
  (38, 'm'): 10,
  (38, 'n'): 10,
  (38, 'o'): 10,
  (38, 'p'): 10,
  (38, 'q'): 10,
  (38, 'r'): 10,
  (38, 's'): 10,
  (38, 't'): 10,
  (38, 'u'): 10,
  (38, 'v'): 10,
  (38, 'w'): 10,
  (38, 'x'): 10,
  (38, 'y'): 10,
  (38, 'z'): 10,
  (38, '{'): 10,
  (38, '|'): 10,
  (38, '}'): 10,
  (38, '~'): 10,
  (38, '\x7f'): 10,
  (38, '\x80'): 10,
  (38, '\x81'): 10,
  (38, '\x82'): 10,
  (38, '\x83'): 10,
  (38, '\x84'): 10,
  (38, '\x85'): 10,
  (38, '\x86'): 10,
  (38, '\x87'): 10,
  (38, '\x88'): 10,
  (38, '\x89'): 10,
  (38, '\x8a'): 10,
  (38, '\x8b'): 10,
  (38, '\x8c'): 10,
  (38, '\x8d'): 10,
  (38, '\x8e'): 10,
  (38, '\x8f'): 10,
  (38, '\x90'): 10,
  (38, '\x91'): 10,
  (38, '\x92'): 10,
  (38, '\x93'): 10,
  (38, '\x94'): 10,
  (38, '\x95'): 10,
  (38, '\x96'): 10,
  (38, '\x97'): 10,
  (38, '\x98'): 10,
  (38, '\x99'): 10,
  (38, '\x9a'): 10,
  (38, '\x9b'): 10,
  (38, '\x9c'): 10,
  (38, '\x9d'): 10,
  (38, '\x9e'): 10,
  (38, '\xa0'): 10,
  (38, '\xa1'): 10,
  (38, '\xa2'): 10,
  (38, '\xa3'): 10,
  (38, '\xa4'): 10,
  (38, '\xa5'): 10,
  (38, '\xa6'): 10,
  (38, '\xa7'): 10,
  (38, '\xa8'): 10,
  (38, '\xa9'): 10,
  (38, '\xac'): 10,
  (38, '\xad'): 10,
  (38, '\xae'): 10,
  (38, '\xaf'): 10,
  (38, '\xb0'): 10,
  (38, '\xb1'): 10,
  (38, '\xb2'): 10,
  (38, '\xb3'): 10,
  (38, '\xb4'): 10,
  (38, '\xb5'): 10,
  (38, '\xb6'): 10,
  (38, '\xb7'): 10,
  (38, '\xb8'): 10,
  (38, '\xb9'): 10,
  (38, '\xba'): 10,
  (38, '\xbb'): 10,
  (38, '\xbc'): 10,
  (38, '\xbd'): 10,
  (38, '\xbe'): 10,
  (38, '\xbf'): 10,
  (38, '\xc0'): 10,
  (38, '\xc1'): 10,
  (38, '\xc2'): 10,
  (38, '\xc3'): 10,
  (38, '\xc4'): 10,
  (38, '\xc5'): 10,
  (38, '\xc6'): 10,
  (38, '\xc7'): 10,
  (38, '\xc8'): 10,
  (38, '\xc9'): 10,
  (38, '\xca'): 10,
  (38, '\xcb'): 10,
  (38, '\xcc'): 10,
  (38, '\xcd'): 10,
  (38, '\xce'): 10,
  (38, '\xcf'): 10,
  (38, '\xd0'): 10,
  (38, '\xd1'): 10,
  (38, '\xd2'): 10,
  (38, '\xd3'): 10,
  (38, '\xd4'): 10,
  (38, '\xd5'): 10,
  (38, '\xd6'): 10,
  (38, '\xd7'): 10,
  (38, '\xd8'): 10,
  (38, '\xd9'): 10,
  (38, '\xda'): 10,
  (38, '\xdb'): 10,
  (38, '\xdc'): 10,
  (38, '\xdd'): 10,
  (38, '\xde'): 10,
  (38, '\xdf'): 10,
  (38, '\xe0'): 10,
  (38, '\xe1'): 10,
  (38, '\xe3'): 10,
  (38, '\xe4'): 10,
  (38, '\xe5'): 10,
  (38, '\xe6'): 10,
  (38, '\xe7'): 10,
  (38, '\xe8'): 10,
  (38, '\xe9'): 10,
  (38, '\xea'): 10,
  (38, '\xeb'): 10,
  (38, '\xec'): 10,
  (38, '\xed'): 10,
  (38, '\xee'): 10,
  (38, '\xef'): 10,
  (38, '\xf0'): 10,
  (38, '\xf1'): 10,
  (38, '\xf2'): 10,
  (38, '\xf3'): 10,
  (38, '\xf4'): 10,
  (38, '\xf5'): 10,
  (38, '\xf6'): 10,
  (38, '\xf7'): 10,
  (38, '\xf8'): 10,
  (38, '\xf9'): 10,
  (38, '\xfa'): 10,
  (38, '\xfb'): 10,
  (38, '\xfc'): 10,
  (38, '\xfd'): 10,
  (38, '\xfe'): 10,
  (38, '\xff'): 10,
  (39, '\x00'): 10,
  (39, '\x01'): 10,
  (39, '\x02'): 10,
  (39, '\x03'): 10,
  (39, '\x04'): 10,
  (39, '\x05'): 10,
  (39, '\x06'): 10,
  (39, '\x07'): 10,
  (39, '\x08'): 10,
  (39, '\x0b'): 10,
  (39, '\x0e'): 10,
  (39, '\x0f'): 10,
  (39, '\x10'): 10,
  (39, '\x11'): 10,
  (39, '\x12'): 10,
  (39, '\x13'): 10,
  (39, '\x14'): 10,
  (39, '\x15'): 10,
  (39, '\x16'): 10,
  (39, '\x17'): 10,
  (39, '\x18'): 10,
  (39, '\x19'): 10,
  (39, '\x1a'): 10,
  (39, '\x1b'): 10,
  (39, '\x1c'): 10,
  (39, '\x1d'): 10,
  (39, '\x1e'): 10,
  (39, '\x1f'): 10,
  (39, '!'): 10,
  (39, '"'): 10,
  (39, '$'): 10,
  (39, '%'): 10,
  (39, '&'): 10,
  (39, "'"): 10,
  (39, '*'): 10,
  (39, '+'): 10,
  (39, '-'): 10,
  (39, '.'): 10,
  (39, '/'): 10,
  (39, '0'): 10,
  (39, '1'): 10,
  (39, '2'): 10,
  (39, '3'): 10,
  (39, '4'): 10,
  (39, '5'): 10,
  (39, '6'): 10,
  (39, '7'): 10,
  (39, '8'): 10,
  (39, '9'): 10,
  (39, ':'): 10,
  (39, ';'): 10,
  (39, '<'): 10,
  (39, '='): 10,
  (39, '>'): 10,
  (39, '?'): 10,
  (39, '@'): 10,
  (39, 'A'): 10,
  (39, 'B'): 10,
  (39, 'C'): 10,
  (39, 'D'): 10,
  (39, 'E'): 10,
  (39, 'F'): 10,
  (39, 'G'): 10,
  (39, 'H'): 10,
  (39, 'I'): 10,
  (39, 'J'): 10,
  (39, 'K'): 10,
  (39, 'L'): 10,
  (39, 'M'): 10,
  (39, 'N'): 10,
  (39, 'O'): 10,
  (39, 'P'): 10,
  (39, 'Q'): 10,
  (39, 'R'): 10,
  (39, 'S'): 10,
  (39, 'T'): 10,
  (39, 'U'): 10,
  (39, 'V'): 10,
  (39, 'W'): 10,
  (39, 'X'): 10,
  (39, 'Y'): 10,
  (39, 'Z'): 10,
  (39, '['): 10,
  (39, '\\'): 10,
  (39, ']'): 10,
  (39, '^'): 10,
  (39, '_'): 10,
  (39, '`'): 10,
  (39, 'a'): 10,
  (39, 'b'): 10,
  (39, 'c'): 10,
  (39, 'd'): 10,
  (39, 'e'): 10,
  (39, 'f'): 10,
  (39, 'g'): 10,
  (39, 'h'): 10,
  (39, 'i'): 10,
  (39, 'j'): 10,
  (39, 'k'): 10,
  (39, 'l'): 10,
  (39, 'm'): 10,
  (39, 'n'): 10,
  (39, 'o'): 10,
  (39, 'p'): 10,
  (39, 'q'): 10,
  (39, 'r'): 10,
  (39, 's'): 10,
  (39, 't'): 10,
  (39, 'u'): 10,
  (39, 'v'): 10,
  (39, 'w'): 10,
  (39, 'x'): 10,
  (39, 'y'): 10,
  (39, 'z'): 10,
  (39, '{'): 10,
  (39, '|'): 10,
  (39, '}'): 10,
  (39, '~'): 10,
  (39, '\x7f'): 10,
  (39, '\x80'): 10,
  (39, '\x81'): 10,
  (39, '\x82'): 10,
  (39, '\x83'): 10,
  (39, '\x84'): 10,
  (39, '\x85'): 10,
  (39, '\x86'): 10,
  (39, '\x87'): 10,
  (39, '\x88'): 10,
  (39, '\x89'): 10,
  (39, '\x8a'): 10,
  (39, '\x8b'): 10,
  (39, '\x8c'): 10,
  (39, '\x8d'): 10,
  (39, '\x8e'): 10,
  (39, '\x8f'): 10,
  (39, '\x90'): 10,
  (39, '\x91'): 10,
  (39, '\x92'): 10,
  (39, '\x93'): 10,
  (39, '\x94'): 10,
  (39, '\x95'): 10,
  (39, '\x96'): 10,
  (39, '\x97'): 10,
  (39, '\x98'): 10,
  (39, '\x99'): 10,
  (39, '\x9a'): 10,
  (39, '\x9b'): 10,
  (39, '\x9c'): 10,
  (39, '\x9d'): 10,
  (39, '\x9e'): 10,
  (39, '\xa0'): 10,
  (39, '\xa1'): 10,
  (39, '\xa2'): 10,
  (39, '\xa3'): 10,
  (39, '\xa4'): 10,
  (39, '\xa5'): 10,
  (39, '\xa6'): 10,
  (39, '\xa7'): 10,
  (39, '\xa8'): 10,
  (39, '\xa9'): 10,
  (39, '\xac'): 10,
  (39, '\xad'): 10,
  (39, '\xae'): 10,
  (39, '\xaf'): 10,
  (39, '\xb0'): 10,
  (39, '\xb1'): 10,
  (39, '\xb2'): 10,
  (39, '\xb3'): 10,
  (39, '\xb4'): 10,
  (39, '\xb5'): 10,
  (39, '\xb6'): 10,
  (39, '\xb7'): 10,
  (39, '\xb8'): 10,
  (39, '\xb9'): 10,
  (39, '\xba'): 10,
  (39, '\xbb'): 10,
  (39, '\xbc'): 10,
  (39, '\xbd'): 10,
  (39, '\xbe'): 10,
  (39, '\xbf'): 10,
  (39, '\xc0'): 10,
  (39, '\xc1'): 10,
  (39, '\xc2'): 10,
  (39, '\xc3'): 10,
  (39, '\xc4'): 10,
  (39, '\xc5'): 10,
  (39, '\xc6'): 10,
  (39, '\xc7'): 10,
  (39, '\xc8'): 10,
  (39, '\xc9'): 10,
  (39, '\xca'): 10,
  (39, '\xcb'): 10,
  (39, '\xcc'): 10,
  (39, '\xcd'): 10,
  (39, '\xce'): 10,
  (39, '\xcf'): 10,
  (39, '\xd0'): 10,
  (39, '\xd1'): 10,
  (39, '\xd2'): 10,
  (39, '\xd3'): 10,
  (39, '\xd4'): 10,
  (39, '\xd5'): 10,
  (39, '\xd6'): 10,
  (39, '\xd7'): 10,
  (39, '\xd8'): 10,
  (39, '\xd9'): 10,
  (39, '\xda'): 10,
  (39, '\xdb'): 10,
  (39, '\xdc'): 10,
  (39, '\xdd'): 10,
  (39, '\xde'): 10,
  (39, '\xdf'): 10,
  (39, '\xe0'): 10,
  (39, '\xe1'): 10,
  (39, '\xe3'): 10,
  (39, '\xe4'): 10,
  (39, '\xe5'): 10,
  (39, '\xe6'): 10,
  (39, '\xe7'): 10,
  (39, '\xe8'): 10,
  (39, '\xe9'): 10,
  (39, '\xea'): 10,
  (39, '\xeb'): 10,
  (39, '\xec'): 10,
  (39, '\xed'): 10,
  (39, '\xee'): 10,
  (39, '\xef'): 10,
  (39, '\xf0'): 10,
  (39, '\xf1'): 10,
  (39, '\xf2'): 10,
  (39, '\xf3'): 10,
  (39, '\xf4'): 10,
  (39, '\xf5'): 10,
  (39, '\xf6'): 10,
  (39, '\xf7'): 10,
  (39, '\xf8'): 10,
  (39, '\xf9'): 10,
  (39, '\xfa'): 10,
  (39, '\xfb'): 10,
  (39, '\xfc'): 10,
  (39, '\xfd'): 10,
  (39, '\xfe'): 10,
  (39, '\xff'): 10,
  (41, '\x00'): 10,
  (41, '\x01'): 10,
  (41, '\x02'): 10,
  (41, '\x03'): 10,
  (41, '\x04'): 10,
  (41, '\x05'): 10,
  (41, '\x06'): 10,
  (41, '\x07'): 10,
  (41, '\x08'): 10,
  (41, '\x0b'): 10,
  (41, '\x0e'): 10,
  (41, '\x0f'): 10,
  (41, '\x10'): 10,
  (41, '\x11'): 10,
  (41, '\x12'): 10,
  (41, '\x13'): 10,
  (41, '\x14'): 10,
  (41, '\x15'): 10,
  (41, '\x16'): 10,
  (41, '\x17'): 10,
  (41, '\x18'): 10,
  (41, '\x19'): 10,
  (41, '\x1a'): 10,
  (41, '\x1b'): 10,
  (41, '\x1c'): 10,
  (41, '\x1d'): 10,
  (41, '\x1e'): 10,
  (41, '\x1f'): 10,
  (41, '!'): 10,
  (41, '"'): 10,
  (41, '$'): 10,
  (41, '%'): 10,
  (41, '&'): 10,
  (41, "'"): 10,
  (41, '*'): 10,
  (41, '+'): 10,
  (41, '-'): 10,
  (41, '.'): 10,
  (41, '/'): 10,
  (41, '0'): 10,
  (41, '1'): 10,
  (41, '2'): 10,
  (41, '3'): 10,
  (41, '4'): 10,
  (41, '5'): 10,
  (41, '6'): 10,
  (41, '7'): 10,
  (41, '8'): 10,
  (41, '9'): 10,
  (41, ':'): 10,
  (41, ';'): 10,
  (41, '<'): 10,
  (41, '='): 10,
  (41, '>'): 10,
  (41, '?'): 10,
  (41, '@'): 10,
  (41, 'A'): 10,
  (41, 'B'): 10,
  (41, 'C'): 10,
  (41, 'D'): 10,
  (41, 'E'): 10,
  (41, 'F'): 10,
  (41, 'G'): 10,
  (41, 'H'): 10,
  (41, 'I'): 10,
  (41, 'J'): 10,
  (41, 'K'): 10,
  (41, 'L'): 10,
  (41, 'M'): 10,
  (41, 'N'): 10,
  (41, 'O'): 10,
  (41, 'P'): 10,
  (41, 'Q'): 10,
  (41, 'R'): 10,
  (41, 'S'): 10,
  (41, 'T'): 10,
  (41, 'U'): 10,
  (41, 'V'): 10,
  (41, 'W'): 10,
  (41, 'X'): 10,
  (41, 'Y'): 10,
  (41, 'Z'): 10,
  (41, '['): 10,
  (41, '\\'): 10,
  (41, ']'): 10,
  (41, '^'): 10,
  (41, '_'): 10,
  (41, '`'): 10,
  (41, 'a'): 10,
  (41, 'b'): 10,
  (41, 'c'): 10,
  (41, 'd'): 10,
  (41, 'e'): 10,
  (41, 'f'): 10,
  (41, 'g'): 10,
  (41, 'h'): 10,
  (41, 'i'): 10,
  (41, 'j'): 10,
  (41, 'k'): 10,
  (41, 'l'): 10,
  (41, 'm'): 10,
  (41, 'n'): 10,
  (41, 'o'): 10,
  (41, 'p'): 10,
  (41, 'q'): 10,
  (41, 'r'): 10,
  (41, 's'): 10,
  (41, 't'): 10,
  (41, 'u'): 10,
  (41, 'v'): 10,
  (41, 'w'): 10,
  (41, 'x'): 10,
  (41, 'y'): 10,
  (41, 'z'): 10,
  (41, '{'): 10,
  (41, '|'): 10,
  (41, '}'): 10,
  (41, '~'): 10,
  (41, '\x7f'): 10,
  (41, '\x80'): 10,
  (41, '\x81'): 10,
  (41, '\x82'): 10,
  (41, '\x83'): 10,
  (41, '\x84'): 10,
  (41, '\x85'): 10,
  (41, '\x86'): 10,
  (41, '\x87'): 10,
  (41, '\x88'): 10,
  (41, '\x89'): 10,
  (41, '\x8a'): 10,
  (41, '\x8b'): 10,
  (41, '\x8c'): 10,
  (41, '\x8d'): 10,
  (41, '\x8e'): 10,
  (41, '\x8f'): 10,
  (41, '\x90'): 10,
  (41, '\x91'): 10,
  (41, '\x92'): 10,
  (41, '\x93'): 10,
  (41, '\x94'): 10,
  (41, '\x95'): 10,
  (41, '\x96'): 10,
  (41, '\x97'): 10,
  (41, '\x98'): 10,
  (41, '\x99'): 10,
  (41, '\x9a'): 10,
  (41, '\x9b'): 10,
  (41, '\x9c'): 10,
  (41, '\x9d'): 10,
  (41, '\x9e'): 10,
  (41, '\xa0'): 10,
  (41, '\xa1'): 10,
  (41, '\xa2'): 10,
  (41, '\xa3'): 10,
  (41, '\xa4'): 10,
  (41, '\xa5'): 10,
  (41, '\xa6'): 10,
  (41, '\xa7'): 10,
  (41, '\xa8'): 10,
  (41, '\xa9'): 10,
  (41, '\xac'): 10,
  (41, '\xad'): 10,
  (41, '\xae'): 10,
  (41, '\xaf'): 10,
  (41, '\xb0'): 10,
  (41, '\xb1'): 10,
  (41, '\xb2'): 10,
  (41, '\xb3'): 10,
  (41, '\xb4'): 10,
  (41, '\xb5'): 10,
  (41, '\xb6'): 10,
  (41, '\xb7'): 10,
  (41, '\xb8'): 10,
  (41, '\xb9'): 10,
  (41, '\xba'): 10,
  (41, '\xbb'): 10,
  (41, '\xbc'): 10,
  (41, '\xbd'): 10,
  (41, '\xbe'): 10,
  (41, '\xbf'): 10,
  (41, '\xc0'): 10,
  (41, '\xc1'): 10,
  (41, '\xc2'): 10,
  (41, '\xc3'): 10,
  (41, '\xc4'): 10,
  (41, '\xc5'): 10,
  (41, '\xc6'): 10,
  (41, '\xc7'): 10,
  (41, '\xc8'): 10,
  (41, '\xc9'): 10,
  (41, '\xca'): 10,
  (41, '\xcb'): 10,
  (41, '\xcc'): 10,
  (41, '\xcd'): 10,
  (41, '\xce'): 10,
  (41, '\xcf'): 10,
  (41, '\xd0'): 10,
  (41, '\xd1'): 10,
  (41, '\xd2'): 10,
  (41, '\xd3'): 10,
  (41, '\xd4'): 10,
  (41, '\xd5'): 10,
  (41, '\xd6'): 10,
  (41, '\xd7'): 10,
  (41, '\xd8'): 10,
  (41, '\xd9'): 10,
  (41, '\xda'): 10,
  (41, '\xdb'): 10,
  (41, '\xdc'): 10,
  (41, '\xdd'): 10,
  (41, '\xde'): 10,
  (41, '\xdf'): 10,
  (41, '\xe0'): 10,
  (41, '\xe1'): 10,
  (41, '\xe3'): 10,
  (41, '\xe4'): 10,
  (41, '\xe5'): 10,
  (41, '\xe6'): 10,
  (41, '\xe7'): 10,
  (41, '\xe8'): 10,
  (41, '\xe9'): 10,
  (41, '\xea'): 10,
  (41, '\xeb'): 10,
  (41, '\xec'): 10,
  (41, '\xed'): 10,
  (41, '\xee'): 10,
  (41, '\xef'): 10,
  (41, '\xf0'): 10,
  (41, '\xf1'): 10,
  (41, '\xf2'): 10,
  (41, '\xf3'): 10,
  (41, '\xf4'): 10,
  (41, '\xf5'): 10,
  (41, '\xf6'): 10,
  (41, '\xf7'): 10,
  (41, '\xf8'): 10,
  (41, '\xf9'): 10,
  (41, '\xfa'): 10,
  (41, '\xfb'): 10,
  (41, '\xfc'): 10,
  (41, '\xfd'): 10,
  (41, '\xfe'): 10,
  (41, '\xff'): 10},
 set([0,
      1,
      2,
      3,
      4,
      6,
      7,
      8,
      9,
      10,
      11,
      12,
      14,
      15,
      16,
      17,
      27,
      30,
      31,
      32,
      33,
      34,
      35,
      36,
      37,
      38,
      39,
      40,
      41,
      42]),
 set([0,
      1,
      2,
      3,
      4,
      6,
      7,
      8,
      9,
      10,
      11,
      12,
      14,
      15,
      16,
      17,
      27,
      30,
      31,
      32,
      33,
      34,
      35,
      36,
      37,
      38,
      39,
      40,
      41,
      42]),
 ['IGNORE',
  '__1_.',
  '__0_,',
  'NEWLINE',
  'NAME',
  '1, 1, 1, 1, 1, 1, 1',
  'LEFT_PARENTHESIS',
  'RIGHT_PARENTHESIS',
  'NAME',
  'INTEGER',
  'NAME',
  'IGNORE',
  'IGNORE',
  '1, final*, 0',
  'FLOAT',
  'INTEGER',
  'NAME',
  'FLOAT',
  '2',
  '2',
  '2',
  '2, 2',
  '2, 2',
  '3, start*, start|, final*, final*, 0, start|, 0, start|, 0, 0, 0, 1, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0, 1, final|, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0, 1, final|, final|, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0, 1, final|, final|, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0',
  '3, start*, start|, final*, final*, 0, start|, 0, start|, 0, 0, 0, 1, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0, 1, final|, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0, 1, final|, final|, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0, 1, final|, final|, final|, final*, start*, final*, 0, start|, start|, 0, start|, 0, 0, 0',
  '1, final*, 0',
  '1, final*, 0',
  'QQSTRING',
  '1, final*, 0',
  '1, final*, 0',
  'QSTRING',
  'LEFT_DOUBLE_ANGLE',
  'RIGHT_DOUBLE_ANGLE',
  'DEFINEDAS',
  'RIGHTWARDS_DOUBLE_ARROW',
  'MAPSTO',
  'NAME',
  'NAME',
  'MU',
  'ULAMBDA',
  'ULAMBDA',
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
    f.write(newcontent.encode("utf-8"), mode="wb")
