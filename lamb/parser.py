#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
    Parser for lamb.
"""
from __future__ import absolute_import

from rpython.rlib.parsing.lexer import Lexer
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
    def __init__(self, source, is_file=False):
        RPythonVisitor.__init__(self)
        self.is_file = is_file
        if self.is_file:
            try:
                f = open_file_as_stream(source, buffering=0)
            except OSError as e:
                os.write(2, "Error [%s] %\n" % (source, os.strerror(e.errno)))
                return
            try:
                self.source = Source(f.readall(), source)
            finally:
                f.close()
        else:
            self.source = Source(source)
        self.parser, self.lexer, self.transformer = make_lamb_parser()
        self.bindings_stack = [{}]
        self.lamb_stack = []
        self.rule_effect_tracker = 0
        self.rule_pattern_tracker = 0

    def parse(self):
        try:
            tokens = self.lexer.tokenize(self.source.contents(),
                                         eof=self.is_file)
            if not we_are_translated() and print_tokens:
                from pprint import pprint
                pprint(tokens)
            parsed = self.parser.parse(tokens)
        except ParseError, e:
            print e.nice_error_message(filename=self.source.filename,
                                       source=self.source.contents())
            raise
        except PyParseError, e:
            print e.nice_error_message(filename=self.source.filename,
                                       source=self.source.contents())
            raise
        pre_ast = self.transformer().transform(parsed)
        actual_ast = self.dispatch(pre_ast)
        if not we_are_translated():
            try:
                if py.test.config.option.view:
                    actual_ast.view()
            except AttributeError:
                pass
        import pprint; pprint.pprint(self.bindings_stack)
        return actual_ast

    def toplevel_bindings(self):
        return self.bindings_stack[0]

    # helper

    def handle_all(self, nodes):
        """ Dispatches on all nodes in list """
        processed_nodes = [self.dispatch(child) for child in nodes]
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

    def pattern_from_constructor(self, w_constructor):
        _tag = w_constructor.get_tag()
        _children = [pattern(w_constructor.get_child(i)) \
                    for i in range(w_constructor.get_number_of_children())]
        return pattern.ConstructorPattern(_tag, _children)


    def make_string(self, node, strip=True):
        string = node.additional_info
        if strip:
            s = model.W_String(string[1:len(string)-1])
        else:
            s = model.W_String(string)
        return s

    def make_lambda(self, node, name=""):
        l = model.W_Lambda(rules=[], name=name)
        with Scope(self):
            if name != "":
                self.define(name, l)
            rules = self.handle_all(node.children)
            l._rules = rules
            return l

    def pos(self, node):
        try:
            return node.getsourcepos()
        except IndexError, e:
            return None

    # detokenization
    def visit_NAME(self, node):
        return self.make_string(node, strip=False)

    def visit_QSTRING(self, node):
        return self.make_string(node)
    def visit_QQSTRING(self, node):
        return self.make_string(node)

    def visit_INTEGER(self, node):
        n = model.W_Integer(int(node.additional_info))
        return n

    # def visit_FLOAT(self, node):
    #     f = model.W_Float(float(node.additional_info))
    #     return f


    # productions

    def visit_definition(self, node):
        assert len(node.children) == 2
        name = self.visit_NAME(node.children[0])
        assert isinstance(name, model.W_String)
        if node.children[1].symbol == "lambda":
            definee = self.make_lambda(node.children[1], name.value())
        else:
            definee = self.dispatch(node.children[1])
        self.define(name.value(), definee)
        return no_result

    def visit_lambda(self, node):
        return self.make_lambda(node)

    def visit_rule(self, node):
        if len(node.children) == 1:
            patterns_ = None
            effects_  = node.children[0]
        else:
            patterns_ = node.children[0]
            effects_  = node.children[1]

        with Scope(self):
            with RulePatterns(self):
                patterns = self.dispatch(patterns_) if patterns_ else []
            with RuleEffects(self):
                effects = self.dispatch(effects_)

        return expression.Rule(patterns, effects)

    def visit_patterns(self, node):
        return self.handle_all(node.children)

    def visit_primary_pattern(self, node):
        assert len(node.children) == 1
        primary = self.handle_all(node.children)[0]
        if isinstance(primary, model.W_Integer):
            return pattern.IntegerPattern(primary.value())
        elif isinstance(primary, model.W_String):
            return pattern.StringPattern(primay.value())
        else:
            reason = "Unknown pattern %s " % primary
            raise ParseError(node.getsourcepos(), reason)

    def visit_variable_pattern(self, node):
        children = self.handle_all(node.children)
        assert len(children) == 1
        name = children[0].value()
        if name.startswith("_"):
            return pattern.VariablePattern(expression.Variable(name))

        try:
            found = self.lookup(name)
            if isinstance(found, model.W_Integer):
                return pattern.IntegerPattern(found.value())
            elif isinstance(found, model.W_String):
                return pattern.StringPattern(found.value())
            elif isinstance(found, model.W_Constructor):
                return self.pattern_from_constructor(found)
            if isinstance(found, expression.Variable):
                reason = "Variable already defined: %s " % name
            else:
                reason = "Unknown value bound to %s" % name
            raise ParseError(node.getsourcepos(), reason)
        except KeyError:
            var = expression.Variable(name)
            self.define(name, var)
            return pattern.VariablePattern(var)

    def visit_constructor_pattern(self, node):
        children = self.handle_all(node.children)
        name = children[0].value()
        if len(children) == 1:
            return pattern.ConstructorPattern(model.tag(name, 0), [])
        else:
            ch = children[1]
            tag = model.tag(name, len(ch))
            return pattern.ConstructorPattern(tag, ch)

    def visit_constructor_pattern_args(self, node):
        children = self.handle_all(node.children)
        return children

    def visit_constructor(self, node):
        children = self.handle_all(node.children)
        assert len(children) == 2
        name = children[0].value()
        ch = children[1]
        return model.w_constructor(model.tag(name, len(ch)), ch)

    def visit_constructor_args(self, node):
        return self.handle_all(node.children)

    def visit_variable(self, node):
        children = self.handle_all(node.children)
        assert len(children) == 1
        name = children[0].value()
        try:
            var = self.lookup(name)
        except KeyError:
            reason = "Unbound variable %s" % name
            raise ParseError(node.getsourcepos(), reason)
        else:
            if isinstance(var, expression.Variable) and \
               self.rule_effect_tracker > 0:
                return expression.W_VariableExpression(var)
            else:
                return var


    def visit_application(self, node):
        children = self.handle_all(node.children)
        if len(children) == 1:
            return expression.w_call(children[0], [])
        else:
            return expression.w_call(children[0], children[1])

    def visit_application_args(self, node):
        return self.handle_all(node.children)

    def visit_primitive(self, node):
        children = self.handle_all(node.children)
        assert len(children) == 1
        name = children[0].value()
        return primitive.lookup(name)

    # top level production
    def visit_lamb_source(self, node):
        return self.handle_all(node.children)

    # # general visiting
    # def general_nonterminal_visit(self, node):
    #     # print "g_n_v:\t", type(node), node
    #     new_node = FooNode(children=self.handle_all(node.children),
    #                              symbol=node.symbol,
    #                     source_position=node.getsourcepos())
    #     # TODO
    #     return new_node

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
     p = Parser(filename, is_file=True)
     result = [element for element in p.parse() if element is not no_result]
     bindings = p.toplevel_bindings()
     return (result, bindings)

############################################################################

# generated code between this line and its other occurence
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
    return make_lamb_parser_dynamic()
#    return make_lamb_parser_generated()

############################################################################
if __name__ == '__main__':
    f = py.path.local(__file__)
    oldcontent = f.read()
    s = "# GENERATED CODE BETWEEN THIS LINE AND ITS OTHER OCCURENCE\n".lower()
    pre, gen, after = oldcontent.split(s)

    parser, lexer, ToAST = make_lamb_parser_dynamic()
    transformer = ToAST.source
    newcontent = "%s%s%s\nparser = %r\nlexer = %r\n%s%s" % (
            pre, s, transformer.replace("ToAST", "LambToAST"),
            parser, lexer, s, after)
    print newcontent
    f.write(newcontent)
