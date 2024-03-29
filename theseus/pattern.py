#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit

from rpython.rlib.debug import debug_start, debug_stop, debug_print

from theseus.object import Object
from theseus.util.repr import uni, who, urepr


class Pattern(Object):

    def match(self, an_obj, binding):
        raise NotImplementedError("abstract method")

    def update_number_of_variables(self, rule):
        pass

class IntegerPattern(Pattern):

    _immutable_fields_ = ['value']

    def __init__(self, value):
        self.value = value

    def match(self, obj, binding):
        from theseus.model import W_Integer
        if isinstance(obj, W_Integer): # pragma: no branch
            if obj._value == self.value:
                return
        raise NoMatch()

class StringPattern(Pattern):

    _immutable_fields_ = ['value']

    def __init__(self, value):
        self.value = value

    def match(self, obj, binding):
        from theseus.model import W_String
        if isinstance(obj, W_String): # pragma: no branch
            if obj._value == self.value:
                return
        raise NoMatch()

class VariablePattern(Pattern):

    _immutable_fields_ = ['variable']

    def __init__(self, variable):
        self.variable = variable

    def match(self, obj, binding):
        assert self.variable.binding_index != -1 # bound
        assert binding[self.variable.binding_index] is None
        binding[self.variable.binding_index] = obj

    def update_number_of_variables(self, rule):
        assert self.variable.binding_index == -1 # unbound
        self.variable.binding_index = rule.maximal_number_of_variables
        rule.maximal_number_of_variables += 1

class ConstructorPattern(Pattern):

    _immutable_fields_ = ['_tag', '_children[*]']

    def __init__(self, tag, children=None):
        self._tag = tag
        self._children = children or []
        assert self._tag.arity() == len(self._children)

    @jit.unroll_safe
    def match(self, obj, binding):
        from theseus.execution import W_Constructor
        if not isinstance(obj, W_Constructor):
            raise NoMatch()

        tag = jit.promote(obj.get_tag())
        if tag is self._tag:
            for i in range(tag.arity()):
                self._children[i].match(obj.get_child(i), binding)
            return
        raise NoMatch()

    def update_number_of_variables(self, rule):
        for child in self._children:
            child.update_number_of_variables(rule)


class NoMatch(Exception):
    pass
