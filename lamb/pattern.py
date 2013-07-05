#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit

from lamb.object import Object
from lamb.util.repr import uni, who, urepr


class Pattern(Object):

    def match(self, an_obj, binding):
        raise NotImplementedError("abstract method")

    def update_number_of_variables(self, rule):
        pass

class IntegerPattern(Pattern):

    def __init__(self, value):
        self.value = value

    def match(self, obj, binding):
        from lamb.model import W_Integer
        if isinstance(obj, W_Integer): # pragma: no branch
            if obj._value == self.value:
                return
        raise NoMatch()

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"&" + unicode(repr(self.value))

class VariablePattern(Pattern):

    _immutable_fields_ = ['variable']

    def __init__(self, variable):
        self.variable = variable

    def match(self, obj, binding):
        assert self.variable.binding_index != -1 # recordec
        if binding[self.variable.binding_index] is None:
            # unbound -> bind
            binding[self.variable.binding_index] = obj
        else:
            # bound -> assert equality
            if binding[self.variable.binding_index] != obj:
                raise NoMatch()

    def update_number_of_variables(self, rule):
        if self.variable.binding_index == -1: # un-recorded
            self.variable.binding_index = rule.maximal_number_of_variables
            rule.maximal_number_of_variables += 1

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self.variable, seen)


class ConstructorPattern(Pattern):

    _immutable_fields_ = ['_tag', '_children[*]']

    def __init__(self, tag, children=None):
        self._tag = tag
        self._children = children or []
        assert self._tag.arity == len(self._children)

    @jit.unroll_safe
    def match(self, obj, binding):
        from lamb.execution import W_Constructor
        if not isinstance(obj, W_Constructor):
            raise NoMatch()

        tag = jit.promote(obj.get_tag())
        if tag is self._tag:
            for i in range(tag.arity):
                self._children[i].match(obj.get_child(i), binding)
            return
        raise NoMatch()

    def update_number_of_variables(self, rule):
        for child in self._children:
            child.update_number_of_variables(rule)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self._tag, seen) + u"(" + u", ".join(map(lambda x: urepr(x, seen), self._children)) + u")"

class NoMatch(Exception):
    pass
