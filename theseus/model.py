#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
"""

  W_Object
    W_Tag
    W_Integer
    W_String
    W_Constructor
      W_NAryConstructor
      W_Constructor....
    W_Lambda
      W_Primitive

"""
from rpython.rlib import jit, rbigint
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import compute_identity_hash, r_dict, not_rpython
from rpython.rlib.debug import debug_start, debug_stop, debug_print

from theseus.object import Object

from theseus.shape import (CompoundShape, in_storage_shape, default_shape,
                        integer_shape)
from theseus.pattern import NoMatch
from theseus.small_list import inline_small_list


class W_Object(Object):

    _attrs_ = []

    def shape(self):
        return in_storage_shape
    
    def _replace_with_constructor_expression(self):
        from theseus.expression import Quote
        return Quote(self)
    def merge_point_string(self):
        return "<unknown: %s>" % self

class W_Tag(W_Object):
    tags = {}

    _immutable_fields_ = ['name', '_arity', 'default_shape']

    def __init__(self, name, arity):
        self.name = name
        assert arity >= 0
        self._arity = arity
        self.default_shape = default_shape(self, arity)

    def arity(self):
        return self._arity

    #
    # Tags compare by identity
    #
    def __eq__(self, other): #pragma: no cover
        return self is other

def tag(name, arity):
    assert isinstance(name, str)
    assert isinstance(arity, int)
    tag_ = (name, arity)
    w_tag = W_Tag.tags.get( tag_ , None)
    if w_tag is None:
        w_tag = W_Tag(name, arity)
        W_Tag.tags[tag_] = w_tag

    assert isinstance(w_tag, W_Tag)
    return w_tag

class W_Integer(W_Object):

    _immutable_fields_ = ['_value']

    def __init__(self, value):
        self._value = value
    def value(self):
        return self._value
    def merge_point_string(self):
        return "%d" % self._value
    # def shape(self):
    #     return integer_shape


def w_integer(value):
    return W_Integer(value)

class W_Float(W_Object):

    _immutable_fields_ = ['_value']

    def __init__(self, value):
        self._value = value
    def value(self):
        return self._value
    def merge_point_string(self):
        return "%f" % self.value()


def w_float(value):
    return W_Float(value)

class W_Bignumber(W_Object):
    _immutable_fields_ = ["_value"]

    def __init__(self, value):
        self._value = value
    def value(self):
        return self._value
    def merge_point_string(self):
        return self._value.str()

def w_bignumber(value):
    assert isinstance(value, rbigint.rbigint)
    return W_Bignumber(value)

class W_String(W_Object):

    _immutable_fields_ = ['_value']
    def __init__(self, value):
        self._value = value
    def value(self):
        return self._value
    def merge_point_string(self):
        return "%s" % self._value

def w_string(value):
    # assert isinstance(value, str)
    return W_String(value)

@inline_small_list(sizemax=31,
                   immutable=True, nonull=True,
                   attrname="_storage",
                   listgettername="get_storage",
                   listsizename="get_storage_width", gettername="get_storage_at"
)
class W_Constructor(W_Object):

    #_immutable_ = True
    _immutable_fields_ = ['_shape']

    def __init__(self, shape):
        assert isinstance(shape, CompoundShape)
        self._shape = shape

    def get_tag(self):
        return self.shape()._tag

    def get_children(self):
        return self.shape().get_children(self)

    def get_child(self, index):
        return self.shape().get_child(self, index)

    def get_number_of_children(self):
        return self.shape().get_number_of_direct_children()
    
    def shape(self):
        return jit.promote(self._shape)

    @not_rpython
    def __eq__(self, other):
        if isinstance(other, W_Constructor):
            if self.get_number_of_children() == other.get_number_of_children():
                return self.get_children() == other.get_children()
        return False

    def merge_point_string(self):
        return "%s/%s" % (self.get_tag().name, self.get_tag().arity())

    # for convenience
    @staticmethod
    def construct(shape, storage):
        return W_Constructor.make(storage, shape)

def prepare_constructor(tag, children):
    """
    create what is necessary to build a constructor.
    """
    pre_shape = tag.default_shape
    shape, storage = pre_shape.fusion(children)
    return (shape, storage)

SHOT=False
def w_constructor(tag, children):
    if SHOT:
        import pdb; pdb.set_trace()
    shape, storage = prepare_constructor(tag, children)
    return W_Constructor.construct(shape, storage)

class W_Lambda(W_Object):
    """
    λ arity is the number of patterns in the first rule, or zero
    """

    _immutable_fields_ = ['_rules[*]']

    def __init__(self, rules=[], name=""):
        self._rules = rules
        self._name = name

    @jit.elidable
    def _rule_arity(self):
        assert len(self._rules) > 0
        return self._rules[0].arity()

    def arity(self):
        return self._rule_arity()
    def merge_point_string(self):
        return "%s/%d" % (self._name, self.arity())

class W_Primitive(W_Lambda):
    """
    like a λ, but calls a rpython function instead.
    """
    _immutable_fields_ = ['_fun', '_arity']
    def __init__(self, fun, arity, name=""):
        W_Lambda.__init__(self, [], name)
        self._arity = arity
        self._fun = fun

    def arity(self):
        return self._arity
