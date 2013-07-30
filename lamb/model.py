#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
"""

  W_Object
    W_Tag
    W_Integer
    W_Constructor
      W_NAryConstructor
    W_Lambda

"""
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import compute_identity_hash, r_dict

from lamb.object import Object

from lamb.shape import CompoundShape, in_storage_shape, default_shape
from lamb.pattern import NoMatch
from lamb.stack import ExecutionStackElement, OperandStackElement

class W_Object(Object):

    _attrs_ = []

    def shape(self):
        return in_storage_shape


class W_Tag(W_Object):
    tags = {}

    _immutable_fields_ = ['name', 'arity', '_cursor', 'default_shape']

    def __init__(self, name, arity):
        from lamb.expression import W_ConstructorCursor
        self.name = name
        self.arity = arity
        self._cursor = W_ConstructorCursor(self)
        self.default_shape = default_shape(self, arity)

    #
    # Tags compare by identity
    #
    def __eq__(self, other): #pragma: no cover
        return self is other

    #
    # pickle
    def __setstate__(self, state):
        from lamb.expression import W_ConstructorCursor
        self.name = state['name']
        self.arity = state['arity']
        self.default_shape = state['default_shape']
        self._cursor = W_ConstructorCursor(self)


def tag(name, arity):
    assert isinstance(name, str)
    assert isinstance(arity, int)
    w_tag = W_Tag.tags.get( (name, arity) , None)
    if w_tag is None:
        w_tag = W_Tag(name, arity)
        W_Tag.tags[ (name, arity) ] = w_tag

    assert isinstance(w_tag, W_Tag)
    return w_tag

class W_Integer(W_Object):

    def __init__(self, value):
        self._value = value

class W_Constructor(W_Object):

    _immutable_fields_ = ['_shape']

    def __init__(self, shape):
        assert isinstance(shape, CompoundShape)
        self._shape = shape

    def _init_storage(self, stroage):
        pass

    def get_storage(self):
        return []

    def get_storage_at(self, index):
        raise IndexError()

    def get_storage_width(self):
        return 0

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

    def __eq__(self, other):
        if isinstance(other, W_Constructor):
            if self.get_number_of_children() == other.get_number_of_children():
                return self.get_children() == other.get_children()
        return False

class W_NAryConstructor(W_Constructor):

    _immutable_fields_ = ['_storage[*]']

    def _init_storage(self, storage):
        self._storage = storage or []

    def get_storage(self):
        return self._storage

    def get_storage_at(self, index):
        return self._storage[index]

    def get_storage_width(self):
        return len(self._storage)

STORAGE_ATTR_TEMPLATE = "storage_%d"

def constructor_class_name(n_storage):
    return 'W_Constructor%d' % n_storage


def generate_constructor_class(n_storage):

    storage_iter = unrolling_iterable(range(n_storage))

    class constructor_class(W_Constructor):
        _immutable_fields_ = [(STORAGE_ATTR_TEMPLATE % x) for x in storage_iter]

        def _init_storage(self, storage):
            for x in storage_iter:
                setattr(self, STORAGE_ATTR_TEMPLATE % x, storage[x])

        def get_storage(self):
            result = [None] * n_storage
            for x in storage_iter:
                result[x] = getattr(self, STORAGE_ATTR_TEMPLATE % x)
            return result

        def get_storage_at(self, index):
            for x in storage_iter:
                if x == index:
                    return getattr(self, STORAGE_ATTR_TEMPLATE % x)
            raise IndexError

        def get_storage_width(self):
            return n_storage

    constructor_class.__name__ = constructor_class_name(n_storage)
    return constructor_class

constructor_classes = [W_Constructor]
for n_storage in range(1, 10):
    constructor_classes.append(generate_constructor_class(n_storage))

class_iter = unrolling_iterable(enumerate(constructor_classes))

def select_constructor_class(storage):
    length = len(storage)
    for i, cls in class_iter:
        if i == length:
            return cls
    # otherwise:
    return W_NAryConstructor


def prepare_constructor(tag, children):
    """
    create what is necessary to build a constructor.
    """
    pre_shape = tag.default_shape
    shape, storage = pre_shape.fusion(children)
    return (shape, storage)

def w_constructor(tag, children):
    shape, storage = prepare_constructor(tag, children)
    constr_cls = select_constructor_class(storage)
    constr = constr_cls(shape)
    constr._init_storage(storage)
    return constr

class W_Lambda(W_Object):
    """
    λ arity is the number of patterns in the first rule, or zero
    """

    _immutable_fields_ = ['_rules[*]', '_cursor']

    def __init__(self, rules, name=""):
        from lamb.expression import W_LambdaCursor
        self._rules = rules
        self._name = name
        self._cursor = W_LambdaCursor(self)

    @jit.elidable
    def arity(self):
        assert len(self._rules) > 0
        return self._rules[0].arity


    def name(self):
        if len(self._name) > 0:
            return unicode(self._name)
        else:
            return who(self)
