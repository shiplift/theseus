#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb.util.repr import urepr, uni
from lamb.util.testing import HelperMixin

class StackElement(HelperMixin):
    _mixin_ = True

    _attrs_ = ['_next']

    def __init__(self, data=None, next=None):
        self._data = data
        self._next = next
    
    #
    # useful when inspecing the stack
    #
    def linearize(self): # pragma: no cover
        element = self
        ret = []
        while element is not None:
            ret.insert(0, element)
            try:
                element = element._next
            except AttributeError:
                element = None
        return ret
    
    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        r = u""
        if self._next is None:
            r += u"⊥"
        if self._data is not None:
            r += urepr(self._data, seen)
        return r


class ExecutionStackElement(StackElement):
    pass

class OperandStackElement(StackElement):
    pass

