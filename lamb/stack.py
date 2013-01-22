#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb.util.repr import urepr, uni
from lamb.util.testing import HelperMixin

class StackElement(HelperMixin):
    _mixin_ = True

    def __init__(self, next): # pragma: no cover
        # never actually called
        self._next = next
    
    #
    # useful when inspecing the stack
    #
    def linearize(self):
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
        if not (hasattr(self, '_next') and self._next is not None):
            return u"⊥"
        else:
            return u"<%s[%h]>" % (self.__class__, id(self))

class ExecutionStackElement(StackElement):
    pass

class OperandStackElement(HelperMixin):

    def __init__(self, data=None, next=None):
        self._data = data
        self._next = next
    
    #
    # useful when inspecing the stack
    #
    def linearize(self): 
        element = self
        ret = []
        while element is not None:
            ret.insert(0, element)
            element = element._next
        return ret
    
    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        r = u""
        if self.is_bottom():
            r += u"⊥"
        if self._data is not None:
            r += urepr(self._data, seen)
        return r

