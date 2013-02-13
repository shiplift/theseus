#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
from rpython.rlib import jit

from lamb.util.repr import uni, who, urepr
from lamb.util.testing import HelperMixin


class Shape(HelperMixin):
    def _init_children(self, w_c, children):
        pass

    def _update_child(self, new_children, children, index):
        pass
    
    def get_child(self, w_c, index):
        raise NotImplementedError("abstract method")
    
    def get_children(self, w_c):
        raise NotImplementedError("abstract method")
    
    def get_number_of_direct_children(self):
        raise NotImplementedError("abstract method")

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        res = u"σ"
        res += u"%d" % self.get_number_of_direct_children()
        return res2

class ConstructorShape(Shape):

    _immutable_files_ = ['_tag', '_structure[*]'] 

    def __init__(self, tag, structure):
        self._structure = structure
        self._tag = tag

    @jit.unroll_safe
    def _init_children(self, w_c, children):
        assert self._tag == w_c._tag
        num_storage = self.get_number_of_direct_children()
        the_storage = [None] * num_children
        for index in range(num_children):
            self._structure[index]._update_child(the_storage, children, index)
        w_c._storage = the_storage

    def _update_child(self, new_storage, storage, index):
        # TODO: optimize here.
        new_storage[index] = storage[index]
        # subshape = child._shape
        # for index in range(subshape.get_number_of_direct_children()):
        #     subshape._structure[index]._update_child(new_children, subshape.get_child(child, index))

    def get_child(self, w_c, index):
        try:
            return w_c._storage[index]
        except IndexError, e:
            raise e

    def get_children(self, w_c):
        return w_c._storage
    

    def get_number_of_direct_children(self):
        return self._tag.arity if self._tag else len(self._structure)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        res = u"σ"
        res += urepr(self._tag, seen)
        return res


def singleton(cls):
    instances = {}
    def getinstance():
        if cls not in instances:
            instances[cls] = cls()
        return instances[cls]
    return getinstance

@singleton
class InStorageShape(Shape):

    def _update_child(self, new_storage, storage, index):
        new_storage[index] = storage[index]

    def get_child(self, w_c, index):
        return w_c

    def get_number_of_direct_children(self):
        return 0
