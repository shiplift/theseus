#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
from lamb.util.repr import uni, who, urepr
from lamb.util.testing import HelperMixin


class Shape(HelperMixin):
    def _init_children(self, w_c, children):
        pass

    def _update_child(self, new_children, child):
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
        return res

class ConstructorShape(Shape):

    def __init__(self, structure):
        self._structure = structure
        self._tag = None

    def _init_children(self, w_c, children):
        self._tag = w_c._tag

        the_children = []
        for index in range(self.get_number_of_direct_children()):
            self._structure[index]._update_child(the_children, children[index])
        w_c._children = the_children

    def _update_child(self, new_children, child):
        # TODO: optimize here.
        new_children.append(child)
        # subshape = child._shape
        # for index in range(subshape.get_number_of_direct_children()):
        #     subshape._structure[index]._update_child(new_children, subshape.get_child(child, index))

    def get_child(self, w_c, index):
        try:
            return w_c._children[index]
        except IndexError, e:
            raise e

    def get_children(self, w_c):
        return w_c._children
    

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

    def _update_child(self, new_children, child):
        new_children.append(child)

    def get_child(self, w_c, index):
        return w_c

    def get_number_of_direct_children(self):
        return 0
