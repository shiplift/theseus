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

    def get_children(self, w_c):
        raise NotImplementedError("abstract method")

    def get_number_of_direct_children(self):
        raise NotImplementedError("abstract method")

    def extract_child(self, w_c, index):
        raise NotImplementedError("abstract method")

    def fusion(self, children):
        return (self, children)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        res = u"σ"
        res += u"%d" % self.get_number_of_direct_children()
        return res

class CompoundShape(Shape):

    _immutable_files_ = ['_tag', '_structure[*]'] 

    def __init__(self, tag, structure):
        self._structure = structure
        self._tag = tag
        self.know_transformations = {}

    def get_child(self, w_c, index):
        try:
            return self.extract_child(w_c, index)
        except IndexError, e:
            raise

    @jit.unroll_safe
    def get_children(self, w_c):
        return [self.get_child(w_c, index) for index in range(self.get_number_of_direct_children())]


    def get_number_of_direct_children(self):
        return self._tag.arity if self._tag else len(self._structure)

    def extract_child(self, w_c, index):
        storage_index = self.structure_to_storage(index)
        newlen = self._structure[index].storage_width()
        new_storage = w_c._storage[storage_index:storage_index+newlen]
        return self._structure[index].build_child(new_storage)

    def structure_to_storage(self, index):
        offset = 0
        for i in range(index):
            subshape = self._structure[i]
            offset += subshape.storage_width()
        return offset

    def storage_width(self):
        return sum(subshape.storage_width() for subshape in self._structure)

    def build_child(self, new_children):
        return self._tag.constructor_class(self, new_children)

    #
    # shape merge/fusion
    #
    def fusion(self, children):
        u"""
        fusion ≔ Shape × [W_Object] → Shape' × [W_Object]'
        """
        return self.fusion_transforms(children, self.know_transformations)

    def fusion_transforms(self, storage, transformations):
        if len(storage) < 1:
            # nothing to do
            return (self, storage)

        # dynamic programming would be cool here.

        current_storage = storage
        storage_index = index = 0
        shape = self

        while index < len(shape._structure):
            child = current_storage[storage_index]
            subshape = shape._structure[index]
            new_shape = transformations.get((index, subshape), None)

            if new_shape is not None:
                structure = list(shape._structure)
                structure[index] = new_shape
                shape = shape.__class__(shape._tag, structure)

                #
                # We splice the subchildren into ours:
                #
                # index = 1
                # storage = [a, b, c]
                # b has children [x, y]
                # =>
                # new_storage = [a, x, y, c]
                #
                num_children = child.get_number_of_children()
                new_storage = [None] * (len(current_storage) - 1 + num_children)

                for pre_index in range(storage_index):
                    new_storage[pre_index] = current_storage[pre_index]
                for child_index in range(num_children):
                    subchild = child.get_child(child_index)
                    new_storage[storage_index + child_index] = subchild
                for post_index in range(storage_index + 1, len(current_storage)):
                    new_storage[post_index + num_children - 1] = current_storage[post_index]

                current_storage = new_storage
                storage_index += num_children
            else:
                storage_index += subshape.get_number_of_direct_children()
                #storage_index += 1

            index += 1

        return (shape, current_storage)

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

    def extract_child(self, w_c, index):
        return w_c._storage[index]

    def get_number_of_direct_children(self):
        return 0

    def storage_width(self):
        return 1

    def build_child(self, new_children):
        return new_children[0]



