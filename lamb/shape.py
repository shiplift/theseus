#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
from rpython.rlib import jit

from lamb.util.repr import uni, who, urepr
from lamb.util.testing import HelperMixin


def _splice(array, index, insertion):
    u"""
    We splice insertion into array at index:

    index = 1
    array = [a, b, c]
    insertion = [x, y]
    =>
    new_storage = [a, x, y, c]
    """
    array_len = len(array)
    insertion_len = len(insertion)
    new_len = array_len + insertion_len - 1
    new_array = [None] * new_len

    for pre_index in range(index):
        new_array[pre_index] = array[pre_index]
    for insert_index in range(insertion_len):
        new_array[index + insert_index] = insertion[insert_index]
    for post_index in range(index + 1, array_len):
        new_array[post_index + insertion_len - 1] = array[post_index]

    return new_array


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
        self.known_transformations = {}

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

    def get_storage(self, w_c):
        return w_c._storage

    def storage_width(self):
        return sum(subshape.storage_width() for subshape in self._structure)

    def build_child(self, new_children):
        return self._tag.constructor_class(self, new_children)

    #
    # shape merge/fusion
    #
    def fusion(self, storage):
        u"""
        fusion ≔ Shape × [W_Object] → Shape' × [W_Object]'
        """
        from lamb.execution import W_Constructor

        if len(storage) < 1:
            # nothing to do
            return (self, storage)

        current_storage = storage
        storage_index = index = 0
        shape = self
        structure = shape._structure

        while index < len(structure):
            subshape = structure[index]

            new_shape = shape.known_transformations.get((index, subshape), None)
            if new_shape is not None and new_shape != shape:

                child = current_storage[storage_index]
                child_storage = child._storage if isinstance(child, W_Constructor) else [child]
                new_storage = _splice(current_storage, storage_index, child_storage)

                current_storage = new_storage
                structure = new_shape._structure
                shape = new_shape

                # rewind over new storage
                storage_index = index = 0
            else:
                storage_index += subshape.storage_width()
                index += 1

        if structure != shape._structure:
            shape = shape.__class__(shape._tag, structure)


        return (shape, current_storage)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        def mini_urepr(x):
            s = set(seen)
            s.discard(x)
            return urepr(x, s)


        res = u"σ"
        res += urepr(self._tag, seen)
        res += u"["
        res += ", ".join(map(mini_urepr, self._structure))
        res += u"]"
        return res

    def print_transforms(self):
        for (index, src), dest in sorted(self.known_transformations.items()):
            print "\t(", index, ", ", src, u") ↦ ", dest


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

    def get_storage(self, w_c):
        return [w_c]
        #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"◊"

