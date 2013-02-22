#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#
from rpython.rlib import jit

from lamb.util.repr import uni, who, urepr
from lamb.util.testing import HelperMixin

@jit.unroll_safe
def _splice(array, array_len, index, insertion, insertion_len):
    u"""
    We splice insertion into array at index:

    index = 1
    array = [a, b, c]
    array_len = 3
    insertion = [x, y]
    insertion_len = 2
    =>
    new_storage = [a, x, y, c]
    """
    new_len = array_len + insertion_len - 1
    assert new_len >= 0
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

    _immutable_fields_ = ['_tag', '_structure[*]']

    def __init__(self, tag, structure):
        self._structure = structure
        self._tag = tag
        self.known_transformations = {}

    def get_child(self, w_c, index):
        return self.extract_child(w_c, index)

    @jit.unroll_safe
    def get_children(self, w_c):
        return [self.get_child(w_c, index) for index in range(self.get_number_of_direct_children())]


    def get_number_of_direct_children(self):
        return self._tag.arity #if self._tag else len(self._structure)

    def extract_child(self, w_c, index):
        storage_index = self.structure_to_storage(index)
        subshape = self._structure[index]
        if subshape is InStorageShape():
            return w_c._storage[storage_index]
        else:
            newlen = subshape.storage_width()
            endindex = storage_index + newlen
            assert endindex <= self.storage_width()
            new_storage = w_c._storage[storage_index:endindex]
            return subshape.build_child(new_storage)

    @jit.unroll_safe
    def structure_to_storage(self, index):
        offset = 0
        structure = self._structure
        for i in range(index):
            subshape = structure[i]
            offset += subshape.storage_width()
        return offset

    def get_storage(self, w_c):
        from execution import W_Constructor
        assert isinstance(w_c, W_Constructor)
        return w_c._storage

    @jit.unroll_safe
    def storage_width(self):
        sum = 0
        for subshape in self._structure:
            sum += subshape.storage_width()
        return sum

    def build_child(self, new_children):
        from execution import W_Constructor
        (shape, storage) = self.fusion(new_children)
        return W_Constructor(shape, storage)

    #
    # shape merge/fusion
    #
    @jit.unroll_safe
    def fusion(self, storage):
        u"""
        fusion ≔ Shape × [W_Object] → Shape' × [W_Object]'
        """
        from lamb.execution import W_Constructor

        current_storage = storage
        index = 0
        shape = self
        storage_len = shape.storage_width()
        
        if storage_len < 1:
            # nothing to do
            return (self, storage)

        while index < storage_len:
            child = current_storage[index]
            subshape = child.shape()

            new_shape = shape.get_transformation(index, subshape)
            if new_shape is not None and new_shape != shape:

                child_storage = child._storage if isinstance(child, W_Constructor) else [child]
                new_storage = _splice(current_storage, storage_len, index, child_storage, subshape.storage_width())

                current_storage = new_storage
                shape = new_shape
                storage_len = shape.storage_width()

                # rewind over new storage
                index = 0
            else:
                index += 1

        return (shape, current_storage)

    @jit.elidable
    def get_transformation(self, index, subshape):
        return self.known_transformations.get((index, subshape), None)

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
        raise NotImplementedError()  #should not happen
        #return new_children[0]

    def get_storage(self, w_c):
        return [w_c]
        #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"◊"

