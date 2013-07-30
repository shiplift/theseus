#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Test.
#

from rpython.rlib import jit

from lamb.object import Object

from lamb.util.repr import uni, who, urepr

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


class Shape(Object):
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

    def record_shapes(self, storage):
        pass

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

    def merge_point_string(self):
        return self.merge_point_string_seen([])

    def merge_point_string_seen(self, seen):
        return "<some shape>"


class ShapeConfig(object):

    def __init__(self, substitution_threshold, max_storage_width, ignore_nils):
        self.substitution_threshold = substitution_threshold
        self.max_storage_width = max_storage_width
        self.log_transformations = False
        self.ignore_nils = ignore_nils
        self._inhibit_recognition = False
        self._inhibit_all = False

class CompoundShape(Shape):

    _immutable_fields_ = ['_tag', '_structure[*]']

    _config = ShapeConfig(substitution_threshold=17,
                          max_storage_width=7,
                          ignore_nils=False)

    _shapes = []

    def __init__(self, tag, structure):
        self._structure = structure
        self._tag = tag
        self._hist = {}
        self.known_transformations = {}
        self._shapes.append(self)

    def get_child(self, w_c, index):
        return self.extract_child(w_c, index)

    @jit.unroll_safe
    def get_children(self, w_c):
        new_length = self.get_number_of_direct_children()
        return [self.get_child(w_c, index) for index in range(new_length)]


    def get_number_of_direct_children(self):
        return self._tag.arity

    def extract_child(self, w_c, index):
        storage_index = self.structure_to_storage(index)
        subshape = self._structure[index]
        if subshape is in_storage_shape:
            return w_c.get_storage_at(storage_index)
        else:
            newlen = subshape.storage_width()
            endindex = storage_index + newlen
            assert endindex <= self.storage_width()
            new_storage = (w_c.get_storage())[storage_index:endindex]
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
        from model import W_Constructor
        assert isinstance(w_c, W_Constructor)
        return w_c.get_storage()

    @jit.unroll_safe
    def storage_width(self):
        sum = 0
        for subshape in self._structure:
            sum += subshape.storage_width()
        return sum

    def build_child(self, new_children):
        from model import W_Constructor, select_constructor_class
        (shape, storage) = self.fusion(new_children)
        cls = select_constructor_class(storage)
        constructor = cls(shape)
        constructor._init_storage(storage)
        return constructor

    def replace(self, storage_index, new_shape):
        structure = self._structure[:]
        for i, child in enumerate(structure):
            if storage_index < child.storage_width():
                structure[i] = child.replace(storage_index, new_shape)
                return CompoundShape(self._tag, structure)
            storage_index -= child.storage_width()

    @jit.elidable
    def may_subsitute(self, constructor):
        from util.construction_helper import is_nil
        if self._config.ignore_nils:
            return not is_nil(constructor)
        else:
            return True

    @jit.unroll_safe
    def record_shapes(self, storage):
        from model import W_Constructor

        for i in range(len(storage)):
            child = storage[i]
            if isinstance(child, W_Constructor) and self.may_subsitute(child):
                key = (i, child._shape)
                count = self._hist.get(key, 0)
                width = child.get_storage_width()
                if (key not in self.known_transformations and
                    width <= self._config.max_storage_width and
                    count <= self._config.substitution_threshold):
                    self._hist[key] = count + 1
                    if self._hist[key] >= self._config.substitution_threshold:
                        self.recognize_transformation(i, child._shape)


    def recognize_transformation(self, i, shape):
        new_shape = self.replace(i, shape)
        self.known_transformations[i, shape] = new_shape
        if self._config.log_transformations:
            print "%s/%d\t(%d,%s)\n\t->%s" % (
                self._tag.name, self._tag.arity,
                i, shape.merge_point_string(),
                new_shape.merge_point_string())

    def fusion(self, storage):

        if self._config._inhibit_all:
            return (self, storage)

        if not self._config._inhibit_recognition:
            # We do not record statistics in jitted code,
            # it should be stable beforehand
            if not jit.we_are_jitted():
                self.record_shapes(storage)
        new_shape, new_storage = self.merge(storage)
        return (new_shape, new_storage)


    #
    # shape merge/fusion
    #
    @jit.unroll_safe
    def merge(self, storage):
        u"""
        fusion ≔ Shape × [W_Object] → Shape' × [W_Object]'
        """
        from model import W_Constructor

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
            if new_shape is not shape:

                if isinstance(child, W_Constructor):
                    child_storage = child.get_storage()
                else:
                    child_storage = [child]
                new_storage = _splice(current_storage, storage_len, index,
                                      child_storage, subshape.storage_width())

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
        return self.known_transformations.get((index, subshape), self)

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


    def merge_point_string_seen(self, seen):
        seen.append(self)
        res  = "%s%d{" % (self._tag.name, self._tag.arity)
        first = True
        for subshape in self._structure:
            if first:
                first = False
            else:
                res += ", "
            res += subshape.merge_point_string_seen(seen) if not subshape in seen else "."
        res += "}"
        return res

    def print_transforms(self):
        for (index, src), dest in self.known_transformations.items():
            print "\t(%d,%s) -> %s" % (
                index, src.merge_point_string(), dest.merge_point_string())

    def print_hist(self):
        for (index, src), count in self._hist.items():
            print "\t%d: (%d,%s)" % (
                count, index, src.merge_point_string())

    def __eq__(self, other):
        return (self.__class__  == other.__class__ and
                self._tag       == other._tag and
                self._structure == other._structure)


class InStorageShape(Shape):

    def extract_child(self, w_c, index):
        return w_c.get_storage_at(index)

    def get_number_of_direct_children(self):
        return 0

    def storage_width(self):
        return 1

    def build_child(self, new_children):
        raise NotImplementedError()  #should not happen
        #return new_children[0]

    def get_storage(self, w_c):
        return [w_c]

    def replace(self, storage_index, new_shape):
        assert storage_index == 0
        return new_shape

    ##
    #  for pickle
    def __reduce__(self):
        return ( in_storage_shape_instance, tuple() )

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"◊"

    def merge_point_string_seen(self, seen):
        return "|"

in_storage_shape = InStorageShape()


def in_storage_shape_instance():
    return in_storage_shape


@jit.unroll_safe
def default_shape(tag, arity):
    shape = CompoundShape(tag, [in_storage_shape] * arity)
    return shape

class ShapeTuple(object):
    """
    I am a little bit like the python tuple but I can
    built up myself consecutively and still retain obejct identity.
    """

    _immutable_fields_ = ["shape", "parent"]

    def __init__(self, shape, parent):
        assert isinstance(shape, Shape) or shape is None
        self.shape = shape
        self.parent = parent
        self._route = {}

    @jit.elidable
    def tuple_for_shape(self, shape):
        tup = self._route.get(shape, None)
        if tup is None:
            tup = self.__class__(shape, self)
            self._route[shape] = tup
        return tup

    # #
    # # Testing and Debug
    # #
    # @uni
    # def to_repr(self, seen):
    #     return self.merge_point_string()


    def merge_point_string(self):
        res = ""
        if self.shape is None and self.parent is None:
            return res

        if self.parent is not None:
            res += self.parent.merge_point_string()
        if self.shape is not None:
            res += ".%s" % self.shape.merge_point_string()
        else:
            res += "."
        return res

_empty_tuple = ShapeTuple(None, None)

@jit.unroll_safe
def find_shape_tuple(shape_list):
    tup = _empty_tuple
    for shape in shape_list:
        tup = tup.tuple_for_shape(jit.promote(shape))
    return tup
