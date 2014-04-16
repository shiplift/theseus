#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb import model
from rpython.rlib import jit


# Primitives
class UnsupportedPrimitive(Exception):
    def __init__(self, name):
        self.name = name


class PrimitiveHolder(object):
    _immutable_fields_ = ["prim_table[*], lookup_table"]


prim_table = []
lookup_table = {}

@jit.elidable
def _index_for_name(name):
    try:
        return lookup_table[name]
    except IndexError:
        raise UnsupportedPrimitive(name)

def lookup(name):
    try:
        return prim_table[_index_for_name(name)]
    except LookupError:
        raise UnsupportedPrimitive(name)


def define(name, val):
    i = len(prim_table)
    prim_table.append(val)
    lookup_table[name] = i

primitives = PrimitiveHolder()
primitives.prim_table = prim_table
primitives.lookup_table = lookup_table

generic = object()


def expose_primitive(name=None, num_args=None, unwrap_spec=None):
    def decorator(func,name=name, num_args=num_args, unwrap_spec=unwrap_spec):
        if name is None:
            name = func.func_name
        assert name not in lookup_table
        func.func_name = "prim_" + name

        wrapped = wrap_primitive(
            num_args=num_args,
            unwrap_spec=unwrap_spec
        )(func)
        wrapped.func_name = "wrap_prim_" + name
        if num_args is None:
            assert unwrap_spec is not None
            num_args = len(unwrap_spec)
        primitive = model.W_Primitive(wrapped, num_args, name)
        define(name, primitive)
        return func
    return decorator


def wrap_primitive(num_args=None, unwrap_spec=None):
    "NOT_RPYTHON"
    # some serious magic, don't look
    import inspect
    from rpython.rlib.unroll import unrolling_iterable

    def decorator(func):
        if unwrap_spec is None:
            assert num_args is not None
            def wrapped(w_arguments):
                assert len(w_arguments) == num_args
                w_result = func(w_arguments)
                return w_result
            return wrapped

        # unwrap_spec not None.
        len_unwrap_spec = len(unwrap_spec)
        assert num_args is None or num_args == len_unwrap_spec
        actual_arglen = len(inspect.getargspec(func)[0])

        assert (len_unwrap_spec == actual_arglen), \
            "wrong number of unwrap arguments (%d for %d) in %r" % (
                len_unwrap_spec, actual_arglen, func)
        unrolling_unwrap_spec = unrolling_iterable(enumerate(unwrap_spec))
        def wrapped(w_arguments):
            assert len(w_arguments) == len_unwrap_spec
            args = ()
            for i, spec in unrolling_unwrap_spec:
                w_arg = w_arguments[i]
                if False: pass
                elif spec is generic:
                    assert isinstance(w_arg, model.W_Object)
                    args += (w_arg, )
                elif spec is int:
                    assert isinstance(w_arg, model.W_Integer)
                    args += (w_arg.value(), )
                # elif spec is float:
                #     assert isinstance(w_arg, model.W_Float)
                #     args += (interpreter.space.unwrap_float(w_arg), )
                elif spec is str:
                    assert isinstance(w_arg, model.W_String)
                    args += (w_arg.value(), )
                # elif spec is list:
                #     assert isinstance(w_arg, model.W_MutableArray)
                #     args += (interpreter.space.unwrap_array(w_arg), )
                else:
                    raise NotImplementedError(
                        "unknown unwrap_spec %s" % (spec, ))
            w_result = func(*args)
            return w_result
        return wrapped
    return decorator

@expose_primitive(unwrap_spec=[])
def currentmilliseconds():
    import time
    return model.w_integer(int(time.clock()*1000))

@expose_primitive("-", unwrap_spec=[int, int])
def minus(x, y):
    return model.w_integer(x - y)

@expose_primitive("+", unwrap_spec=[int, int])
def plus(x, y):
    return model.w_integer(x + y)

@expose_primitive("*", unwrap_spec=[int, int])
def mult(x, y):
    return model.w_integer(x * y)

@expose_primitive("/", unwrap_spec=[int, int])
def div(x, y):
    return model.w_integer(x / y)


@expose_primitive(unwrap_spec=[int])
def print_int(x):
    from lamb.util.construction_helper import nil
    print x
    return nil()

# EOF
