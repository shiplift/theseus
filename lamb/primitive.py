#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb import model
from rpython.rlib import jit, rarithmetic, rstring, rfloat, rbigint

from lamb.util.construction_helper import conslist, plist, nil

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
                elif spec is float:
                    assert isinstance(w_arg, model.W_Float)
                    args += (w_arg.value(), )
                elif spec is long:
                    assert isinstance(w_arg, model.W_Bignumber)
                    args += (w_arg.value(), )
                elif spec is str:
                    assert isinstance(w_arg, model.W_String)
                    args += (w_arg.value(), )
                elif spec is list:
                    assert isinstance(w_arg, model.W_Constructor)
                    t = w_arg.get_tag()
                    assert t.arity() == 2
                    args += (plist(w_arg), )
                else:
                    raise NotImplementedError(
                        "unknown unwrap_spec %s" % (spec, ))
            w_result = func(*args)
            return w_result
        return wrapped
    return decorator

################################################################

@expose_primitive(unwrap_spec=[])
def currentmilliseconds():
    import time
    return model.w_integer(int(time.clock()*1000))

@expose_primitive(unwrap_spec=[])
def clock():
    import time
    return model.w_float(time.clock())

###############################################################

@expose_primitive("-", unwrap_spec=[generic, generic])
def minus(w_x, w_y):
    if isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Integer):
        return minus_int(w_x.value(), w_y.value())
    elif isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Float):
        return minus_float(float(w_x.value()), w_y.value())
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Integer):
        return minus_float(w_x.value(), float(w_y.value()))
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Float):
        return minus_float(w_x.value(), w_y.value())
    else:
        assert False

@expose_primitive("+", unwrap_spec=[generic, generic])
def plus(w_x, w_y):
    if isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Integer):
        return plus_int(w_x.value(), w_y.value())
    elif isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Float):
        return plus_float(float(w_x.value()), w_y.value())
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Integer):
        return plus_float(w_x.value(), float(w_y.value()))
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Float):
        return plus_float(w_x.value(), w_y.value())
    else:
        assert False

@expose_primitive("*", unwrap_spec=[generic, generic])
def mult(w_x, w_y):
    if isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Integer):
        return mult_int(w_x.value(), w_y.value())
    elif isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Float):
        return mult_float(float(w_x.value()), w_y.value())
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Integer):
        return mult_float(w_x.value(), float(w_y.value()))
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Float):
        return mult_float(w_x.value(), w_y.value())
    else:
        assert False

@expose_primitive("/", unwrap_spec=[generic, generic])
def div(w_x, w_y):
    if isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Integer):
        return div_int(w_x.value(), w_y.value())
    elif isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Float):
        return div_float(float(w_x.value()), w_y.value())
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Integer):
        return div_float(w_x.value(), float(w_y.value()))
    elif isinstance(w_x, model.W_Float) and isinstance(w_y, model.W_Float):
        return div_float(w_x.value(), w_y.value())
    else:
        assert False
    return model.w_integer(w_x / w_y)

@expose_primitive("%", unwrap_spec=[generic, generic])
def mod(w_x, w_y):
    if isinstance(w_x, model.W_Integer) and isinstance(w_y, model.W_Integer):
        return mod_int(w_x.value(), w_y.value())
    else:
        assert False

################################################################
@expose_primitive(unwrap_spec=[int, int])
def minus_int(x, y):
    return model.w_integer(x - y)

@expose_primitive(unwrap_spec=[int, int])
def plus_int(x, y):
    return model.w_integer(x + y)

@expose_primitive(unwrap_spec=[int, int])
def mult_int(x, y):
    return model.w_integer(x * y)

@expose_primitive(unwrap_spec=[int, int])
def div_int(x, y):
    return model.w_integer(x / y)

@expose_primitive(unwrap_spec=[int, int])
def mod_int(x, y):
    return model.w_integer(x % y)

@expose_primitive(unwrap_spec=[int, int])
def lsl(x, y):
    return model.w_integer(x << y)

@expose_primitive(unwrap_spec=[int, int])
def lsr(x, y):
    return model.w_integer(x >> y)

################################################################
@expose_primitive(unwrap_spec=[long, long])
def minus_bignumber(x, y):
    return model.w_bignumber(x.sub(y))

@expose_primitive(unwrap_spec=[long, long])
def plus_bignumber(x, y):
    return model.w_bignumber(x.add(y))

@expose_primitive(unwrap_spec=[long, long])
def mult_bignumber(x, y):
    return model.w_bignumber(x.mul(y))

@expose_primitive(unwrap_spec=[long, long])
def div_bignumber(x, y):
    return model.w_bignumber(x.div(y))

@expose_primitive(unwrap_spec=[long, long])
def mod_bignumber(x, y):
    return model.w_bignumber(x.mod(y))

# @expose_primitive(unwrap_spec=[int, int])
# def lsl(x, y):
#     return model.w_bignumber(x << y)

# @expose_primitive(unwrap_spec=[int, int])
# def lsr(x, y):
#     return model.w_bignumber(x >> y)

@expose_primitive(unwrap_spec=[int])
def int_to_bignumber(x):
    return model.w_bignumber(rbigint.rbigint.fromint(x))


################################################################
@expose_primitive(unwrap_spec=[float, float])
def minus_float(x, y):
    return model.w_float(x - y)

@expose_primitive(unwrap_spec=[float, float])
def plus_float(x, y):
    return model.w_float(x + y)

@expose_primitive(unwrap_spec=[float, float])
def mult_float(x, y):
    return model.w_float(x * y)

@expose_primitive(unwrap_spec=[float, float])
def div_float(x, y):
    return model.w_float(x / y)

################################################################

# @expose_primitive("Σ*→ℤ", unwrap_spec=[str])
@expose_primitive("strtol", unwrap_spec=[str])
def string_to_int(s):
    return model.w_integer(rarithmetic.string_to_int(
        rstring.replace(s, "_", ""), base=0))

# @expose_primitive("Σ*→ℝ", unwrap_spec=[str])
@expose_primitive("strtof", unwrap_spec=[str])
def string_to_float(s):
    return model.w_float(rfloat.string_to_float(s))

# @expose_primitive("Σ*→ℝ", unwrap_spec=[str])
@expose_primitive("strtob", unwrap_spec=[str])
def string_to_bignumber(s):
    return model.w_bignumber(rbigint.rbigint.fromstr(s))


# @expose_primitive("Σ*→ℤ", unwrap_spec=[str])
@expose_primitive("ltostr", unwrap_spec=[int])
def int_to_string(i):
    return str(i)

################################################################

@expose_primitive(unwrap_spec=[int])
def print_int(x):
    print x
    return nil()

@expose_primitive(unwrap_spec=[long])
def print_bignumber(x):
    print x.str()
    return nil()

@expose_primitive(unwrap_spec=[str])
def print_string(x):
    print x
    return nil()

@expose_primitive(unwrap_spec=[float])
def print_result_string(x):
    " A hacky primitive to quickly generate ReBench out format "
    from lamb.util.construction_helper import nil
    x *= 1000.0
    print "0:RESULT-cpu:ms: %s\n0:RESULT-total:ms: %s" % (x, x)
    return nil()


################################################################

@expose_primitive(unwrap_spec=[])
def inputstring():
    import sys
    return model.w_string(sys.stdin.read())

@expose_primitive(unwrap_spec=[str])
def explode(s):
    return conslist([model.w_string(c) for c in list(s)])

@expose_primitive(unwrap_spec=[list])
def implode(l):
    for w_s in l: assert isinstance(w_s, model.W_String)
    return model.w_string("".join([w_s.value() for w_s in l]))

# EOF
