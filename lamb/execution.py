#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import compute_identity_hash, r_dict

from lamb.util.debug import debug_stack
from lamb.stack import ExecutionStackElement, OperandStackElement

from lamb.pattern import NoMatch
from lamb.model import W_Object, W_Constructor, W_Lambda
from lamb.shape import (default_shape, find_shape_tuple,
                        CompoundShape, InStorageShape)
from lamb.expression import W_LambdaCursor, W_ConstructorCursor, W_Cursor
#
#
#
#  Support for the JIT.
#
#
def get_printable_location(current_cursor, current_args_shapes): #pragma: no cover
    res = ""
    if current_cursor is None:
        res += "<None>"
    else:
        if isinstance(current_cursor, W_LambdaCursor):
            res += "Lamb[%s/%s] " % (current_cursor._lamb._name, current_cursor._lamb.arity())
        elif isinstance(current_cursor, W_ConstructorCursor):
            res +=  "Cons[%s/%s] " % (current_cursor._tag.name, current_cursor._tag.arity)
        else:
            return "<Unknown>"
        res += current_args_shapes.merge_point_string()
    return res

jitdriver = jit.JitDriver(
    greens=["current_cursor", "current_args_shapes"],
    reds=["op_stack", "ex_stack", "expr"],
    get_printable_location=get_printable_location,
)

# shortcuts to access stack content.
def ex_data_or_none(stack): return stack._data if stack is not None else None
def op_data_or_none(stack): return stack._data if stack is not None else None


@jit.unroll_safe
def _stack_to_list(op_stack, depth):
    """
    transform `op_stack` of (possibly) W_Constructors into
    list of Shapes, if they have
    """
    op_s = op_stack
    shapes = [None] * depth
    for i in range(depth):
        w = op_data_or_none(op_s)
        shapes[i] = w._shape if isinstance(w, W_Constructor) else None
        op_s = op_s._next if op_s is not None else None
    return shapes

def shapes_of_current_args(depth, op_stack):
    shapes = _stack_to_list(op_stack, depth)
    tup = find_shape_tuple(shapes)
    return tup

def interpret(expression_stack, arguments_stack=None, debug=False, debug_callback=None):

    op_stack = arguments_stack
    ex_stack = expression_stack

    # jit greens
    expr = None
    current_cursor = None
    current_args_shapes = None

    if debug_callback is None: debug_callback = debug_stack

    while True:
        ex_data = ex_data_or_none(ex_stack)
        if isinstance(ex_data, W_Cursor):
            current_cursor = jit.promote(ex_data)
            if isinstance(current_cursor, W_LambdaCursor):
                current_args_shapes = shapes_of_current_args(current_cursor._lamb.arity(), op_stack)
            elif isinstance(current_cursor, W_ConstructorCursor):
                current_args_shapes = shapes_of_current_args(current_cursor._tag.arity, op_stack)

            # print "cursor", current_cursor
            # print "args\t", current_args_shapes
            jitdriver.can_enter_jit(
                expr=expr, op_stack=op_stack, ex_stack=ex_stack,
                current_cursor=current_cursor,
                current_args_shapes=current_args_shapes,
            )
        jitdriver.jit_merge_point(
            expr=expr, op_stack=op_stack, ex_stack=ex_stack,
            current_cursor=current_cursor, current_args_shapes=current_args_shapes
        )
        if ex_stack is None:
            break


        if debug: debug_callback({'ex_stack':ex_stack, 'op_stack':op_stack})
        expr = ex_stack._data
        ex_stack = ex_stack._next
        (op_stack, ex_stack) = expr.interpret(op_stack, ex_stack)

    if debug: debug_callback({'ex_stack':ex_stack, 'op_stack':op_stack})
    return op_stack._data
