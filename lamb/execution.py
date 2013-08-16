#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.debug import debug_start, debug_stop, debug_print

from lamb.stack import ExecutionStackElement, OperandStackElement, Stack

from lamb.pattern import NoMatch
from lamb.model import W_Object, W_Constructor, W_Lambda, w_constructor
from lamb.shape import (default_shape, find_shape_tuple,
                        CompoundShape, InStorageShape)
from lamb.expression import (W_LambdaCursor, W_ConstructorCursor, W_Cursor,
                             W_ConstructorEvaluator, W_VariableExpression,
                             W_Call, W_NAryCall, VariableUnbound)

#
# Execution behavior.
#
class __extend__(W_Object):
    def evaluate_with_binding(self, binding):
        return self.copy(binding).evaluate()

    def evaluate(self):
        return self

    def interpret(self, op_stack, ex_stack):
        return (OperandStackElement(self, op_stack), ex_stack)

class __extend__(W_Constructor):
    def evaluate(self):
        return w_constructor(self.get_tag(), [child.evaluate() for child in self.get_children()])

class __extend__(W_Lambda):
    def call(self, w_arguments):
        assert len(w_arguments) == self.arity()
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(w_arguments, binding)
            except NoMatch:
                pass
            else:
                return expression.copy(binding).evaluate()

        raise NoMatch()

    @jit.unroll_safe
    def interpret_lambda(self, op_stack, ex_stack):
        jit.promote(self)
        num_args = self.arity()
        w_arguments = [None] * num_args
        for i in range(num_args):
            w_arguments[i] = op_stack._data
            op_stack = op_stack._next
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(w_arguments, binding)
            except NoMatch:
                pass
            else:
                resolved = expression.copy(binding)
                ex_stack = ExecutionStackElement(resolved, ex_stack)
                return (op_stack, ex_stack)
        raise NoMatch()

class __extend__(W_ConstructorEvaluator):
    def evaluate(self):
        return w_constructor(self._tag,
                             [child.evaluate() for child in self._children])

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        ex_stack = ExecutionStackElement(self._tag._cursor, ex_stack)
        for child in self._children:
            ex_stack = ExecutionStackElement(child, ex_stack)
        return (op_stack, ex_stack)

class __extend__(W_VariableExpression):
    def evaluate(self): # pragma: no cover
        # should not happen
        raise VariableUnbound()

    def interpret(self, op_stack, ex_stack): # pragma: no cover
        # should not happen
        raise VariableUnbound()

class __extend__(W_Call):
    def evaluate(self):
        args = [argument.evaluate() for argument in self.get_arguments()]
        return self.callee.evaluate().call(args)

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        lamb = self.callee
        jit.promote(lamb)
        assert isinstance(lamb, W_Lambda)
        ex_stack = ExecutionStackElement(lamb._cursor, ex_stack)
        return (op_stack, ex_stack)

class __extend__(W_NAryCall):
    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        # super
        (op_stack, ex_stack) = W_Call.interpret(self, op_stack, ex_stack)
        for index in range(self.get_number_of_arguments()):
            arg = self.get_argument(index)
            ex_stack = ExecutionStackElement(arg, ex_stack)
        return (op_stack, ex_stack)

#
# XXX:
# Attention: interpret for W_Call1..10 is defined inline
#            because of generated classes.
#
#class __extend__(W_Call1): pass
#

class __extend__(W_Cursor):
    def evaluate(self):
        raise NotImplementedError("only meaningfull in non-recursive implementation")

class __extend__(W_ConstructorCursor):
    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        children = []
        for i in range(self._tag.arity()):
            children.append(op_stack._data)
            op_stack = op_stack._next
        new_top = w_constructor(self._tag, children)
        op_stack = OperandStackElement(new_top, op_stack)
        return (op_stack, ex_stack)

class __extend__(W_LambdaCursor):
    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        return self._lamb.interpret_lambda(op_stack, ex_stack)



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

def current_shapes(depth, op_stack):
    shapes = _stack_to_list(op_stack, depth)
    tup = find_shape_tuple(shapes)
    return tup




###############################################################################
#
#
#
#  Support for the JIT.
#
#

def get_printable_location_t(current_cursor, current_args_shapes):
    return get_printable_location_d(None, False,
                                    current_cursor, current_args_shapes)

def get_printable_location_d(dc, d, current_cursor, current_args_shapes):
    res = ""
    if current_cursor is None:
        res += "<None>"
    else:
        if isinstance(current_cursor, W_LambdaCursor):
            res += "Lamb[%s/%s] " % (current_cursor._lamb._name, current_cursor._lamb.arity())
        elif isinstance(current_cursor, W_ConstructorCursor):
            res +=  "Cons[%s/%s] " % (current_cursor._tag.name, current_cursor._tag.arity())
        else:
            return "<Unknown>"
        res += current_args_shapes.merge_point_string()
    return res

jitdriver_d = jit.JitDriver(
    greens=["debug_callback", "debug",
            "current_cursor", "current_args_shapes"],
    reds=["op_stack", "ex_stack", "expr"],
    get_printable_location=get_printable_location_d,
)

jitdriver_t = jit.JitDriver(
    greens=["current_cursor", "current_args_shapes"],
    reds=["op_stack", "ex_stack", "expr"],
    get_printable_location=get_printable_location_t,
)

jitdriver = jitdriver_d

def interpret(expression_stack, arguments_stack=None,
              debug=False, debug_callback=None):

    op_stack = arguments_stack
    ex_stack = expression_stack

    # jit greens
    expr = None
    current_cursor = None
    current_args_shapes = None

    if we_are_translated():
        jitdriver = jitdriver_t
        if debug: assert debug_callback is None
    else:
        jitdriver = jitdriver_d
        if debug_callback is None:
            from lamb.util.debug import debug_stack
            debug_callback = debug_stack

    while True:
        ex_data = ex_data_or_none(ex_stack)
        if isinstance(ex_data, W_Cursor):
            current_cursor = jit.promote(ex_data)
            if isinstance(current_cursor, W_LambdaCursor):
                current_args_shapes = current_shapes(
                    current_cursor._lamb.arity(), op_stack)
            elif isinstance(current_cursor, W_ConstructorCursor):
                current_args_shapes = current_shapes(
                    current_cursor._tag.arity(), op_stack)

            if we_are_translated():
                jitdriver.can_enter_jit( expr=expr, op_stack=op_stack, ex_stack=ex_stack, current_cursor=current_cursor, current_args_shapes=current_args_shapes)
            else:
                jitdriver.can_enter_jit( expr=expr, op_stack=op_stack, ex_stack=ex_stack, current_cursor=current_cursor, current_args_shapes=current_args_shapes, debug=debug, debug_callback=debug_callback)

        #here is the merge point
        if we_are_translated():
            jitdriver.jit_merge_point( expr=expr, op_stack=op_stack, ex_stack=ex_stack, current_cursor=current_cursor, current_args_shapes=current_args_shapes)
        else:
            jitdriver.jit_merge_point( expr=expr, op_stack=op_stack, ex_stack=ex_stack, current_cursor=current_cursor, current_args_shapes=current_args_shapes, debug=debug, debug_callback=debug_callback)

        if ex_stack is None:
            break


        if debug: debug_callback(Stack(ex_stack, op_stack))
        expr = ex_stack._data
        ex_stack = ex_stack._next
        (op_stack, ex_stack) = expr.interpret(op_stack, ex_stack)

    if debug: debug_callback(Stack(ex_stack, op_stack))
    return op_stack._data
