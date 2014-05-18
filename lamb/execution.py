#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.debug import debug_start, debug_stop, debug_print

from lamb.stack import (Stack, ExecutionStackElement, OperandStackElement,
                        ex_push, op_push)

from lamb.pattern import NoMatch
from lamb.object import Object
from lamb.model import (W_Object, W_Constructor, W_Lambda, W_Primitive,
                        w_constructor)
from lamb.shape import (default_shape, find_shape_tuple,
                        CompoundShape, InStorageShape)
from lamb.expression import (W_LambdaCursor, W_ConstructorCursor, W_Cursor,
                             W_ConstructorEvaluator, W_VariableExpression,
                             W_Call, W_NAryCall, Quote,
                             VariableUnbound, Rule)
from lamb.small_list import inline_small_list

#
# Execution behavior.
#
class __extend__(W_Object):
    def evaluate_with_binding(self, binding_list):
        # only used from tests
        assert isinstance(binding_list, list)
        return self.evaluate(Env.make(binding_list))

    def evaluate(self, binding):
        return self

    def interpret(self, op_stack, ex_stack):
        return (op_push(op_stack, self), ex_stack)


class __extend__(Quote):
    def evaluate(self, binding):
        return self.w_value

    def interpret_new(self, bindings, cont):
        return cont.plug_reduce(self.w_value)

class __extend__(W_Constructor):
    def evaluate(self, binding):
        return w_constructor(self.get_tag(), [child.evaluate(binding) for child in self.get_children()])

    def interpret_new(self, bindings, cont):
        assert 0, "should be unreachable"

class __extend__(W_Lambda):
    def call(self, arguments_w):
        assert len(arguments_w) == self.arity()
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(arguments_w, binding)
            except NoMatch:
                pass
            else:
                return expression.evaluate(Env.make(binding))

        raise NoMatch()

    @jit.unroll_safe
    def interpret_lambda(self, op_stack, ex_stack):
        jit.promote(self)
        num_args = self.arity()
        w_arguments = [None] * num_args
        for i in range(num_args):
            w_arguments[i], op_stack = op_stack.pop()
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(w_arguments, binding)
            except NoMatch:
                pass
            else:
                resolved = expression.copy(binding)
                ex_stack = ex_push(ex_stack, resolved)
                return (op_stack, ex_stack)
        raise NoMatch()

    @jit.unroll_safe
    def select_rule(self, args_w):
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(args_w, binding)
            except NoMatch:
                pass
            else:
                return expression, Env.make(binding)
        raise NoMatch()

    def call_cont(self, args_w, cont):
        expr, bindings = self.select_rule(args_w)
        return expr, bindings, cont

class __extend__(W_Primitive):
    def call(self, w_arguments):
        assert len(w_arguments) == self.arity()
        return self._fun(w_arguments)

    @jit.unroll_safe
    def interpret_lambda(self, op_stack, ex_stack):
        jit.promote(self)
        num_args = self.arity()
        w_arguments = [None] * num_args
        for i in range(num_args):
            w_arguments[i], op_stack = op_stack.pop()
        ex_stack = ex_push(ex_stack, self._fun(w_arguments))
        return (op_stack, ex_stack)

    def call_cont(self, args_w, cont):
        w_res = self.call(args_w)
        return cont.plug_reduce(w_res)

class __extend__(W_ConstructorEvaluator):
    def evaluate(self, binding):
        return w_constructor(self._tag,
                             [child.evaluate(binding) for child in self._children])

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        ex_stack = ex_push(ex_stack, self._tag._cursor)
        for child in self._children:
            ex_stack = ex_stack.push(child)
        return (op_stack, ex_stack)

    def interpret_new(self, bindings, cont):
        if len(self._children) == 0:
            return cont.plug_reduce(w_constructor(self._tag, []))
        return self._children[0], bindings, constrcont([], self, bindings, cont)

class __extend__(W_VariableExpression):
    def evaluate(self, binding):
        return self.resolve(binding)

    def interpret(self, op_stack, ex_stack): # pragma: no cover
        # should not happen
        raise VariableUnbound()

    def interpret_new(self, binding, cont):
        return cont.plug_reduce(self.resolve(binding))


class __extend__(W_Call):
    def evaluate(self, binding):
        args = [argument.evaluate(binding) for argument in self.get_arguments()]
        return self.callee.evaluate(binding).call(args)

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        lamb = self.callee
        jit.promote(lamb)
        assert isinstance(lamb, W_Lambda)
        ex_stack = ex_push(ex_stack, lamb._cursor)
        return (op_stack, ex_stack)

    @jit.unroll_safe
    def interpret_new(self, bindings, cont):
        return self.callee, bindings, CallContinuation.make([], self, bindings, cont)



class __extend__(W_NAryCall):
    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        # super
        (op_stack, ex_stack) = W_Call.interpret(self, op_stack, ex_stack)
        for index in range(self.get_number_of_arguments()):
            arg = self.get_argument(index)
            ex_stack = ex_push(ex_stack, arg)
        return (op_stack, ex_stack)

#
# XXX:
# Attention: interpret for W_Call1..10 is defined inline
#            because of generated classes.
#
#class __extend__(W_Call1): pass
#

class __extend__(W_Cursor):
    def evaluate(self, binding):
        raise NotImplementedError("only meaningfull in non-recursive implementation")

class __extend__(W_ConstructorCursor):
    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        children = []
        for i in range(self._tag.arity()):
            child, op_stack = op_stack.pop()
            children.append(child)
        new_top = w_constructor(self._tag, children)
        op_stack = op_push(op_stack, new_top)
        return (op_stack, ex_stack)

class __extend__(W_LambdaCursor):
    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        return self._lamb.interpret_lambda(op_stack, ex_stack)

#
#
#
#
#
class Toplevel(Object):
    def __init__(self):
        self.bindings = {}
    def set_bindings(self, bindings):
        self.bindings = bindings
    @jit.elidable
    def get(self, name):
        return self.bindings.get(name, None)
toplevel_bindings = Toplevel()


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
        _, op_s = op_s.pop() if op_s is not None else (None, None)
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
def get_printable_location(current_cursor, current_args_shapes):
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

jitdriver = jit.JitDriver(
    greens=["current_cursor", "current_args_shapes"],
    reds=["op_stack", "ex_stack", "expr"],
    get_printable_location=get_printable_location,
)

_debug_callback = None
def old_interpret(expression_stack, arguments_stack=None, debug=False):

    op_stack = arguments_stack
    ex_stack = expression_stack

    # jit greens
    expr = None
    current_cursor = None
    current_args_shapes = None

    debug_callback = None
    if debug:
        assert _debug_callback is not None
        debug_callback = _debug_callback

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

            jitdriver.can_enter_jit( expr=expr, op_stack=op_stack, ex_stack=ex_stack, current_cursor=current_cursor, current_args_shapes=current_args_shapes)

        #here is the merge point
        jitdriver.jit_merge_point( expr=expr, op_stack=op_stack, ex_stack=ex_stack, current_cursor=current_cursor, current_args_shapes=current_args_shapes)

        if ex_stack is None:
            break


        if debug:
            assert debug_callback is not None
            debug_callback(Stack(ex_stack, op_stack))
        expr, ex_stack = ex_stack.pop()
        (op_stack, ex_stack) = expr.interpret(op_stack, ex_stack)

    if debug:
        assert debug_callback is not None
        debug_callback(Stack(ex_stack, op_stack))
    res, _ = op_stack.pop()
    return res

class Env(object):
    def __init__(self):
        pass

    @jit.unroll_safe
    def shape_tuple(self):
        shapes = [None] * self._get_size_list()
        for i in range(self._get_size_list()):
            w_obj = self._get_list(i)
            if isinstance(w_obj, W_Constructor):
                shapes[i] = w_obj._shape
        return find_shape_tuple(shapes)

inline_small_list(Env)

class Continuation(object):
    def plug_reduce(self, w_val):
        raise NotImplementedError("abstract base class")

    def needs_bindings(self):
        return True

class FinishContinuation(Continuation):
    def plug_reduce(self, w_val):
        raise Done(w_val)

    def needs_bindings(self):
        return False

class CallContinuation(Continuation):
    def __init__(self, w_expr, bindings, cont):
        assert isinstance(w_expr, W_Call)
        if self._get_size_list() == w_expr.get_number_of_arguments():
            bindings = None # won't need the old one
        self.w_expr = w_expr
        self.bindings = bindings
        self.cont = cont

    def plug_reduce(self, w_val):
        size = jit.promote(self._get_size_list())
        jit.promote(self.w_expr)
        values_w = self._get_full_list() + [w_val]
        if size == self.w_expr.get_number_of_arguments():
            w_lambda = values_w[0]
            jit.promote(w_lambda)
            assert isinstance(w_lambda, W_Lambda)
            args_w = values_w[1:]
            return w_lambda.call_cont(args_w, self.cont)
        bindings = self.bindings
        assert bindings is not None
        cont = CallContinuation.make(values_w, self.w_expr, bindings, self.cont)
        return self.w_expr.get_argument(size), bindings, cont
inline_small_list(CallContinuation)

constrdriver = jit.JitDriver(
    greens=["expr", "shape"],
    reds=["self", "w_val"],
    #get_printable_location=get_printable_location2,
    should_unroll_one_iteration=lambda expr, shape: True,
)

def constrcont(values_w, w_expr, bindings, cont):
    if len(values_w) + 1 == len(w_expr._children):
        return ConstrContinuation.make(values_w, w_expr, cont)
    return ConstrEvalArgsContinuation.make(values_w, w_expr, bindings, cont)

class ConstrEvalArgsContinuation(Continuation):
    def __init__(self, w_expr, bindings, cont):
        self.w_expr = w_expr
        self.bindings = bindings
        self.cont = cont

    def plug_reduce(self, w_val):
        jit.promote(self._get_size_list())
        jit.promote(self.w_expr)
        values_w = self._get_full_list() + [w_val]
        bindings = self.bindings
        cont = constrcont(values_w, self.w_expr, bindings, self.cont)
        return self.w_expr._children[len(values_w)], bindings, cont
inline_small_list(ConstrEvalArgsContinuation)

class ConstrContinuation(Continuation):

    def __init__(self, w_expr, cont):
        assert isinstance(w_expr, W_ConstructorEvaluator)
        self.w_expr = w_expr
        self.cont = cont

    def plug_reduce(self, w_val):
        while True:
            size = jit.promote(self._get_size_list())
            jit.promote(self.w_expr)
            values_w = self._get_full_list() + [w_val]
            assert len(values_w) == len(self.w_expr._children)
            w_constr = w_constructor(self.w_expr._tag, values_w)
            self = self.cont
            if not isinstance(self, ConstrContinuation):
                return self.plug_reduce(w_constr)
            w_val = w_constr
            constrdriver.jit_merge_point(expr=self.w_expr, shape=w_val._shape, self=self, w_val=w_val)

inline_small_list(ConstrContinuation)

class Done(Exception):
    def __init__(self, w_val):
        self.w_val = w_val


jitdriver2 = jit.JitDriver(
    greens=["expr", "env_shapes"],
    reds=["bindings", "cont"],
    #get_printable_location=get_printable_location2,
)

def interpret(expr, bindings=None, cont=None):
    from lamb.expression import W_PureExpression
    if isinstance(expr, ExecutionStackElement): # XXX for now
        assert expr._next is None
        expr = expr._data._replace_with_constructor_expression()
    if cont is None:
        cont = FinishContinuation()
    if bindings is None:
        bindings = Env.make([])
    assert isinstance(bindings, Env)
    try:
        while True:
            env_shapes = bindings.shape_tuple()
            if expr.should_enter_here:
                jitdriver2.can_enter_jit(expr=expr, bindings=bindings, cont=cont, env_shapes=env_shapes)
            jitdriver2.jit_merge_point(expr=expr, bindings=bindings, cont=cont, env_shapes=env_shapes)
            expr2, bindings2, cont2 = expr.interpret_new(bindings, cont)
            assert not isinstance(expr2, W_Constructor)
            expr, bindings, cont = expr2, bindings2, cont2
            env_shapes = bindings.shape_tuple()
            assert isinstance(expr, W_PureExpression)
    except Done, e:
        return e.w_val
