#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.debug import debug_start, debug_stop, debug_print

from theseus.pattern import NoMatch
from theseus.object import Object
from theseus.model import (W_Object, W_Constructor, W_Lambda, W_Primitive,
                        w_constructor)
from theseus.shape import (default_shape, find_shape_tuple,
                        CompoundShape, InStorageShape)
from theseus.expression import (W_ConstructorEvaluator, W_VariableExpression,
                             W_Call, W_NAryCall, Quote,
                             VariableUnbound, LambdaBox, Rule)
from theseus.small_list import inline_small_list

#
# Execution behavior.
#
class __extend__(W_Object):
    def evaluate_with_binding(self, binding_list):
        # only used from tests
        assert isinstance(binding_list, list)
        expr = self._replace_with_constructor_expression()
        bindings = Env.make(binding_list)
        cont = FinishContinuation()
        try:
            while True:
                expr, bindings, cont = expr.interpret(bindings, cont)
        except Done, e:
            return e.w_val

class __extend__(Quote):

    def interpret(self, bindings, cont):
        return cont.plug_reduce(self.w_value)

class __extend__(W_Constructor):

    def interpret(self, bindings, cont):
        assert 0, "should be unreachable"

class __extend__(W_Lambda):

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

    def call_cont(self, args_w, cont):
        assert len(args_w) == self.arity()
        w_res = self._fun(args_w)
        return cont.plug_reduce(w_res)

class __extend__(W_ConstructorEvaluator):

    def interpret(self, bindings, cont):
        if len(self._children) == 0:
            return cont.plug_reduce(w_constructor(self._tag, []))
        return self._children[0], bindings, constrcont([], self, bindings, cont)

class __extend__(W_VariableExpression):

    def interpret(self, binding, cont):
        return cont.plug_reduce(self.resolve(binding))


class __extend__(W_Call):

    @jit.unroll_safe
    def interpret(self, bindings, cont):
        return self.callee, bindings, CallContinuation.make([], self, bindings, cont)

#
#
#
class Toplevel(Object):
    NoneFound = W_Object()

    def __init__(self):
        self.bindings = {}
    def set_bindings(self, bindings):
        self.bindings = bindings

    @jit.elidable
    def get(self, name):
        return self.bindings.get(name, self.NoneFound)
toplevel_bindings = Toplevel()


##################################################################################
@inline_small_list()
class Env(Object):
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


class Continuation(Object):
    def plug_reduce(self, w_val):
        raise NotImplementedError("abstract base class")

    def needs_bindings(self):
        return True

class FinishContinuation(Continuation):
    def plug_reduce(self, w_val):
        raise Done(w_val)

    def needs_bindings(self):
        return False

@inline_small_list()
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

def get_printable_location_constr(expr, shape):
    res = "C"
    if expr is None:
        res += "<None>"
    else:
        # if isinstance(expr, W_LambdaCursor):
        #     res += "Lamb[%s/%s] " % (current_cursor._lamb._name, current_cursor._lamb.arity())
        # elif isinstance(current_cursor, W_ConstructorCursor):
        #     res +=  "Cons[%s/%s] " % (current_cursor._tag.name, current_cursor._tag.arity())
        # else:
        #     return "<Unknown>"
        res += "<%s>" % expr.merge_point_string()
        res += shape.merge_point_string()
    return res

constrdriver = jit.JitDriver(
    greens=["expr", "shape"],
    reds=["self", "w_val"],
    get_printable_location=get_printable_location_constr,
    should_unroll_one_iteration=lambda expr, shape: True,
    is_recursive=True,
)

def constrcont(values_w, w_expr, bindings, cont):
    if len(values_w) + 1 == len(w_expr._children):
        return ConstrContinuation.make(values_w, w_expr, cont)
    return ConstrEvalArgsContinuation.make(values_w, w_expr, bindings, cont)

@inline_small_list()
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

@inline_small_list()
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
            # print "!", self.w_expr, self.cont
            w_constr = w_constructor(self.w_expr._tag, values_w)
            self = self.cont
            if not isinstance(self, ConstrContinuation):
                return self.plug_reduce(w_constr)
            w_val = w_constr
            constrdriver.jit_merge_point(expr=self.w_expr, shape=w_val._shape, self=self, w_val=w_val)

class Done(Exception):
    def __init__(self, w_val):
        self.w_val = w_val


def get_printable_location(expr, env_shapes):
    res = "E"
    if expr is None:
        res += "<None>"
    else:
        # if isinstance(expr, W_LambdaCursor):
        #     res += "Lamb[%s/%s] " % (current_cursor._lamb._name, current_cursor._lamb.arity())
        # elif isinstance(current_cursor, W_ConstructorCursor):
        #     res +=  "Cons[%s/%s] " % (current_cursor._tag.name, current_cursor._tag.arity())
        # else:
        #     return "<Unknown>"
        res += "<%s>" % expr.merge_point_string()
        res += env_shapes.merge_point_string()
    return res

jitdriver = jit.JitDriver(
    greens=["expr", "env_shapes"],
    reds=["bindings", "cont"],
    get_printable_location=get_printable_location,
    is_recursive=True,
)

def interpret(expr, bindings=None, cont=None):
    from theseus.expression import W_PureExpression
    # if isinstance(expr, ExecutionStackElement): # XXX for now
    #     assert expr._next is None
    #     expr = expr._data._replace_with_constructor_expression()
    if cont is None:
        cont = FinishContinuation()
    if bindings is None:
        bindings = Env.make([])
    assert isinstance(bindings, Env)
    try:
        while True:
            env_shapes = bindings.shape_tuple()
            if expr.should_enter_here:
                jitdriver.can_enter_jit(expr=expr, bindings=bindings, cont=cont, env_shapes=env_shapes)
            jitdriver.jit_merge_point(expr=expr, bindings=bindings, cont=cont, env_shapes=env_shapes)
            # print expr, "\n\t", bindings, "\n\t", cont
            expr2, bindings2, cont2 = expr.interpret(bindings, cont)
            assert not isinstance(expr2, W_Constructor)
            expr, bindings, cont = expr2, bindings2, cont2
            env_shapes = bindings.shape_tuple()
            assert isinstance(expr, W_PureExpression)
    except Done, e:
        return e.w_val

def interpret_expression(expr, bindings=None, cont=None):
    return interpret(expr._replace_with_constructor_expression(),
                     bindings, cont)
