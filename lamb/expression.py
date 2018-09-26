#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable

from rpython.rlib.debug import debug_start, debug_stop, debug_print

from lamb.object import Object
from lamb.pattern import NoMatch, Pattern
from lamb.model import W_Object, W_Tag, W_Lambda, W_Constructor, w_constructor

#
# Resolved copy behavior
#
class __extend__(W_Object):
    def copy(self, binding):
        return self

class __extend__(W_Constructor):
    @jit.unroll_safe
    def copy(self, binding):
        num_children = self.get_number_of_children()
        children = [None] * num_children
        for index in range(num_children):
            children[index] = self.get_child(index).copy(binding)
        return W_ConstructorEvaluator(self.get_tag(), children)

    def _replace_with_constructor_expression(self):
        children = [self.get_child(i)._replace_with_constructor_expression()
                        for i in range(self.get_number_of_children())]
        for child in children:
            if not isinstance(child, Quote):
                return W_ConstructorEvaluator(self.get_tag(), children)
        return Quote(self)

###############################################################################

class W_PureExpression(W_Object):
    """
    Objects that only ever live during execution
    """
    should_enter_here = False
    _immutable_fields_ = ["should_enter_here"]

    def _replace_with_constructor_expression(self):
        return self

class Quote(W_PureExpression):
    _immutable_fields_ = ["w_value"]
    def __init__(self, w_value):
        self.w_value = w_value

    def merge_point_string(self):
        if self.w_value:
            return "'%s" % self.w_value.merge_point_string()
        else:
            return "?"

class W_ConstructorEvaluator(W_PureExpression):

    _immutable_fields_ = ['_tag', '_children[*]']

    def __init__(self, tag, children=None):
        from lamb.model import W_Tag
        assert isinstance(tag, W_Tag)
        self._tag = tag
        self._children = children or []

    @jit.unroll_safe
    def copy(self, binding):
        return W_ConstructorEvaluator(self._tag, [child.copy(binding) \
                                                  for child in self._children])

    def _replace_with_constructor_expression(self):
        children = [child._replace_with_constructor_expression()
                        for child in self._children]
        return W_ConstructorEvaluator(self._tag, children)

    def merge_point_string(self):
        return "C%s/%d" % (self._tag.name, self._tag.arity())

class W_VariableExpression(W_PureExpression):

    _immutable_fields_ = ['variable']

    def __init__(self, variable):
        self.variable = variable

    def resolve(self, binding):
        from lamb.execution import toplevel_bindings
        # var = jit.promote(self.variable)
        var = self.variable.value()
        if not isinstance(var, Variable):
            return var
        w_result = binding._get_list(var.binding_index)

        if w_result is None:
            w_result = toplevel_bindings.get(var.name)
            if w_result is toplevel_bindings.NoneFound:
                raise VariableUnbound()
        return w_result

    def copy(self, binding):
        return self.resolve(binding)

    def merge_point_string(self):
        return "V[%s@%d]" % (self.variable.name, self.variable.binding_index)

class W_Call(W_PureExpression):

    _immutable_fields_ = ['callee']

    def __init__(self, callee):
        self.callee = callee

    def _init_arguments(self, arguments):
        pass

    def get_arguments(self):
        return []

    def get_argument(self, index):
        raise IndexError()

    def get_number_of_arguments(self):
        return 0


    @jit.unroll_safe
    def copy(self, binding):
        argnum = self.get_number_of_arguments()
        args = [None] * argnum
        for i in range(argnum):
            argument = self.get_argument(i)
            args[i] = argument.copy(binding)
        return w_call(self.callee.copy(binding), args)

    def _replace_with_constructor_expression(self):
        children = [self.get_argument(i)._replace_with_constructor_expression()
                        for i in range(self.get_number_of_arguments())]
        return w_call(self.callee._replace_with_constructor_expression(),
                children)

    def merge_point_string(self):
        return "%s()" % (self.callee.merge_point_string())

class W_NAryCall(W_Call):

    _immutable_fields_ = ['arguments[*]']

    def _init_arguments(self, arguments):
        self.arguments = arguments

    def get_arguments(self):
        return self.arguments

    def get_argument(self, index):
        # try:
            return self.arguments[index]
        # except IndexError as e:
        #     raise e

    def get_number_of_arguments(self):
        return len(self.arguments)

ARG_ATTR_TEMPLATE = "arg_%d"

def call_class_name(n_arguments):
    return 'W_Call%d' % n_arguments

def generate_call_class(n_arguments):

    arguments_iter = unrolling_iterable(range(n_arguments))

    class call_class(W_Call):
        _immutable_fields_ = [(ARG_ATTR_TEMPLATE % x) for x in arguments_iter]

        def _init_arguments(self, arguments):
            for x in arguments_iter:
                setattr(self, ARG_ATTR_TEMPLATE % x, arguments[x])

        def get_arguments(self):
            result = [None] * n_arguments
            for x in arguments_iter:
                result[x] = getattr(self, ARG_ATTR_TEMPLATE % x)
            return result

        def get_argument(self, index):
            for x in arguments_iter:
                if x == index:
                    return getattr(self, ARG_ATTR_TEMPLATE % x)
            raise IndexError

        def get_number_of_arguments(self):
            return n_arguments

    call_class.__name__ = call_class_name(n_arguments)
    return call_class

call_classes = [W_Call]
for n_arguments in range(1, 10):
    call_classes.append(generate_call_class(n_arguments))

call_class_iter = unrolling_iterable(enumerate(call_classes))

def w_call(callee, arguments):
    length = len(arguments)
    for i, cls in call_class_iter:
        if i == length:
            constr = cls(callee)
            constr._init_arguments(arguments)
            return constr
    # otherwise:
    constr = W_NAryCall(callee)
    constr._init_arguments(arguments)
    return constr



class Rule(Object):

    _immutable_fields_ = ['_patterns[*]', '_arity',
                          '_expression', 'maximal_number_of_variables']

    def __init__(self, patterns, expression):
        for p in patterns:
            assert isinstance(p, Pattern)
        self._patterns = patterns
        self._arity = len(patterns)
        self._expression = expr = expression._replace_with_constructor_expression()
        assert isinstance(expr, W_PureExpression)
        expr.should_enter_here = True

        self.maximal_number_of_variables = 0
        for pattern in self._patterns:
            pattern.update_number_of_variables(self)

    def arity(self):
        return self._arity

    def match_all(self, w_arguments, binding):
        if self._arity != 0:
            self.match_all_n(w_arguments, binding, self._arity)
        return self._expression

    @jit.unroll_safe
    def match_all_n(self, w_arguments, binding, arity):
        for i in range(arity):
            self._patterns[i].match(w_arguments[i], binding)


class Variable(Object):

    _immutable_fields_ = ['name', 'binding_index']

    def __init__(self, name):
        self.name = name
        self.binding_index = -1

    def value(self):
        return self

class LambdaBox(Variable):

    _immutable_fields_ = ['info', 'lam']
    # lam is "effectively" immutable

    def __init__(self, info, name, lam=None):
        Variable.__init__(self, name)
        self.info = info
        self.lam = lam

class __extend__(LambdaBox):
    def update(self, other):
        assert isinstance(other, LambdaBox)
        self.name = other.name
        self.info = other.info
        self.lam = other.lam

    def value(self):
        if self.lam:
            return self.lam
        else:
            reason = "Unfilled lambda %s" % self.name
            self.info.error(reason)

    def _replace_with_constructor_expression(self):
        v = self.value()
        return v._replace_with_constructor_expression()

class VariableUnbound(Exception):
    pass
