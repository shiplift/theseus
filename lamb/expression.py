#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import compute_identity_hash, r_dict

from lamb.util.repr import uni, who, urepr
from lamb.stack import ExecutionStackElement, OperandStackElement


from lamb.object import Object
from lamb.pattern import NoMatch
from lamb.model import W_Object, W_Lambda, w_constructor



class W_PureExpression(W_Object):
    """
    Objects that only ever live on the expression stack
    """
    pass

class W_ConstructorEvaluator(W_PureExpression):

    def __init__(self, tag, children=None):
        from lamb.model import W_Tag
        assert isinstance(tag, W_Tag)
        self._tag = tag
        self._children = children or []

    #
    # Expression behavior
    #
    def evaluate(self):
        return w_constructor(self._tag, [child.evaluate() for child in self._children])

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        ex_stack = ExecutionStackElement(self._tag._cursor, ex_stack)
        for child in self._children:
            ex_stack = ExecutionStackElement(child, ex_stack)
        return (op_stack, ex_stack)


    @jit.unroll_safe
    def copy(self, binding):
        return W_ConstructorEvaluator(self._tag, [child.copy(binding) for child in self._children])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"^" + urepr(self._tag, seen) + ( (u"(" + u", ".join(map(lambda x: urepr(x, seen), self._children)) + u")") if len(self._children) > 0 else "")


class W_VariableExpression(W_PureExpression):

    _immutable_fields_ = ['variable']

    def __init__(self, variable):
        self.variable = variable

    def resolve(self, binding):
        # var = jit.promote(self.variable)
        var = self.variable
        w_result = binding[var.binding_index]

        if w_result is None:
            raise VariableUnbound()
        else:
            return w_result

    def evaluate(self): # pragma: no cover
        # should not happen
        raise VariableUnbound()

    def interpret(self, op_stack, ex_stack): # pragma: no cover
        # should not happen
        raise VariableUnbound()

    def copy(self, binding):
        return self.resolve(binding)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"!" + urepr(self.variable, seen)

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

    #
    # Expression behavior
    #
    def evaluate(self):
        return self.callee.evaluate().call([argument.evaluate() for argument in self.get_arguments()])

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        lamb = self.callee
        jit.promote(lamb)
        assert isinstance(lamb, W_Lambda)
        ex_stack = ExecutionStackElement(lamb._cursor, ex_stack)
        return (op_stack, ex_stack)

    @jit.unroll_safe
    def copy(self, binding):
        return w_call(self.callee.copy(binding), [argument.copy(binding) for argument in self.get_arguments()])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        res = u"μ"
        if isinstance(self.callee, W_Lambda):
            res += unicode(self.callee._name)
        else:
            res += urepr(self.callee, seen)
        res += self.children_to_repr(seen)
        return res

    #
    # Testing and Debug
    #
    def children_to_repr(self, seen):
        if self.get_number_of_arguments() > 0:
            return u"(" + u", ".join(map(lambda x: urepr(x, seen), self.get_arguments())) + u")"
        else:
            return u""

class W_NAryCall(W_Call):

    _immutable_fields_ = ['arguments[*]']

    def _init_arguments(self, arguments):
        self.arguments = arguments

    def get_arguments(self):
        return self.arguments

    def get_argument(self, index):
        try:
            return self.arguments[index]
        except IndexError as e:
            raise e

    def get_number_of_arguments(self):
        return len(self.arguments)

    #
    # Expression behavior
    #
    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        # super
        (op_stack, ex_stack) = W_Call.interpret(self, op_stack, ex_stack)
        for index in range(self.get_number_of_arguments()):
            arg = self.get_argument(index)
            ex_stack = ExecutionStackElement(arg, ex_stack)
        return (op_stack, ex_stack)



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

        #
        # Expression behavior
        #
        def interpret(self, op_stack, ex_stack):
            # super
            (op_stack, ex_stack) = W_Call.interpret(self, op_stack, ex_stack)
            for x in arguments_iter:
                argument = getattr(self, ARG_ATTR_TEMPLATE % x)
                ex_stack = ExecutionStackElement(argument, ex_stack)
            return (op_stack, ex_stack)

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

class W_Cursor(W_PureExpression):
    """
    Cursors are no actual expressions but act as such on the expression stack.
    """
    def evaluate(self):
        raise NotImplementedError("only meaningfull in non-recursive implementation")

class W_ConstructorCursor(W_Cursor):

    _immutable_fields_ = ['_tag']

    def __init__(self, tag):
        self._tag = tag

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        children = []
        for i in range(self._tag.arity):
            children.append(op_stack._data)
            op_stack = op_stack._next
        new_top = w_constructor(self._tag, children)
        op_stack = OperandStackElement(new_top, op_stack)
        return (op_stack, ex_stack)


    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._tag, seen)

class W_LambdaCursor(W_Cursor):

    _immutable_fields_ = ['_lamb']

    def __init__(self, lamb):
        self._lamb = lamb

    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        return self._lamb.interpret_lambda(op_stack, ex_stack)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._lamb, seen)

    #
    # to avoid recursion in _lamb._cursor
    # only ever used by the type annotator
    #
    def __eq__(self, other): #pragma: no cover
        return self.__class__ == other.__class__ and  self._lamb is other._lamb


class Rule(Object):

    _immutable_fields_ = ['_patterns[*]', 'arity', '_expression', 'maximal_number_of_variables']

    def __init__(self, patterns, expression):
        self._patterns = patterns
        self.arity = len(patterns)
        self._expression = expression
        self.maximal_number_of_variables = 0
        for pattern in self._patterns:
            pattern.update_number_of_variables(self)

    @jit.unroll_safe
    def match_all(self, w_arguments, binding):
        if self.arity != 0:
            for i in range(self.arity):
                self._patterns[i].match(w_arguments[i], binding)
        return self._expression

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        res = u""
        pats_seen = set(seen)
        res += u"{%s}" % (u", ".join(map(lambda x: urepr(x, pats_seen), self._patterns)))
        res += u" ↦ "
        exp_seen = set(seen)
        res += urepr(self._expression, exp_seen)
        return res


class Variable(Object):

    _immutable_fields_ = ['name', 'binding_index']

    def __init__(self, name):
        self.name = name
        self.binding_index = -1

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return self.name + u"_" + who(self)  + ("@%s" % self.binding_index if self.binding_index != -1 else "")



class VariableUnbound(Exception):
    pass

