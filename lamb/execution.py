#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable

from lamb.util.repr import uni, who, urepr
from lamb.util.debug import debug_stack
from lamb.util.testing import HelperMixin
from lamb.stack import ExecutionStackElement, OperandStackElement

class W_Object(HelperMixin):

    #
    # Expression behavior
    #
    def evaluate_with_binding(self, binding):
        return self.copy(binding).evaluate()

    def evaluate(self):
        return self

    def interpret(self, binding, stack, exp_stack):
        return (OperandStackElement(self, stack), exp_stack)

    def copy(self, binding):
        return self


class W_Tag(W_Object):
    tags = {}

    _immutable_fields_ = ['name', 'arity', '_cursor']
    
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity
        self._cursor = W_ConstructorCursor(self, self.arity)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"%s/%d" % (self.name, self.arity)

    #
    # Tags compare by identity
    #
    def __eq__(self, other): #pragma: no cover
        return self is other


def tag(name, arity):
    assert isinstance(name, str)
    assert isinstance(arity, int)
    w_tag = W_Tag.tags.get( (name, arity) , None)
    if w_tag is None:
        w_tag = W_Tag(name, arity)
        W_Tag.tags[ (name, arity) ] = w_tag
    
    assert isinstance(w_tag, W_Tag)
    return w_tag

class W_Integer(W_Object):

    def __init__(self, value):
        self._value = value

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"#%d" % self._value

class W_Constructor(W_Object):

    _immutable_fields_ = ['_tag']

    def __init__(self, tag):
        assert isinstance(tag, W_Tag)
        self._tag = tag

    def _init_children(self, children):
        pass

    def get_tag(self):
        return self._tag

    def get_children(self):
        return []  
    
    def get_child(self, index):
        raise IndexError()

    def get_number_of_children(self):
        return 0

    #
    # Expression behavior
    #
    @jit.unroll_safe
    def copy(self, binding):
        children = [self.get_child(index).copy(binding) for index in range(self.get_number_of_children())]
        return W_ConstructorEvaluator(self._tag, children)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"#" + urepr(self._tag, seen) + self.children_to_repr(seen)

    def children_to_repr(self, seen):
        return u""


class W_NAryConstructor(W_Constructor):

    _immutable_fields_ = ['_children[*]']

    def _init_children(self, children):
        self._children = children or []

    def get_children(self):
        return self._children

    def get_child(self, index):
        try:
            return self._children[index]
        except IndexError as e:
            raise e

    def get_number_of_children(self):
        return len(self._children)

    #
    # Expression behavior
    #
    def evaluate(self):
        return type(self)(self._tag, [child.evaluate() for child in self._children])

    #
    # Testing and Debug
    #
    def children_to_repr(self, seen):
        if len(self._children) > 0:
            return u"(" + urepr(self._children, seen)[1:][:-1] + u")"
        else:
            return u""

CHILD_ATTR_TEMPLATE = "child_%d"

def constructor_class_name(n_children):
    return 'W_Constructor%d' % n_children


def generate_constructor_class(n_children):

    children_iter = unrolling_iterable(range(n_children))

    class constructor_class(W_Constructor):
        _immutable_fields_ = [(CHILD_ATTR_TEMPLATE % x) for x in children_iter]

        def _init_children(self, children):
            for x in children_iter:
                setattr(self, CHILD_ATTR_TEMPLATE % x, children[x])

        def get_children(self):
            result = [None] * n_children
            for x in children_iter:
                result[x] = getattr(self, CHILD_ATTR_TEMPLATE % x)
            return result
        
        def get_child(self, index):
            for x in children_iter:
                if x == index:
                    return getattr(self, CHILD_ATTR_TEMPLATE % x)
            raise IndexError
        
        def get_number_of_children(self):
            return n_children
        
        #
        # Expression behavior
        #
        def evaluate(self):
            return w_constructor(self._tag, [child.evaluate() for child in self.get_children()])
        
        #
        # Testing and Debug
        #
        @uni
        def children_to_repr(self, seen):
            result = u""
            for x in children_iter:
                result += urepr(getattr(self, CHILD_ATTR_TEMPLATE % x), seen)
                result += u", "
            return result

    constructor_class.__name__ = constructor_class_name(n_children)
    return constructor_class

constructor_classes = [W_Constructor]
for n_children in range(1, 10):
    constructor_classes.append(generate_constructor_class(n_children))

class_iter = unrolling_iterable(enumerate(constructor_classes))

def w_constructor(tag, children):
    length = len(children)
    for i, cls in class_iter:
        if i == length:
            constr = cls(tag)
            constr._init_children(children)
            return constr
    # otherwise:
    constr = W_NAryConstructor(tag)
    constr._init_children(children)
    return constr

class W_Lambda(W_Object):
    """
    λ arity is the number of patterns in the first rule, or zero
    """

    _immutable_fields_ = ['_rules[*]', '_cursor']
    
    def __init__(self, rules, name=""):
        self._rules = rules
        self._name = name
        self._cursor = W_LambdaCursor(self)
        
    def arity(self):
        assert len(self._rules) > 0
        return self._rules[0].arity()

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
    def interpret_lamdba(self, stack, exp_stack):
        jit.promote(self)
        w_arguments = []
        for i in range(self.arity()):
            w_arguments.append(stack._data)
            stack = stack._next
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(w_arguments, binding)
            except NoMatch:
                pass
            else:
                exp_stack = ExecutionStackElement(expression.copy(binding), exp_stack)
                return (stack, exp_stack)

        raise NoMatch()
        
    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"λ" + (self._name if len(self._name) > 0 else who(self)) + u"(" + u"; ".join(map(lambda x: urepr(x, seen), self._rules)) + u")"

class W_PureExpression(W_Object):
    """
    Objects that only ever live on the expresion stack
    """
    pass

class W_ConstructorEvaluator(W_PureExpression):

    def __init__(self, tag, children=None):
        assert isinstance(tag, W_Tag)
        self._tag = tag
        self._children = children or []


    #
    # Expression behavior
    #
    def evaluate(self):
        return w_constructor(self._tag, [child.evaluate() for child in self._children])

    @jit.unroll_safe
    def interpret(self, binding, stack, exp_stack):
        exp_stack = ExecutionStackElement(self._tag._cursor, exp_stack)
        for child in self._children:
            exp_stack = ExecutionStackElement(child, exp_stack)
        return (stack, exp_stack)


    @jit.unroll_safe
    def copy(self, binding):
        return W_ConstructorEvaluator(self._tag, [child.copy(binding) for child in self._children])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"^" + urepr(self._tag, seen) + ( ("(" + urepr(self._children, seen)[1:][:-1] + u")") if len(self._children) > 0 else "")


class W_VariableExpression(W_PureExpression):

    _immutable_fields_ = ['variable']
    
    def __init__(self, variable):
        self.variable = variable

    def resolve(self, binding):
        try:
            w_result = binding[self.variable.binding_index]
        except KeyError: # pragma: no cover
            # should not happen
            raise VariableUnbound()
        
        if w_result is None:
            raise VariableUnbound()
        else:            
            return w_result
    
    def evaluate(self): # pragma: no cover
        # should not happen
        raise VariableUnbound()

    def interpret(self, binding, stack, exp_stack): # pragma: no cover
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
    def interpret(self, binding, stack, exp_stack):
        lamb = self.callee
        jit.promote(lamb)
        assert isinstance(lamb, W_Lambda)        
        exp_stack = ExecutionStackElement(lamb._cursor, exp_stack)
        return (stack, exp_stack)

    @jit.unroll_safe
    def copy(self, binding):
        return w_call(self.callee.copy(binding), [argument.copy(binding) for argument in self.get_arguments()])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"μ" + urepr(self.callee, seen) + self.children_to_repr(seen)

    def children_to_repr(self, seen):
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
    def interpret(self, binding, stack, exp_stack):
        # super
        (stack, exp_stack) = W_Call.interpret(self, binding, stack, exp_stack)
        for index in range(self.get_number_of_arguments()):
            arg = self.get_argument(index)
            exp_stack = ExecutionStackElement(arg, exp_stack)
        return (stack, exp_stack)

    #
    # Testing and Debug
    #
    def children_to_repr(self, seen):
        if len(self._children) > 0:
            return u"(" + urepr(self._children, seen)[1:][:-1] + u")"
        else:
            return u""



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
        def interpret(self, binding, stack, exp_stack):
            # super
            (stack, exp_stack) = W_Call.interpret(self, binding, stack, exp_stack)
            for x in arguments_iter:
                argument = getattr(self, ARG_ATTR_TEMPLATE % x)
                exp_stack = ExecutionStackElement(argument, exp_stack)
            return (stack, exp_stack)

        
        #
        # Testing and Debug
        #
        def children_to_repr(self, seen):
            result = u""
            for x in arg_iter:
                result += urepr(getattr(self, ARG_ATTR_TEMPLATE % x), seen)
                result += u", "
            return result

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

    _immutable_fields_ = ['_tag', '_number_of_children']
    
    def __init__(self, tag, number_of_children):
        self._tag = tag
        self._number_of_children = number_of_children

    @jit.unroll_safe
    def interpret(self, binding, stack, exp_stack):
        jit.promote(self)
        children = []
        for i in range(self._number_of_children):
            children.append(stack._data)
            stack = stack._next
        stack = OperandStackElement(w_constructor(self._tag, children), stack)
        return (stack, exp_stack)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._tag, seen) + u"(" + urepr(self._number_of_children, seen) + u")"

class W_LambdaCursor(W_Cursor):

    _immutable_fields_ = ['_lamb']
    
    def __init__(self, lamb):
        self._lamb = lamb

    def interpret(self, binding, stack, exp_stack):
        jit.promote(self)
        return self._lamb.interpret_lamdba(stack, exp_stack)

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
        return self._lamb is other._lamb



class Rule(HelperMixin):

    _immutable_fields_ = ['_patterns[*]', '_expression', 'maximal_number_of_variables']

    def __init__(self, patterns, expression):
        self._patterns = patterns
        self._expression = expression
        self.maximal_number_of_variables = 0
        for pattern in self._patterns:
            pattern.update_number_of_variables(self)

    def arity(self):
        return len(self._patterns)

    @jit.unroll_safe
    def match_all(self, w_arguments, binding):
        if self.arity() != 0:
            for i in range(self.arity()):
                self._patterns[i].match(w_arguments[i], binding)
        return self._expression            

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"{" + u", ".join(map(lambda x: urepr(x, seen), self._patterns)) + u" ↦ " + urepr(self._expression, seen) + u"}"


class Variable(HelperMixin):

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


class Pattern(HelperMixin):

    def match(self, an_obj, binding):
        raise NotImplementedError("abstract method")

    def update_number_of_variables(self, rule):
        pass

class IntegerPattern(Pattern):

    def __init__(self, value):
        self.value = value

    def match(self, obj, binding):
        if isinstance(obj, W_Integer): # pragma: no branch
            if obj._value == self.value:
                return
        raise NoMatch()

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"&" + unicode(repr(self.value))
    
class VariablePattern(Pattern):

    _immutable_fields_ = ['variable']

    def __init__(self, variable):
        self.variable = variable

    def match(self, obj, binding):
        assert self.variable.binding_index != -1 # bound
        assert binding[self.variable.binding_index] is None
        binding[self.variable.binding_index] = obj

    def update_number_of_variables(self, rule):
        assert self.variable.binding_index == -1 # unbound        
        self.variable.binding_index = rule.maximal_number_of_variables
        rule.maximal_number_of_variables += 1
    
    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self.variable, seen)


class ConstructorPattern(Pattern):

    _immutable_fields_ = ['_tag', '_children[*]']

    def __init__(self, tag, children=None):
        self._tag = tag
        self._children = children or []

    @jit.unroll_safe
    def match(self, obj, binding):
        if isinstance(obj, W_Constructor): # pragma: no branch
            # be sure to use the W_Constructor api
            tag = jit.promote(obj.get_tag())
            if (tag == self._tag) and (obj.get_number_of_children() == len(self._children)):
                for i in range(len(self._children)):
                    self._children[i].match(obj.get_child(i), binding)
                return
        if isinstance(obj, W_ConstructorEvaluator): # pragma: no branch
            # shortcut to the evaluator properties
            tag = jit.promote(obj._tag)
            if (tag == self._tag) and (len(obj._children) == len(self._children)):
                for i in range(len(self._children)):
                    self._children[i].match(obj._children[i], binding)
                return
        raise NoMatch()

    def update_number_of_variables(self, rule):
        for child in self._children:
            child.update_number_of_variables(rule)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self._tag, seen) + u"(" + u", ".join(map(lambda x: urepr(x, seen), self._children)) + u")"






class VariableUnbound(Exception):
    pass

class NoMatch(Exception):
    pass

def get_printable_location(current_lambda): #pragma: no cover
    if current_lambda is None:
        return "<None>"
    else:
        return "Lamb " + current_lambda._name

jitdriver = jit.JitDriver(
    greens=["current_lambda"],
    reds=["w_stack", "e_stack", "expr"],
    get_printable_location=get_printable_location,
)


    

def interpret(expression_stack, arguments_stack=None, debug=False, debug_callback=None):

    w_stack = arguments_stack
    e_stack = expression_stack
    current_lambda = None
    expr = None
    
    if debug_callback is None: debug_callback = debug_stack

    while True:
        n = e_stack._data if e_stack is not None else None
        if isinstance(n, W_LambdaCursor):
            current_lambda = n._lamb
            jitdriver.can_enter_jit(
                expr=expr, w_stack=w_stack, e_stack=e_stack,
                current_lambda=current_lambda,
            )
        jitdriver.jit_merge_point(
            expr=expr, w_stack=w_stack, e_stack=e_stack,
            current_lambda=current_lambda,
        )
        if e_stack is None:
            break


        if debug: debug_callback({'e_stack':e_stack, 'w_stack':w_stack})
        expr = e_stack._data
        e_stack = e_stack._next
        (w_stack, e_stack) = expr.interpret(None, w_stack, e_stack)

    if debug: debug_callback({'e_stack':e_stack, 'w_stack':w_stack})
    return w_stack._data
