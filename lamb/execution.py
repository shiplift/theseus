#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit

from lamb.util.repr import uni, who, urepr
from lamb.util.debug import debug_stack
from lamb.util.testing import HelperMixin
from lamb.stack import ExecutionStackElement, OperandStackElement

class W_Object(HelperMixin):
    pass

class W_Symbol(W_Object):
    symbols = {}
    
    def __init__(self, name):
        self.name = name


    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return self.name

def symbol(name):
    assert isinstance(name, str)
    w_symbol = W_Symbol.symbols.get(name, None)
    if w_symbol is None:
        w_symbol = W_Symbol(name)
        W_Symbol.symbols[name] = w_symbol
    
    assert isinstance(w_symbol, W_Symbol)
    return w_symbol

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

    def __init__(self, tag, children=None):
        assert isinstance(tag, W_Symbol)
        self._tag = tag
        self._children = children or []

    def get_tag(self):
        return self._tag
        
    def get_child(self, index):
        return self._children[index]

    def get_number_of_children(self):
        return len(self._children)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"#" + urepr(self._tag, seen) + ( ("(" + urepr(self._children, seen)[1:][:-1] + u")") if len(self._children) > 0 else "")

class W_Lambda(W_Object):
    """
    λ arity is the number of patterns in the first rule, or zero
    """

    _immutable_fields_ = ['_rules[*]', '_cursor']
    
    def __init__(self, rules):
        self._rules = rules
        self._cursor = LambdaCursor(self)
        
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
        return u"λ" + who(self) + u"(" + u"; ".join(map(lambda x: urepr(x, seen), self._rules)) + u")"

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
            tag = jit.promote(obj.get_tag())
            if (tag == self._tag) and (obj.get_number_of_children() == len(self._children)):
                for i in range(len(self._children)):
                    self._children[i].match(obj.get_child(i), binding)
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

class Expression(HelperMixin):


    _attrs_ = []

    def evaluate_with_binding(self, binding):
        return self.copy(binding).evaluate()

    def evaluate(self):
        raise NotImplementedError("abstract method")

    def interpret(self, binding, stack, exp_stack):
        raise NotImplementedError("abstract method")

    def copy(self, binding):
        return self

        
class ValueExpression(Expression):

    _immutable_fields_ = ['value']

    def __init__(self, value):
        self.value = value

    def evaluate(self):
        return self.value

    def interpret(self, binding, stack, exp_stack):
        return (OperandStackElement(self.value, stack), exp_stack)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"!(" + urepr(self.value, seen) + u")"

class VariableExpression(Expression):

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
        return ValueExpression(self.resolve(binding))

    
    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"!" + urepr(self.variable, seen)

class ConstructorExpression(Expression):

    _immutable_fields_ = ['_tag', '_children[*]', '_cursor']

    def __init__(self, tag, children=None, cursor=None):
        self._tag = tag
        self._children = children or []
        self._cursor = cursor or ConstructorCursor(self._tag, len(self._children))
        
    def evaluate(self):
        return W_Constructor(self._tag, [child.evaluate() for child in self._children])

    @jit.unroll_safe
    def interpret(self, binding, stack, exp_stack):
        exp_stack = ExecutionStackElement(self._cursor, exp_stack)
        for child in self._children:
            exp_stack = ExecutionStackElement(child, exp_stack)
        return (stack, exp_stack)

    @jit.unroll_safe
    def copy(self, binding):
        return ConstructorExpression(self._tag, [child.copy(binding) for child in self._children], self._cursor)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"!" + urepr(self._tag,seen) + ( (u"(" + urepr(self._children, seen)[1:][:-1] + u")") if len(self._children) > 0 else "" )

class CallExpression(Expression):

    _immutable_fields_ = ['callee', 'arguments[*]']

    def __init__(self, callee, arguments=None):
        self.callee = callee
        self.arguments = arguments or []

    def evaluate(self):
        return self.callee.evaluate().call([arg.evaluate() for arg in self.arguments])

    @jit.unroll_safe
    def interpret(self, binding, stack, exp_stack):
        callee = self.callee
        assert isinstance(callee, ValueExpression)
        lamb = callee.value
        assert isinstance(lamb, W_Lambda)
        exp_stack = ExecutionStackElement(lamb._cursor, exp_stack)
        for arg in self.arguments:
            exp_stack = ExecutionStackElement(arg, exp_stack)
        return (stack, exp_stack)

    @jit.unroll_safe
    def copy(self, binding):
        return CallExpression(self.callee.copy(binding), [arg.copy(binding) for arg in self.arguments])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"μ" + urepr(self.callee, seen) + u"(" + urepr(self.arguments, seen) + u")"

class Cursor(Expression):
    """
    Cursors are no actual expressions but act as such on the expression stack.
    """
    def evaluate(self):
        raise NotImplementedError("only meaningfull in non-recursive implementation")

class ConstructorCursor(Cursor):

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
        stack = OperandStackElement(W_Constructor(self._tag, children), stack)
        return (stack, exp_stack)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._tag, seen) + u"(" + urepr(self._number_of_children, seen) + u")"

class LambdaCursor(Cursor):

    _immutable_fields_ = ['_lamb']
    
    def __init__(self, lamb):
        self._lamb = lamb

    def interpret(self, binding, stack, exp_stack):
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

class VariableUnbound(Exception):
    pass

class NoMatch(Exception):
    pass

jitdriver = jit.JitDriver(
    greens=["current_lambda"],
    reds=["w_stack", "e_stack", "expr"],
    #    get_printable_location=get_printable_location,
)

def interpret(expression_stack, arguments_stack=None, debug=False, debug_callback=None):

    w_stack = arguments_stack
    e_stack = expression_stack
    current_lambda = None
    expr = None
    
    if debug_callback is None: debug_callback = debug_stack

    while True:
        n = e_stack._data if e_stack is not None else None
        if isinstance(n, LambdaCursor):
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
