#!/usr/bin/python
# -*- coding: utf-8 -*-
#
# Hi.
#

from util import TestEqualityMixin, uni, who, urepr, debug_stack
from util import _dot, view


class W_Object(TestEqualityMixin):
    pass

class W_Symbol(W_Object):
    symbols = {}
    
    def __init__(self, name):
        self.name = name


    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return self.name
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


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
    def to_repr(self):
        return u"#" + unicode(self._value)
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

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
    def to_repr(self):
        return u"#" + urepr(self._tag) + ( ("(" + urepr(self._children)[1:][:-1] + u")") if len(self._children) > 0 else "") 
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class W_Lambda(W_Object):
    """
    λ arity is the number of patterns in the first rule, or zero
    """
    
    def __init__(self, rules):
        self._rules = rules

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

    def interpret_lamdba(self, stack, exp_stack):
        w_arguments = []
        for i in range(self.arity()):
            w_arguments.append(stack.pop())
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(w_arguments, binding)
            except NoMatch:
                pass
            else:
                exp_stack.append(expression.copy(binding))
                return

        raise NoMatch()
        
    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return u"λ" + who(self) + u"(" + u"; ".join(map(urepr, self._rules)) + u")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class Rule(TestEqualityMixin):

    def __init__(self, patterns, expression):
        self._patterns = patterns
        self._expression = expression
        self.maximal_number_of_variables = 0
        for pattern in self._patterns:
            pattern.update_number_of_variables(self)

    def arity(self):
        return len(self._patterns)

    def match_all(self, w_arguments, binding):
        if self.arity() != 0:
            for i in range(self.arity()):
                self._patterns[i].match(w_arguments[i], binding)
        return self._expression            

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return u"{" + u", ".join(map(urepr, self._patterns)) + u" ↦ " + urepr(self._expression) + u"}"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class Variable(TestEqualityMixin):

    def __init__(self, name):        
        self.name = name
        self.binding_index = -1

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return self.name + u"_" + who(self)  + ("@%s" % self.binding_index if self.binding_index != -1 else "")
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class Pattern(TestEqualityMixin):

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
    def to_repr(self):
        return u"&" + unicode(repr(self.value))
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str
    
class VariablePattern(Pattern):

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
    def to_repr(self):
        return u"&" + urepr(self.variable)
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class ConstructorPattern(Pattern):

    def __init__(self, tag, children=None):
        self._tag = tag
        self._children = children or []

    def match(self, obj, binding):
        if isinstance(obj, W_Constructor): # pragma: no branch
            if (obj.get_tag() == self._tag) and (obj.get_number_of_children() == len(self._children)):
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
    def to_repr(self):
        return u"&" + urepr(self._tag) + u"(" + u", ".join(map(urepr, self._children)) + u")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str




class Expression(TestEqualityMixin):

    def evaluate_with_binding(self, binding):
        return self.copy(binding).evaluate()

    def evaluate(self):
        raise NotImplementedError("abstract method")

    def interpret(self, binding, stack, exp_stack):
        raise NotImplementedError("abstract method")

    def copy(self, binding):
        return self

        
class ValueExpression(Expression):

    def __init__(self, value):
        self.value = value

    def evaluate(self):
        return self.value

    def interpret(self, binding, stack, exp_stack):
        stack.append(self.value)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return u"!(" + urepr(self.value) + u")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class VariableExpression(Expression):

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
    def to_repr(self):
        return u"!" + urepr(self.variable)
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class ConstructorExpression(Expression):

    def __init__(self, tag, children=None):
        self._tag = tag
        self._children = children or []

    def evaluate(self):
        return W_Constructor(self._tag, [child.evaluate() for child in self._children])

    def interpret(self, binding, stack, exp_stack):
        exp_stack.append(ConstructorCursor(self._tag, len(self._children)))
        for child in self._children:
            exp_stack.append(child)

    def copy(self, binding):
        return ConstructorExpression(self._tag, [child.copy(binding) for child in self._children])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return u"!" + urepr(self._tag) + ( (u"(" + urepr(self._children)[1:][:-1] + u")") if len(self._children) > 0 else "" )
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class CallExpression(Expression):

    def __init__(self, callee, arguments=None):
        self.callee = callee
        self.arguments = arguments or []

    def evaluate(self):
        return self.callee.evaluate().call([arg.evaluate() for arg in self.arguments])

    def interpret(self, binding, stack, exp_stack):
        exp_stack.append(self.callee)
        for arg in self.arguments:
            exp_stack.append(arg)

    def copy(self, binding):
        return CallExpression(self.callee.copy(binding), [arg.copy(binding) for arg in self.arguments])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return u"μ" + urepr(self.callee) + u"(" + urepr(self.arguments) + u")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class Cursor(Expression):
    """
    Cursors are no actual expressions but act as such on the expression stack.
    """
    pass

class ConstructorCursor(Cursor):
    def __init__(self, tag, number_of_children):
        self._tag = tag
        self._number_of_children = number_of_children

    def interpret(self, binding, stack, exp_stack):
        children = []
        for i in range(self._number_of_children):
            children.append(stack.pop())
        stack.append(W_Constructor(self._tag, children))

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return u"%" + urepr(self._tag) + u"(" + urepr(self._number_of_children) + u")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class LambdaCursor(Cursor):
    def __init__(self, lamb):
        self._lamb = lamb

    def evaluate(self):
        return self._lamb



    def interpret(self, binding, stack, exp_stack):
        self._lamb.interpret_lamdba(stack, exp_stack)

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self):
        return u"%" + urepr(self._lamb)
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class VariableUnbound(Exception):
    pass

class NoMatch(Exception):
    pass

def interpret(expressions, arguments=None, debug=False):

    stack = arguments or []
    if debug: debug_stack({'expressions': expressions, 'stack': stack})
    while len(expressions) > 0:
        expression = expressions.pop()
        expression.interpret(None, stack, expressions)
        if debug: debug_stack({'expressions': expressions, 'stack': stack})
    assert len(stack) > 0
    return stack.pop()

