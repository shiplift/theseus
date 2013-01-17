# -*- coding: utf-8 -*-
#
# Hi.
#

class TestEqualityMixin(object):
    _mixin_ = True
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self == other
    
    
class W_Object(TestEqualityMixin):
    pass

class W_Symbol(W_Object):
    symbols = {}
    
    def __init__(self, name):
        self.name = name


    #
    # Testing and Debug
    #
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
    def to_repr(self):
        return "#" + str(self._value)
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
    def to_repr(self):
        return "(" + repr(self._tag) + ", " + repr(self._children) + ")"
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
        if len(self._rules) > 0:
            return self._rules[0].arity()
        else:
            return 0

    def call(self, w_arguments):
        assert len(w_arguments) == self.arity()
        binding = {}
        for rule in self._rules:
            try:
                expression = rule.match_all(w_arguments, binding)
            except NoMatch:
                binding = {}
            else:
                return expression.evaluate(binding)  

        raise NoMatch()

    def interpret(self, binding, stack, exp_stack):
        w_arguments = []
        for i in range(self.arity()):
            w_arguments.append(stack.pop())
        local_binding = {}
        for rule in self._rules:
            try:
                expression = rule.match_all(w_arguments, local_binding)
            except NoMatch:
                local_binding = {}
            else:
                exp_stack.append(expression)
                binding.update(local_binding)
                return

        raise NoMatch()
        
    #
    # Testing and Debug
    #
    def to_repr(self):
        return "lambda (" + repr(self._rules) + ")"
    def to_str(self):
        return "λ(" + repr(self._rules)
    __repr__ = to_repr
    __str__ = to_str


class Rule(TestEqualityMixin):

    def __init__(self, patterns, expression):
        self._patterns = patterns
        self._expression = expression

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
    def to_repr(self):
        return "[" + repr(self._patterns) + " -> " + repr(self._expression) + "]"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class Variable(TestEqualityMixin):

    def __init__(self, name):        
        self.name = name

    #
    # Testing and Debug
    #
    def to_repr(self):
        return "v_" + str(id(self)) + "_" + self.name
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class Pattern(TestEqualityMixin):
    def match(self, an_obj, binding):
        raise NotImplementedError("abstract method")

class IntegerPattern(Pattern):

    def __init__(self, value):
        self.value = value

    def match(self, obj, binding):
        if isinstance(obj, W_Integer):
            if obj._value == self.value:
                return
        raise NoMatch()
    
class VariablePattern(Pattern):

    def __init__(self, variable):
        self.variable = variable

    def match(self, obj, binding):
        assert self.variable not in binding
        binding[self.variable] = obj

class ConstructorPattern(Pattern):

    def __init__(self, tag, children=None):
        self._tag = tag
        self._children = children or []

    def match(self, obj, binding):
        if isinstance(obj, W_Constructor):
            if (obj.get_tag() == self._tag):
                if obj.get_number_of_children() == len(self._children):
                    for i in range(len(self._children)):
                        self._children[i].match(obj.get_child(i), binding)
                    return
        raise NoMatch()



class Expression(TestEqualityMixin):

    def evaluate(self, binding):
        raise NotImplementedError("abstract method")

    def interpret(self, binding, stack, exp_stack):
        raise NotImplementedError("abstract method")

class ValueExpression(Expression):

    def __init__(self, value):
        self.value = value

    def evaluate(self, binding):
        return self.value

    def interpret(self, binding, stack, exp_stack):
        if isinstance(self.value, W_Lambda):
            exp_stack.append(self.value)
        else:
            stack.append(self.value)

    #
    # Testing and Debug
    #
    def to_repr(self):
        return "?(" + repr(self.value) + ")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class VariableExpression(Expression):

    def __init__(self, variable):
        self.variable = variable

    def evaluate(self, binding):
        w_result = binding.get(self.variable, None)
        if w_result is None:
            raise VariableUnbound()
        else:            
            return w_result

    def interpret(self, binding, stack, exp_stack):
        # ok here.
        stack.append(self.evaluate(binding))
    #
    # Testing and Debug
    #
    def to_repr(self):
        return "!" + repr(self.variable)
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class ConstructorExpression(Expression):

    def __init__(self, tag, children=None):
        self._tag = tag
        self._children = children or []

    def evaluate(self, binding):
        children = [child.evaluate(binding) for child in self._children]
        return W_Constructor(self._tag, children)

    def interpret(self, binding, stack, exp_stack):
        exp_stack.append(ConstructorBuilder(self._tag, len(self._children)))
        for child in self._children:
            exp_stack.append(child)

    #
    # Testing and Debug
    #
    def to_repr(self):
        return "$" + repr(self._tag) + "(" + repr(self._children) + ")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str

class ConstructorBuilder(object):
    def __init__(self, tag, number_of_children):
        self._tag = tag
        self._number_of_children = number_of_children

    def interpret(self, binding, stack, exp_stack):
        children = []
        for i in range(self._number_of_children):
            children.append(stack.pop())
        stack.append(W_Constructor(self._tag, children))


class CallExpression(Expression):

    def __init__(self, callee, arguments=None):
        self.callee = callee
        self.arguments = arguments or []

    def evaluate(self, binding):
        w_function = self.callee.evaluate(binding)
        w_args = [arg.evaluate(binding) for arg in self.arguments]
        return w_function.call(w_args)

    def interpret(self, binding, stack, exp_stack):
        exp_stack.append(self.callee)
        for arg in self.arguments:
            exp_stack.append(arg)

    #
    # Testing and Debug
    #
    def to_repr(self):
        return "!" + repr(self.callee) + "(" + repr(self.arguments) + ")"
    to_str = to_repr
    __repr__ = to_repr
    __str__ = to_str


class VariableUnbound(Exception):
    pass

class NoMatch(Exception):
    pass



def interpret(expressions, arguments=None):

    binding = {}
    stack = arguments or []
    while len(expressions) > 0:
        expression = expressions.pop()
        expression.interpret(binding, stack, expressions)
    assert len(stack) > 0
    return stack.pop()

