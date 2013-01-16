# -*- coding: utf-8 -*-
#
# Hi.
#
    
class W_Object(object):
    pass

class W_Symbol(W_Object):
    symbols = {}
    

    def __init__(self, name):
        self.name = name

    def to_repr(self):
        return self.name

    to_string = to_repr


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
        self.value = value

    def to_repr(self):
        return str(self.value)

    to_str = to_repr

def integer(value):
    assert isinstance(value, int)
    return W_Integer(value)
   

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


class Variable(object):

    def __init__(self, name):        
        self.name = name


class Pattern(object):
    def match(self, an_obj, binding):
        raise NotImplementedError("abstract method")
        
class VariablePattern(Pattern):

    def __init__(self, variable):
        self.variable = variable

    def match(self, obj, binding):
        assert self.variable not in binding
        binding[self.variable] = obj

class ConstructorPattern(object):

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

class NoMatch(Exception):
    pass
                    
