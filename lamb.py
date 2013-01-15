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

