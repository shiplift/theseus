from lamb import *


class TestSymbol(object):

    def test_newsymbol(self):
        w_res = W_Symbol("name")
        assert isinstance(w_res, W_Symbol)
        assert w_res.name == "name"

    def test_interning(self):
        w_res1 = symbol("name")
        w_res2 = symbol("name")
        assert w_res1 is w_res2

    def test_non_interning(self):
        w_res1 = W_Symbol("name")
        w_res2 = W_Symbol("name")
        assert w_res1 is not w_res2

class TestInteger(object):
    pass

class TestContstructor(object):

    def test_empty_constructor(self):
        w_res = W_Contstructor(symbol("zork"))
        assert isinstance(w_res, W_Contstructor)
        assert w_res.tag is symbol("zork")
