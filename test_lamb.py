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
    
    def test_futile(self):
        w_int = integer(1)
        assert isinstance(w_int, W_Integer)

class TestContstructor(object):

    def test_empty_constructor(self):
        w_res = W_Constructor(symbol("zork"))
        assert isinstance(w_res, W_Constructor)
        assert w_res.tag is symbol("zork")
        assert len(w_res.children()) is 0

    def test_simple_constructor(self):
        w_res = W_Constructor(symbol("zork"), W_Integer(1))
        assert isinstance(w_res, W_Constructor)
        assert w_res.tag is symbol("zork")
        assert len(w_res.children()) is 1

    def test_still_simple_constructor(self):
        w_res = W_Constructor(symbol("zork"), W_Integer(1), W_Integer(2))
        assert isinstance(w_res, W_Constructor)
        assert w_res.tag is symbol("zork")
        assert len(w_res.children()) is 2

    def test_simple_nested_constructor(self):
        w_res = W_Constructor(symbol("zork"), W_Constructor(symbol("barf")))
        assert isinstance(w_res, W_Constructor)
        assert w_res.tag is symbol("zork")
        assert len(w_res.children()) is 1

        w_subcons = w_res.children()[0]
        assert isinstance(w_subcons, W_Constructor)
        assert w_subcons.tag is symbol("barf")
        assert len(w_subcons.children()) is 0
        
        
        
        


