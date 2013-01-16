from lamb import *

def pattern(obj):
    if isinstance(obj, Variable):
        return VariablePattern(obj)
    else:
        return pattern_from_constructor(obj)


def pattern_from_constructor(constructor):
    _tag = constructor.get_tag()
    _children = [pattern(constructor.get_child(i)) for i in range(constructor.get_number_of_children())]
    return ConstructorPattern(_tag, _children)



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
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 0

    def test_simple_constructor(self):
        w_res = W_Constructor(symbol("zork"), [W_Integer(1)])
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 1

    def test_still_simple_constructor(self):
        w_res = W_Constructor(symbol("zork"), [W_Integer(1), W_Integer(2)])
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 2

    def test_simple_nested_constructor(self):
        w_res = W_Constructor(symbol("zork"), [W_Constructor(symbol("barf"))])
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 1

        w_subcons = w_res.get_child(0)
        assert isinstance(w_subcons, W_Constructor)
        assert w_subcons.get_tag() is symbol("barf")
        assert w_subcons.get_number_of_children() is 0

class TestVariable(object):

    def test_variable(self):
        res = Variable("x")
        assert isinstance(res, Variable)

        res2 = Variable("y")
        assert res2 is not res

        res3 = Variable("x")
        assert res3 is not res

class TestPattern(object):

    def test_catch_all(self):
        var = Variable("x")
        pat = pattern(var)
        w_obj = W_Constructor(symbol("barf"))
        binding = {}
        pat.match(w_obj, binding)
        assert binding[var] == w_obj
        
    def test_simple_constructor(self):
        w_cons = W_Constructor(symbol("barf"))
        pat = pattern_from_constructor(w_cons)
        w_obj = W_Constructor(symbol("barf"))

        binding = {}
        pat.match(w_obj, binding)
        assert binding == {}
        
