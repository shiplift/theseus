
import py

from lamb import *


#
# Construction Helper
#
def pattern(obj):
    if isinstance(obj, Variable):
        return VariablePattern(obj)
    elif isinstance(obj, W_Integer):
        return pattern_from_integer(obj)
    else:
        return pattern_from_constructor(obj)


def pattern_from_constructor(w_constructor):
    _tag = w_constructor.get_tag()
    _children = [pattern(w_constructor.get_child(i)) for i in range(w_constructor.get_number_of_children())]
    return ConstructorPattern(_tag, _children)

def pattern_from_integer(w_integer):
    return IntegerPattern(w_integer._value)

def cons(tag, *children):
    return W_Constructor(symbol(tag), list(children))

def integer(value):
    assert isinstance(value, int)
    return W_Integer(value)

def expression(obj):
    if isinstance(obj, Variable):
        return VariableExpression(obj)
    elif isinstance(obj, W_Integer):
        return IntegerExpression(obj)
    else:
        return expression_from_constructor(obj)

def expression_from_constructor(w_constructor):
    _tag = w_constructor.get_tag()
    _children = [expression(w_constructor.get_child(i)) for i in range(w_constructor.get_number_of_children())]
    return ConstructorExpression(_tag, _children)

    


#
# Tests
#

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
        w_res = cons("zork")
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 0

    def test_simple_constructor(self):
        w_res = cons("zork", integer(1))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 1

    def test_still_simple_constructor(self):
        w_res = cons("zork", integer(1), integer(2))
        assert isinstance(w_res, W_Constructor)
        assert w_res.get_tag() is symbol("zork")
        assert w_res.get_number_of_children() is 2

    def test_simple_nested_constructor(self):
        w_res = cons("zork", cons("barf"))
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

    def test_int_pattern(self):
        w_int = integer(1)
        pat = pattern(w_int)
        w_obj = integer(1)
        
        binding = {}
        pat.match(w_obj, binding)
        assert True # should not raise.

        w_obj = integer(2)
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)

        

    def test_catch_all(self):
        var = Variable("x")
        pat = pattern(var)
        w_obj = cons("barf")
        binding = {}
        pat.match(w_obj, binding)
        assert binding[var] == w_obj
        
        
    def test_simple_constructor(self):
        w_cons = cons("barf")
        pat = pattern(w_cons)
        w_obj = cons("barf")

        binding = {}
        pat.match(w_obj, binding)
        assert binding == {}

        w_obj = cons("zork")
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)


    def test_constructor_with_int(self):
        w_cons = cons("zork", integer(1))
        pat = pattern(w_cons)
        w_obj = cons("zork", integer(1))

        binding = {}
        pat.match(w_obj, binding)
        assert binding == {}

        w_obj = cons("zork", integer(2))
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)
        

    def test_nested_constructor(self):
        pat = pattern(cons("barf", cons("zork")))
        w_obj = cons("barf", cons("zork"))
        
        binding = {}
        pat.match(w_obj, binding)
        assert binding == {}

        w_obj = cons("barf", cons("moep"))
        with py.test.raises(NoMatch) as e:
            pat.match(w_obj, binding)


    def test_constructor_with_var(self):
        var = Variable("x")
        pat = pattern(cons("zork", var))
        w_int = integer(1)
        w_obj = cons("zork", w_int)

        binding = {}
        pat.match(w_obj, binding)
        assert binding[var] == w_int

    def test_complex(self):

        var1 = Variable("x")
        var2 = Variable("y")
        var3 = Variable("z")

        w_int1 = integer(1)
        w_int2 = integer(2)
        w_int3 = integer(3)

        w_cons1 = cons("zork")
        w_cons2 = cons("barf", w_int1, w_int2)
        w_cons3 = cons("moep", w_cons1)
        w_cons4 = cons("universe", w_cons2, w_cons3)

        pat1 = pattern(cons("universe", var1, var2))
        pat2 = pattern(cons("moep", var3))
        pat3 = pattern(cons("universe", cons("barf", var1, var2), var3))

        binding = {}
        pat1.match(w_cons4, binding)
        assert binding[var1] == w_cons2
        assert binding[var2] == w_cons3

        binding = {}
        pat2.match(w_cons3, binding)
        assert binding[var3] == w_cons1

        binding = {}
        pat3.match(w_cons4, binding)
        assert binding[var1] == w_int1
        assert binding[var2] == w_int2
        assert binding[var3] == w_cons3


class TestExpression(object):

    def test_simple_expression(self):
        w_int = integer(1)
        expr = expression(w_int)

        binding = {}
        w_res = expr.resolve(binding)
        assert w_res is w_int

    def test_variable_expression(self):

        w_int = integer(42)
        var = Variable("x")
        expr = expression(var)

        binding = { var : w_int }
        w_res = expr.resolve(binding)
        assert w_res is w_int
        
    def test_simple_constructor_expression(self):

        expr = ConstructorExpression(symbol("barf"), [])

        binding = {}
        w_res = expr.resolve(binding)
        assert w_res.get_tag() is symbol("barf")
        assert w_res.get_number_of_children() is 0

    def test_constructor_with_int(self):
        w_int = integer(1)
        w_cons = cons("zork", w_int)
        expr = expression(w_cons)

        binding = {}
        w_res = expr.resolve(binding)
        assert w_res.get_tag() == w_cons.get_tag()
        assert w_res.get_number_of_children() == w_cons.get_number_of_children()
        assert w_res.get_child(0) == w_int
        

    def test_constructor_with_var(self):
        var = Variable("x")
        w_cons = cons("zork", var)
        w_int = integer(1)
        expr = expression(w_cons)

        binding = { var : w_int }
        w_res = expr.resolve(binding)
        assert w_res.get_child(0) == w_int

    def test_complex(self):

        var1 = Variable("x")
        var2 = Variable("y")
        var3 = Variable("z")

        w_int1 = integer(1)
        w_int2 = integer(2)
        w_int3 = integer(3)

        w_cons1 = cons("zork")
        w_cons2 = cons("barf", w_int1, w_int2)
        w_cons3 = cons("moep", w_cons1)

        expr1 = expression(cons("universe", var1, var2))
        expr2 = expression(cons("moep", var3))
        expr3 = expression(cons("universe", cons("barf", var1, var2), var3))

        binding = { var1: w_cons2, var2: w_cons3, var3: w_cons1 }

        w_res = expr1.resolve(binding)
        assert w_res.get_tag() is symbol("universe")
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is symbol("barf")
        assert w_child0.get_child(0) is w_int1
        assert w_child0.get_child(1) is w_int2
        w_child1 = w_res.get_child(1)
        assert w_child1.get_tag() is symbol("moep")
        assert w_child1.get_child(0).get_tag() is symbol("zork")

        w_res = expr2.resolve(binding)
        assert w_res.get_tag() is symbol("moep")
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is symbol("zork")

        w_res = expr3.resolve(binding)
        assert w_res.get_tag() is symbol("universe")
        w_child0 = w_res.get_child(0)
        assert w_child0.get_tag() is symbol("barf")
        w_child00 = w_child0.get_child(0)
        assert w_child00.get_tag() is symbol("barf")
        assert w_child00.get_child(0) is w_int1
        assert w_child00.get_child(1) is w_int2
        w_child01 = w_child0.get_child(1)
        assert w_child01.get_tag() is symbol("moep")
        assert w_child01.get_child(0).get_tag() is symbol("zork")
        w_child1 = w_res.get_child(1)
        assert w_child1.get_tag() is symbol("zork")

        
        
        
        
# note to self: resolve binding == copy exrp, replace var by binding
 
