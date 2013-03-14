#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Hi.
#
from rpython.rlib import jit
from rpython.rlib.unroll import unrolling_iterable
from rpython.rlib.objectmodel import compute_identity_hash, r_dict

from lamb.util.repr import uni, who, urepr
from lamb.util.debug import debug_stack
from lamb.util.testing import HelperMixin
from lamb.stack import ExecutionStackElement, OperandStackElement

from lamb.shape import CompoundShape, InStorageShape, find_shape_tuple


class W_Object(HelperMixin):

    _attrs_ = []

    def shape(self):
        return InStorageShape()
    #
    # Expression behavior
    #
    def evaluate_with_binding(self, binding):
        return self.copy(binding).evaluate()

    def evaluate(self):
        return self

    def interpret(self, op_stack, ex_stack):
        return (OperandStackElement(self, op_stack), ex_stack)

    def copy(self, binding):
        return self


class W_Tag(W_Object):
    tags = {}

    _immutable_fields_ = ['name', 'arity', '_cursor', 'default_shape']

    def __init__(self, name, arity):
        self.name = name
        self.arity = arity
        self._cursor = W_ConstructorCursor(self)
        self.default_shape = CompoundShape(self, [InStorageShape()] * arity)
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

    _immutable_fields_ = ['_shape']

    def __init__(self, shape):
        assert isinstance(shape, CompoundShape)
        self._shape = shape

    def _init_storage(self, stroage):
        pass

    def get_storage(self):
        return []

    def get_storage_at(self, index):
        raise IndexError()

    def get_storage_width(self):
        return 0

    def get_tag(self):
        return self.shape()._tag

    def get_children(self):
        return self.shape().get_children(self)

    def get_child(self, index):
        return self.shape().get_child(self, index)

    def get_number_of_children(self):
        return self.shape().get_number_of_direct_children()

    def shape(self):
        return jit.promote(self._shape)
    #
    # Expression behavior
    #
    @jit.unroll_safe
    def copy(self, binding):
        children = [self.get_child(index).copy(binding) for index in range(self.get_number_of_children())]
        return W_ConstructorEvaluator(self.get_tag(), children)

    def evaluate(self):
        return w_constructor(self.get_tag(), [child.evaluate() for child in self.get_children()])


    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"Γ" + u"%s%s" % (urepr(self.get_tag(), seen), self.children_to_repr(seen))

    def children_to_repr(self, seen):
        def mini_urepr(x):
            s = set(seen)
            s.discard(x)
            return urepr(x, s)

        if self.get_number_of_children() > 0:
            return u"(" + u", ".join(map(mini_urepr, self.get_children())) + u")"
        else:
            return u""

    def __eq__(self, other):
        if isinstance(other, W_Constructor):
            if self.get_number_of_children() == other.get_number_of_children():
                return self.get_children() == other.get_children()
        return False

class W_NAryConstructor(W_Constructor):

    _immutable_fields_ = ['_storage[*]']

    def _init_storage(self, storage):
        self._storage = storage or []

    def get_storage(self):
        return self._storage

    def get_storage_at(self, index):
        return self._storage[index]

    def get_storage_width(self):
        return len(self._storage)

STORAGE_ATTR_TEMPLATE = "storage_%d"

def constructor_class_name(n_storage):
    return 'W_Constructor%d' % n_storage


def generate_constructor_class(n_storage):

    storage_iter = unrolling_iterable(range(n_storage))

    class constructor_class(W_Constructor):
        _immutable_fields_ = [(STORAGE_ATTR_TEMPLATE % x) for x in storage_iter]

        def _init_storage(self, storage):
            for x in storage_iter:
                setattr(self, STORAGE_ATTR_TEMPLATE % x, storage[x])

        def get_storage(self):
            result = [None] * n_storage
            for x in storage_iter:
                result[x] = getattr(self, STORAGE_ATTR_TEMPLATE % x)
            return result

        def get_storage_at(self, index):
            for x in storage_iter:
                if x == index:
                    return getattr(self, STORAGE_ATTR_TEMPLATE % x)
            raise IndexError

        def get_storage_width(self):
            return n_storage

    constructor_class.__name__ = constructor_class_name(n_storage)
    return constructor_class

constructor_classes = [W_Constructor]
for n_storage in range(1, 10):
    constructor_classes.append(generate_constructor_class(n_storage))

class_iter = unrolling_iterable(enumerate(constructor_classes))

def select_constructor_class(storage):
    length = len(storage)
    for i, cls in class_iter:
        if i == length:
            return cls
    # otherwise:
    return W_NAryConstructor


def prepare_constructor(tag, children):
    """
    create what is necessary to build a constructor.
    """
    pre_shape = tag.default_shape
    shape, storage = pre_shape.fusion(children)
    return (shape, storage)

def w_constructor(tag, children):
    shape, storage = prepare_constructor(tag, children)
    # from lamb.util.debug import storagewalker
    # print "t:", tag, "\n\tc:", children, "\n\tts:", tag.default_shape, "\n\tsh:", shape, "\n\tst:", storagewalker(storage)
    constr_cls = select_constructor_class(storage)
    constr = constr_cls(shape)
    constr._init_storage(storage)
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

    @jit.elidable
    def arity(self):
        assert len(self._rules) > 0
        return self._rules[0].arity

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
    def interpret_lambda(self, op_stack, ex_stack):
        jit.promote(self)
        w_arguments = []
        for i in range(self.arity()):
            w_arguments.append(op_stack._data)
            op_stack = op_stack._next
        for rule in self._rules:
            try:
                binding = [None] * rule.maximal_number_of_variables
                expression = rule.match_all(w_arguments, binding)
            except NoMatch:
                pass
            else:
                ex_stack = ExecutionStackElement(expression.copy(binding), ex_stack)
                return (op_stack, ex_stack)

        raise NoMatch()

    #
    # Testing and Debug
    #
    def name(self):
        if len(self._name) > 0:
            return unicode(self._name)
        else:
            return who(self)

    @uni
    def to_repr(self, seen):
        res = u"λ"
        res += self.name()
        res += u"("
        res += u"; ".join(map(lambda x: urepr(x, seen), self._rules))
        res += u")"
        return res

class W_PureExpression(W_Object):
    """
    Objects that only ever live on the expression stack
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
    def interpret(self, op_stack, ex_stack):
        ex_stack = ExecutionStackElement(self._tag._cursor, ex_stack)
        for child in self._children:
            ex_stack = ExecutionStackElement(child, ex_stack)
        return (op_stack, ex_stack)


    @jit.unroll_safe
    def copy(self, binding):
        return W_ConstructorEvaluator(self._tag, [child.copy(binding) for child in self._children])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"^" + urepr(self._tag, seen) + ( (u"(" + u", ".join(map(lambda x: urepr(x, seen), self._children)) + u")") if len(self._children) > 0 else "")


class W_VariableExpression(W_PureExpression):

    _immutable_fields_ = ['variable']

    def __init__(self, variable):
        self.variable = variable

    def resolve(self, binding):
        # var = jit.promote(self.variable)
        var = self.variable
        w_result = binding[var.binding_index]

        if w_result is None:
            raise VariableUnbound()
        else:
            return w_result

    def evaluate(self): # pragma: no cover
        # should not happen
        raise VariableUnbound()

    def interpret(self, op_stack, ex_stack): # pragma: no cover
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
    def interpret(self, op_stack, ex_stack):
        lamb = self.callee
        jit.promote(lamb)
        assert isinstance(lamb, W_Lambda)
        ex_stack = ExecutionStackElement(lamb._cursor, ex_stack)
        return (op_stack, ex_stack)

    @jit.unroll_safe
    def copy(self, binding):
        return w_call(self.callee.copy(binding), [argument.copy(binding) for argument in self.get_arguments()])

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        res = u"μ"
        if isinstance(self.callee, W_Lambda):
            res += unicode(self.callee._name)
        else:
            res += urepr(self.callee, seen)
        res += self.children_to_repr(seen)
        return res

    #
    # Testing and Debug
    #
    def children_to_repr(self, seen):
        if self.get_number_of_arguments() > 0:
            return u"(" + u", ".join(map(lambda x: urepr(x, seen), self.get_arguments())) + u")"
        else:
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
    def interpret(self, op_stack, ex_stack):
        # super
        (op_stack, ex_stack) = W_Call.interpret(self, op_stack, ex_stack)
        for index in range(self.get_number_of_arguments()):
            arg = self.get_argument(index)
            ex_stack = ExecutionStackElement(arg, ex_stack)
        return (op_stack, ex_stack)



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
        def interpret(self, op_stack, ex_stack):
            # super
            (op_stack, ex_stack) = W_Call.interpret(self, op_stack, ex_stack)
            for x in arguments_iter:
                argument = getattr(self, ARG_ATTR_TEMPLATE % x)
                ex_stack = ExecutionStackElement(argument, ex_stack)
            return (op_stack, ex_stack)

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

    _immutable_fields_ = ['_tag']

    def __init__(self, tag):
        self._tag = tag

    @jit.unroll_safe
    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        children = []
        for i in range(self._tag.arity):
            children.append(op_stack._data)
            op_stack = op_stack._next
        op_stack = OperandStackElement(w_constructor(self._tag, children), op_stack)
        return (op_stack, ex_stack)


    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._tag, seen)

class W_LambdaCursor(W_Cursor):

    _immutable_fields_ = ['_lamb']

    def __init__(self, lamb):
        self._lamb = lamb

    def interpret(self, op_stack, ex_stack):
        jit.promote(self)
        return self._lamb.interpret_lambda(op_stack, ex_stack)

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
        return self.__class__ == other.__class__ and  self._lamb is other._lamb


class Rule(HelperMixin):

    _immutable_fields_ = ['_patterns[*]', 'arity', '_expression', 'maximal_number_of_variables']

    def __init__(self, patterns, expression):
        self._patterns = patterns
        self.arity = len(patterns)
        self._expression = expression
        self.maximal_number_of_variables = 0
        for pattern in self._patterns:
            pattern.update_number_of_variables(self)

    @jit.unroll_safe
    def match_all(self, w_arguments, binding):
        if self.arity != 0:
            for i in range(self.arity):
                self._patterns[i].match(w_arguments[i], binding)
        return self._expression

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        res = u""
        pats_seen = set(seen)
        res += u"{%s}" % (u", ".join(map(lambda x: urepr(x, pats_seen), self._patterns)))
        res += u" ↦ "
        exp_seen = set(seen)
        res += urepr(self._expression, exp_seen)
        return res


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
        assert self._tag.arity == len(self._children)

    @jit.unroll_safe
    def match(self, obj, binding):
        if not isinstance(obj, W_Constructor):
            raise NoMatch()

        tag = jit.promote(obj.get_tag())
        if tag is self._tag:
            for i in range(tag.arity):
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

class VariableUnbound(Exception):
    pass

class NoMatch(Exception):
    pass

#
#
#
#  Support for the JIT.
#
#



def get_printable_location(current_cursor, current_args_shapes): #pragma: no cover
    res = ""
    if current_cursor is None:
        res += "<None>"
    else:
        if isinstance(current_cursor, W_LambdaCursor):
            res += "Lamb[%s/%s] " % (current_cursor._lamb._name, current_cursor._lamb.arity())
        elif isinstance(current_cursor, W_ConstructorCursor):
            res +=  "Cons[%s/%s] " % (current_cursor._tag.name, current_cursor._tag.arity)
        else:
            return "<Unknown>"
        res += current_args_shapes.merge_point_string()
    return res

jitdriver = jit.JitDriver(
    greens=["current_cursor", "current_args_shapes"],
    reds=["op_stack", "ex_stack", "expr"],
    get_printable_location=get_printable_location,
)

# shortcuts to access stack content.
def ex_data_or_none(stack): return stack._data if stack is not None else None
def op_data_or_none(stack): return stack._data if stack is not None else None


@jit.unroll_safe
def _stack_to_list(op_stack, depth):
    """
    transform `op_stack` of (possibly) W_Constructors into
    list of Shapes, if they have
    """
    op_s = op_stack
    shapes = [None] * depth
    for i in range(depth):
        w = op_data_or_none(op_s)
        shapes[i] = w._shape if isinstance(w, W_Constructor) else None
        op_s = op_s._next if op_s is not None else None
    return shapes

def shapes_of_current_args(depth, op_stack):
    shapes = _stack_to_list(op_stack, depth)
    tup = find_shape_tuple(shapes)
    return tup

def interpret(expression_stack, arguments_stack=None, debug=False, debug_callback=None):

    op_stack = arguments_stack
    ex_stack = expression_stack

    # jit greens
    expr = None
    current_cursor = None
    current_args_shapes = None

    if debug_callback is None: debug_callback = debug_stack

    while True:
        ex_data = ex_data_or_none(ex_stack)
        if isinstance(ex_data, W_Cursor):
            current_cursor = jit.promote(ex_data)
            if isinstance(current_cursor, W_LambdaCursor):
                current_args_shapes = shapes_of_current_args(current_cursor._lamb.arity(), op_stack)
            elif isinstance(current_cursor, W_ConstructorCursor):
                current_args_shapes = shapes_of_current_args(current_cursor._tag.arity, op_stack)

            jitdriver.can_enter_jit(
                expr=expr, op_stack=op_stack, ex_stack=ex_stack,
                current_cursor=current_cursor, current_args_shapes=current_args_shapes,
            )
        jitdriver.jit_merge_point(
            expr=expr, op_stack=op_stack, ex_stack=ex_stack,
            current_cursor=current_cursor, current_args_shapes=current_args_shapes
        )
        if ex_stack is None:
            break


        if debug: debug_callback({'ex_stack':ex_stack, 'op_stack':op_stack})
        expr = ex_stack._data
        ex_stack = ex_stack._next
        (op_stack, ex_stack) = expr.interpret(op_stack, ex_stack)

    if debug: debug_callback({'ex_stack':ex_stack, 'op_stack':op_stack})
    return op_stack._data
