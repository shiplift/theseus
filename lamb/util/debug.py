#!/usr/bin/env python
# -*- coding: utf-8 -*-

import py, sys

from lamb.util.view import _dot, view
from lamb.util.repr import urepr, who, uni

_iteration = 0
_stacks = {}
_current_lambda = None

from lamb import model, shape, pattern, expression, execution, stack, object as obj
# Monkeypatch debug output
#

sys.setrecursionlimit(1000000)

hard_debug = False

### General ###

class __extend__(obj.Object):
    def __repr__(self):
        r = self.to_repr(set())
        r = r if isinstance(r, str) else r.encode("utf-8")
        if hard_debug:
            r += "<" + who(self).encode("utf-8") + ">"
        return r

    @uni
    def to_repr(self, seen):
        return object.__repr__(self)

### Shapes ###

class __extend__(shape.Shape):
    @uni
    def to_repr(self, seen):
        res = u"σ"
        res += u"%d" % self.get_number_of_direct_children()
        return res

class __extend__(shape.CompoundShape):
    @uni
    def to_repr(self, seen):
        def mini_urepr(x):
            s = set(seen)
            s.discard(x)
            return urepr(x, s)

        res = u"σ"
        res += urepr(self._tag, seen)
        res += u"["
        res += ", ".join(map(mini_urepr, self._structure))
        res += u"]"
        return res

class __extend__(shape.InStorageShape):
    @uni
    def to_repr(self, seen):
        return u"◊"

### Pattern ###

class __extend__(pattern.IntegerPattern):
    @uni
    def to_repr(self, seen):
        return u"&" + unicode(repr(self.value))

class __extend__(pattern.VariablePattern):
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self.variable, seen)

class __extend__(pattern.ConstructorPattern):
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self._tag, seen) + u"(" \
            + u", ".join(map(lambda x: urepr(x, seen), self._children)) \
            + u")"

### Models ###


class __extend__(model.W_Tag):
    @uni
    def to_repr(self, seen):
        return u"%s/%d" % (self.name, self.arity())

class __extend__(model.W_Integer):
    @uni
    def to_repr(self, seen):
        return u"#%d" % self._value

class __extend__(model.W_String):
    @uni
    def to_repr(self, seen):
        if len(self._value) > 0:
            return u"»" + self._value.decode("utf-8") + u"«"
        else:
            return u"»«"

class __extend__(model.W_Constructor):
    @uni
    def to_repr(self, seen, maxdepth=8):
        return u"Γ" + u"%s%s" % (urepr(self.get_tag(), seen), self.children_to_repr(seen, maxdepth))

    def children_to_repr(self, seen, maxdepth=8):
        if maxdepth <= 0:
            return u"…"

        def mini_urepr(x):
            s = set(seen)
            s.discard(x)
            return urepr(x, s)

        if self.get_number_of_children() > 0:
            res = u"("
            first = True
            for child in self.get_children():
                res += u", " if not first else u""
                first = False
                if isinstance(child, model.W_Constructor):
                    ret = child.to_repr(seen, maxdepth - 1)
                    res += ret if isinstance(ret, unicode) else ret.decode("utf-8")
                else:
                    res += mini_urepr(child)
            return res + u")"
        else:
            return u""

class __extend__(model.W_Lambda):
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

class __extend__(model.W_Primitive):
    @uni
    def to_repr(self, seen):
        res = u"⟪"
        res += self.name()
        res += u"⟫"
        res += u"/"
        res += u"%d" % self.arity()
        return res

### Expressions ###

#### helper
def name_if_lam(c, seen):
    res = u""
    if isinstance(c, expression.Quote):
        res += "'"
        c = c.w_value
    if isinstance(c, model.W_Lambda):
        res += u"λ" + unicode(c._name)
    else:
        res += urepr(c, seen)
    return res

class __extend__(expression.W_ConstructorEvaluator):
    @uni
    def to_repr(self, seen):
        return u"^" + urepr(self._tag, seen) \
            + ( (u"(" + u", ".join(
                map(lambda x: urepr(x, seen), self._children)) + u")") \
                if len(self._children) > 0 else "")

class __extend__(expression.W_VariableExpression):
    @uni
    def to_repr(self, seen):
        return u"!" + urepr(self.variable, seen)

class __extend__(expression.Quote):
    @uni
    def to_repr(self, seen):
        return u"'" + urepr(self.w_value, seen)

class __extend__(expression.W_Call):

    @uni
    def to_repr(self, seen):
        res = u"μ" + name_if_lam(self.callee, seen)
        res += self.children_to_repr(seen)
        return res

    def children_to_repr(self, seen):
        def rp(o):
            return name_if_lam(o, seen)
        if self.get_number_of_arguments() > 0:
            return u"(" + u", ".join(map(rp, self.get_arguments())) + u")"
        else:
            return u""


class __extend__(expression.W_ConstructorCursor):
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._tag, seen)

class __extend__(expression.W_LambdaCursor):
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._lamb, seen)

class __extend__(expression.Rule):
    @uni
    def to_repr(self, seen):
        res = u""
        pats_seen = set(seen)
        res += u"{%s}" % (u", ".join(
            map(lambda x: urepr(x, pats_seen), self._patterns)))
        res += u" ↦ "
        exp_seen = set(seen)
        res += urepr(self._expression, exp_seen)
        return res

class __extend__(expression.Variable):
    @uni
    def to_repr(self, seen):
        i = ("@%s" % self.binding_index if self.binding_index != -1 else "")
        return self.name + u"_" + who(self) + i


class __extend__(stack.StackElement):
    #
    # useful when inspecing the stack
    #
    def linearize(self): # pragma: no cover
        element = self
        ret = []
        while element is not None:
            ret.insert(0, element)
            try:
                element = element._next
            except AttributeError:
                element = None
        return ret

    #
    # Testing and Debug
    #
    @uni
    def to_repr(self, seen):
        r = u""
        if self._next is None:
            r += u"⊥"
        if self._data is not None:
            r += urepr(self._data, seen)
        return r

### Execution ###

class __extend__(execution.Env):
    @uni
    def to_repr(self, seen):
        def rp(o):
            return name_if_lam(o, seen)
        return (u"Env[" +
                u", ".join([rp(x) for x in self._get_full_list()]) +
                u"]")

class __extend__(execution.Continuation):
    @uni
    def to_repr(self, seen):
        def rp(o):
            return name_if_lam(o, seen)
        r = u"C%d" % self._get_size_list()
        r += (urepr(self.w_expr, seen) + u"/[" +
              u", ".join([rp(x) for x in self._get_full_list()]) +
              u"]")
        if not isinstance(self.cont, execution.FinishContinuation):
            r += u"\n\t\t --> " + urepr(self.cont, seen)
        return r

class __extend__(execution.FinishContinuation):
    @uni
    def to_repr(self, seen):
        r = u"C⊥"
        return r

###############################################################################

def debug_stack(stack):
    """
    print dictionary of stacks.
    """
    global _current_lambda
    print
    #print "%: Cursor, !: Expression, μ: Call, #: Value, λ: Lambda, &: Pattern, {}: Rule, _ Variable"

    d = { 'ex_stack': stack.execution_stack, 'op_stack': stack.operand_stack }

    length = 60

    def i_(o):
        if hasattr(o, 'linearize'):
            return o.linearize()
        try: [ e for e in o ]
        except TypeError: return [o]
        else: return o
    def t_(o):
        return o[:length] if len(o) > length else o

    from itertools import izip_longest
    k = d.keys()
    v = map(list, map(list, map(i_, d.values())))

    update_stack_mappings(stack)
    if stack.execution_stack is not None:
        expr, _ = stack.execution_stack.pop()
        if isinstance(expr, expression.W_LambdaCursor):
            _current_lambda = expr._lamb

    if _current_lambda is not None:
        print _current_lambda
    stacklists = map(list, map(reversed, zip(*list(izip_longest(*v, fillvalue="")))))
    stackreprs = map(lambda x: map(lambda y: t_(urepr(y)) if y else u"", x), stacklists)
    stacks = map(lambda x: map(lambda y: (u"[%%-%ds]" % length) % y, x), stackreprs)

    tops = map(lambda x: [(u"%%-%ds" % (length + 3)) % x], k)
    stat = map(lambda x: x[0] + x[1], list(zip(tops,stacks)))
    lines = map(lambda x: u" ".join(x), map(list, zip(*stat)))
    print "\n".join(map(lambda x: x.encode("utf-8"), lines))

def update_stack_mappings(stack):
    """
    update the global stack mapping to be viewed with view_stacks()
    """
    import copy
    global _stacks
    global _iteration

    d = { 'ex_stack': stack.execution_stack, 'op_stack': stack.operand_stack }
    k = d.keys()
    for i in range(len(k)):
        localkey = "_%03d%s" % (_iteration, k[i])
        _stacks[localkey] = copy.copy(d[k[i]])
    _iteration += 1



def view_stacks():
    """
    view all stacks using dot/pygame as captured with update_stack_mappings()
    """
    view(**_stacks)


def storagewalker(l):
    def sw(l, seen):
        res = u"["
        first = True
        for item in l:
            if first:
                first = False
            else:
                res += u", "
            if not item in seen:
                seen.add(item)
                if hasattr(item, "get_storage"):
                    res += sw(item.get_storage(), seen)
                else:
                    res += urepr(item)
            else:
                res += u"…"
        res += u"]"
        return res
    return sw(l, set())
