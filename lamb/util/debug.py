#!/usr/bin/env python
# -*- coding: utf-8 -*-

import py

from lamb.util.view import _dot, view
from lamb.util.repr import urepr, who, uni

_iteration = 0
_stacks = {}

from lamb.model import W_Tag, W_Integer, W_Constructor, W_Lambda, Object
from lamb.shape import Shape, CompoundShape, InStorageShape
from lamb.pattern import VariablePattern, ConstructorPattern, IntegerPattern
#
# Monkeypatch debug output
#

hard_debug = False

### General ###

class __extend__(Object):
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

class __extend__(Shape):
    @uni
    def to_repr(self, seen):
        res = u"σ"
        res += u"%d" % self.get_number_of_direct_children()
        return res

class __extend__(CompoundShape):
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

class __extend__(InStorageShape):
    @uni
    def to_repr(self, seen):
        return u"◊"

### Pattern ###

class __extend__(IntegerPattern):
    @uni
    def to_repr(self, seen):
        return u"&" + unicode(repr(self.value))

class __extend__(VariablePattern):
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self.variable, seen)

class __extend__(ConstructorPattern):
    @uni
    def to_repr(self, seen):
        return u"&" + urepr(self._tag, seen) + u"(" \
            + u", ".join(map(lambda x: urepr(x, seen), self._children)) \
            + u")"

### Models ###


class __extend__(W_Tag):
    @uni
    def to_repr(self, seen):
        return u"%s/%d" % (self.name, self.arity)

class __extend__(W_Integer):
    @uni
    def to_repr(self, seen):
        return u"#%d" % self._value

class __extend__(W_Constructor):
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

class __extend__(W_Lambda):
    @uni
    def to_repr(self, seen):
        res = u"λ"
        res += self.name()
        res += u"("
        res += u"; ".join(map(lambda x: urepr(x, seen), self._rules))
        res += u")"
        return res

### Expressions ###
from lamb.expression import (W_ConstructorEvaluator,
                             W_VariableExpression, W_Call,
                             W_ConstructorCursor, W_LambdaCursor,
                             Rule, Variable)
class __extend__(W_ConstructorEvaluator):
    @uni
    def to_repr(self, seen):
        return u"^" + urepr(self._tag, seen) \
            + ( (u"(" + u", ".join(
                map(lambda x: urepr(x, seen), self._children)) + u")") \
                if len(self._children) > 0 else "")

class __extend__(W_VariableExpression):
    @uni
    def to_repr(self, seen):
        return u"!" + urepr(self.variable, seen)

class __extend__(W_Call):
    @uni
    def to_repr(self, seen):
        res = u"μ"
        if isinstance(self.callee, W_Lambda):
            res += unicode(self.callee._name)
        else:
            res += urepr(self.callee, seen)
        res += self.children_to_repr(seen)
        return res

    def children_to_repr(self, seen):
        if self.get_number_of_arguments() > 0:
            return u"(" + u", ".join(map(lambda x: urepr(x, seen), self.get_arguments())) + u")"
        else:
            return u""


class __extend__(W_ConstructorCursor):
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._tag, seen)

class __extend__(W_LambdaCursor):
    @uni
    def to_repr(self, seen):
        return u"%" + urepr(self._lamb, seen)

class __extend__(Rule):
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

class __extend__(Variable):
    @uni
    def to_repr(self, seen):
        i = ("@%s" % self.binding_index if self.binding_index != -1 else "")
        return self.name + u"_" + who(self) + i

###############################################################################

def debug_stack(stack):
    """
    print dictionary of stacks.
    """
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
