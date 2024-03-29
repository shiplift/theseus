#!/usr/bin/env python
# -*- coding: utf-8 -*-

import py, sys

from theseus.util.view import _dot, view
from theseus.util.repr import urepr, who, uni


from theseus import model, shape, pattern, expression, execution, object as obj
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
        children = self.get_number_of_direct_children()
        if children > 0:
            res += u"%d" % children
        return res

class __extend__(shape.CompoundShape):
    @uni
    def to_repr(self, seen):
        def mini_urepr(x):
            s = set(seen)
            s.discard(x)
            return urepr(x, s)

        res = u"σ%s" % self._tag.name
        if len(self._structure) > 0:
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
        if self.arity() > 0:
            return u"%s/%d" % (self.name, self.arity())
        else:
            return u"%s" % self.name

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
        def mini_urepr(x):
            s = set(seen)
            s.discard(x)
            return urepr(x, s)
        return u"Γ" + u"%s%s" % (mini_urepr(self.get_tag()), self.children_to_repr(seen, maxdepth))

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
