#!/usr/bin/env python
# -*- coding: utf-8 -*-

import py

from util_view import _dot, view, DebugVizualizationMixin
from util_repr import urepr, who, uni

_iteration = 0
_stacks = {}

def debug_stack(w_stack, e_stack, **rest):
    """
    print dictionary of stacks.
    """
    print
    print "%: Cursor, !: Expression, μ: Call, #: Value, λ: Lambda, &: Pattern, {}: Rule, _ Variable"

    length = 60

    d = {'w_stack':w_stack,'e_stack':e_stack}
    
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

    update_stack_mappings(d)
    
    stacks = map(lambda x: map(lambda y: (u"[%%-%ds]" % length) % y, map(t_, map(lambda y: urepr(y) if y else u"", x))), map(list, map(reversed, zip(*list(izip_longest(*v, fillvalue=""))))))
    tops = map(lambda x: [(u"%%-%ds" % (length + 3)) % x], k)
    stat = map(lambda x: x[0] + x[1], list(zip(tops,stacks)))
    lines = map(lambda x: u" ".join(x), map(list, zip(*stat)))
    print u"\n".join(lines)

def update_stack_mappings(d):
    """
    update the global stack mapping to be viewed with view_stacks()
    """
    import copy
    global _stacks
    global _iteration

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

#
# Helper for equality testing in tests
#
class HelperMixin(DebugVizualizationMixin):
    _mixin_ = True
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        r = self.to_repr(set())
        return r if isinstance(r, str) else r.encode("utf-8")
        
