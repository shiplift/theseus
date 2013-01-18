#!/usr/bin/python
# -*- coding: utf-8 -*-

#
# Debug helper
#
def who(object):
    """ concise id """
    return unicode(hex(id(object) % 0xFFFF)[2:])
def urepr(object):
    """ support for unicode repr. see uni() """
    return repr(object).decode("utf-8")
def uni(fun):
    """ support decorator for unicode repr. see urepr() """
    def fun2(*args): return fun(*args).encode("utf-8")
    return fun2
def debug_stack(d):
    """
    print dictionary of stacks.
    """
    print
    print "%: Cursor, !: Expression, μ: Call, #: Value, λ: Lambda, &: Pattern, {}: Rule, _ Variable"
    from itertools import izip_longest 
    def i_(o):
        try: [ e for e in o ]
        except TypeError: return [o]
        else: return o
    def t_(o):
        length = 52; return o[:length] if len(o) > length else o
    
    k = d.keys()
    v = map(list, map(list, map(i_, d.values())))
    stacks = map(lambda x: map(lambda y: u"[%-52s]" % y, map(t_, map(lambda y: urepr(y) if y else u"", x))), map(list, map(reversed, zip(*list(izip_longest(*v, fillvalue=""))))))
    tops = map(lambda x: [u"%-55s" % x], k)
    stat = map(lambda x: x[0] + x[1], list(zip(tops,stacks)))
    lines = map(lambda x: u" ".join(x), map(list, zip(*stat)))
    print u"\n".join(lines)


#
# Helper for equality testing in tests
#
class TestEqualityMixin(object):
    _mixin_ = True
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self == other

#
# Graphviz
#
def _dot(self, seen):
    if self in seen:
        return
    seen.add(self)
    yield '%s [label="%s", shape=box]' % (id(self), repr(self)[:50])
    for key, value in self.__dict__.iteritems():
        if hasattr(value, "_dot"):
            yield "%s -> %s [label=%s]" % (id(self), id(value), key)
            for line in value._dot(seen):
                yield line

def view(*objects, **names):
    from dotviewer import graphclient
    content = ["digraph G{"]
    seen = set()
    for obj in list(objects) + names.values():
        content.extend(obj._dot(seen))
    for key, value in names.items():
        content.append("%s -> %s" % (key, id(value)))
    content.append("}")
    p = py.test.ensuretemp("prolog").join("temp.dot")
    p.write("\n".join(content))
    graphclient.display_dot_file(str(p))
