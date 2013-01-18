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
    from itertools import izip_longest 
    def i_(o):
        try: [ e for e in o ]
        except TypeError: return [o]
        else: return o
    def t_(o):
        length = 52; return o[:length] if len(o) > length else o
    
    k = d.keys()
    v = map(list, map(reversed, map(list, map(i_, d.values()))))
    stacks = map(lambda x: map(lambda y: u"[%-52s]" % y, map(t_, map(lambda y: urepr(y) if y else u"", x))), map(list, zip(*list(izip_longest(*v, fillvalue="")))))
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
