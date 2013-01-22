#!/usr/bin/python
# -*- coding: utf-8 -*-

#
# Debug helper
#
def who(object):
    """ concise id """
    return unicode(hex(id(object) % 0xFFFF)[2:])
def urepr(obj, seen=None):
    """ support for unicode repr. see uni() """
    if seen is None:
        seen = set()
    ret = obj.to_repr(seen) if hasattr(obj, 'to_repr') else repr(obj)
    return ret if isinstance(ret, unicode) else ret.decode("utf-8")

def uni(fun):
    """ support decorator for unicode repr. see urepr() """
    def fun2(obj, seen):
        if obj in seen:
            # assert False
            return u"…"
        else:
            seen.add(obj)
        return fun(obj, seen).encode("utf-8")
    return fun2
