#!/usr/bin/python
# -*- coding: utf-8 -*-

from theseus.util.repr import urepr
from rpython.rlib import objectmodel
#
# Graphviz
#
@objectmodel.not_rpython
def _dot(self, seen):
    if self in seen:
        return
    seen.add(self)
    yield u'%s [label="%s", shape=box]' % (id(self), urepr(self)[:50])

    ignored = ['_tag', '_lamb']

    for key, value in self.__dict__.iteritems():
        if key in ignored: # ignore certain properies
            continue
        if hasattr(value, "_dot"):
            yield u"%s -> %s [label=%s]" % (id(self), id(value), key)
            for line in value._dot(seen):
                yield line

def graph(objects, names):
    content = [u"digraph G{"] # ,u"rankdir=LR;"]
    seen = set()
    for obj in list(objects):
        content.extend(obj._dot(seen))

    for k in sorted(names.keys()):
        obj = names[k]
        if isinstance(obj, list) or isinstance(obj, dict):
            content.append("%s" % k)

    for k in sorted(names.keys()):
        obj = names[k]
        if isinstance(obj, dict):
            obj = obj.values()

        if isinstance(obj, list):
            for subobj in obj:
                content.extend(subobj._dot(seen))
        else:
            content.extend(obj._dot(seen))

    for key in sorted(names.keys()):
        obj = names[key]
        if isinstance(obj, list):
            for i in range(len(obj)):
                content.append(u"%s -> %s [label=%02d]" % (key, id(obj[i]), i))
        elif isinstance(obj, dict):
            for subkey, subobj in obj.items():
                content.append(u"%s -> %s [label=%s]" % (key, id(subobj)), subkey)
        else:
            content.append(u"%s -> %s" % (key, id(obj)))
    content.append(u"}")
    return content

def view(*objects, **names):
    from dotviewer import graphclient
    import py
    p = py.path.local().mkdtemp().join("lamb").join("temp.dot")
    p.write(u"\n".join(graph(objects, names)).encode('utf-8'), 'wb')
    graphclient.display_dot_file(p, save_tmp_file='/tmp/foo/out.dot')


#
# Helper for viewing items on the stack
#
class DebugVizualizationMixin(object):
    _mixin_ = True
    _dot = _dot
