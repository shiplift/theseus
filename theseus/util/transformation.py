#!/usr/bin/env python
# -*- coding: utf-8 -*-

from rpython.rlib import jit

from theseus.execution import (current_shapes,
                            ex_data_or_none, op_data_or_none,
                            W_LambdaCursor, W_ConstructorCursor,
                            )
from theseus.util.view import _dot, view
from theseus.util.repr import urepr, who, uni

glob = { 'predicates': [] }

def record_predicates(stack):

    ex_data = ex_data_or_none(stack.execution_stack)
    op_stack = stack.operand_stack
    cursor = ex_data
    tup = None
    if isinstance(cursor, W_LambdaCursor):
        shapes = current_shapes(cursor._lamb.arity(), op_stack)
        shapes_string = shapes.merge_point_string()
        tup = ("L", cursor._lamb._name, shapes_string)
        glob['predicates'].append( tup )
    elif isinstance(cursor, W_ConstructorCursor):
        shapes = current_shapes(cursor._tag.arity(), op_stack)
        shapes_string = shapes.merge_point_string()
        tup = ("C", cursor._tag.name, shapes_string)
        glob['predicates'].append( tup )
    else:
        return
#    print tup

def _number_of_digits(n):
    from math import log10, floor
    return int(1+floor(log10(n)))

def tuple_key(l, tup):
    assert tup in l
    return "_%d" % l.index(tup)

def tuple_node(l, tup):
    return tuple_key(l, tup) + " [" + \
        'label="%s",' % "".join(list(tup)) + \
        'shape="%s",' % ("octagon" if tup[0] == 'C' else "box") + \
        "];"

def tuple_subgraph(l, key):
    ret = 'subgraph cluster_%s { ' % key
    for t in l:
        typ, name, shape = t
        if t[0] == key:
            ret += "%s; " % tuple_key(l, t)
    ret += '};'
    return ret


def _cmp_edge(a, b):
    return cmp(a[0], b[0])

@jit.dont_look_inside
def print_transformations():
    from math import log, pow
    l = glob.get('predicates', [])

    max_width = 16

    print "digraph tuple_transformations {"
#    print 'rankdir="LR";'
    print "\tnode [shape=box];"
    print "\tedge [fontsize=16, labelfloat=true];"
    print "\tgraph [splines=true, concentrate=false];"
    tuples = []
    edges = {}
    for index in range(len(l)):
        tup = l[index]
        if tup not in tuples:
            tuples.append(tup)

        if index > 0:
            pre = l[index - 1]
            key = (pre, tup)
            edges[key] = edges.setdefault(key, 0) + 1

    for t in tuples:
        print tuple_node(tuples, t)

    # print tuple_subgraph(tuples, 'L')
    # print tuple_subgraph(tuples, 'C')

    max_v = 1
    if len(edges) > 0:
        for count in edges.values():
            max_v = max(count, max_v)

    max_value = float(max_v)
    steepness = pow(10, _number_of_digits(max_v) - 1)
    targetscale = (max_width - 1) / log(1 + steepness)

    for key, value in edges.items():
        pre, post = key
        assert value != 0
        norm_value = value / max_value
        #weight = 10/log10(1+10*float(value))
        #penwidth = pow(max_width, norm_value)
        penwidth = 1 + (targetscale * log(steepness * norm_value + 1))
        weight = int(1 + (log(value)/log(1.5))) # max_value - value + 1
        print "%s -> %s [" % (tuple_key(tuples, pre), tuple_key(tuples, post)),
        print "label=\"%d\"," % value ,
        print "penwidth=%f," % penwidth ,
        print "style=\"setlinewidth(%f)\"," % penwidth,
        print "weight=%d" % weight ,
        print "];"
    print "}"
