#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""

serialize

provide means to persist and recreate the currently known
set of W_Tags and all shapes and transformations reachable
from there.

The rmarshal modules is used for serialization; the format is

marshal_proto = (
    int, # number of shapes
    [ # shape list
        ( # a shape
            int, # id
            (str, int), # tag
            [int], # structure: list of id's
            { # _hist
                (int, int) : # index, id
                int # count
            },
            { # transformation_rules
                (int, int) : # index, id
                int # id
            }
        )
    ],
    {
        (str, int) : # name arity
        int #id
    }
)

The serialized tree is written to a '.lambc' files

"""
import os.path
import pickle

from lamb.model import W_Tag

def come_up(basename):
    # later
    # from os import stat
    # statres = stat(path)
    debug_start("lamb-come-up")

    filename = basename + '.lambc'
    if not os.path.exists(filename):
        return

    f = file(filename, 'rU')
    try:
        res = pickle.load(f)
    finally:
        f.close()
    W_Tag.tags = res

def settle(basename):
    """
    Settle Tags, shapes and transformations to a '.lambc' file
    punching and marshalling all current Tags.
    """
    debug_start("lamb-settle")

    filename = basename + '.lambc'
    f = file(filename, 'w')
    buf = []
    try:
        pickle.dump(W_Tag.tags, f)
    finally:
        f.close()
    debug_stop("lamb-settle")
