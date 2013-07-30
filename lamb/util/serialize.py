#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os.path
import pickle

from lamb.model import W_Tag

def come_up(basename):
    # later
    # from os import stat
    # statres = stat(filename)

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

    filename = basename + '.lambc'
    f = file(filename, 'w')
    buf = []
    try:
        pickle.dump(W_Tag.tags, f)
    finally:
        f.close()
