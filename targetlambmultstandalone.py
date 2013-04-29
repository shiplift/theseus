#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys

from lamb.util.construction_helper import run
from mu.peano import mult, peano_num, python_num

# __________  Entry point  __________


def entry_point(argv):
    argno = len(argv)
    if argno == 3:
        arg1 = peano_num(int(argv[1]))
        arg2 = peano_num(int(argv[2]))
        res = run(mult, [arg1, arg2])
        print python_num(res)
        return 0
    else:
        return 1

# _____ Define and setup target ___


def target(driver, args):
    driver.exe_name = 'lambmult-%(backend)s'
    return entry_point, None


def jitpolicy(driver):
    from rpython.jit.codewriter.policy import JitPolicy
    return JitPolicy()


if __name__ == '__main__':
    entry_point(sys.argv)
