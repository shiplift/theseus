#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys
import time

from rpython.rlib import jit

from lamb.util.construction_helper import interpret, conslist, integer
from lamb.stack import ExecutionStackElement, OperandStackElement
from lamb.execution import jitdriver
from lamb.shape import CompoundShape

from mu.functions import all_functions

reverse = all_functions["reverse"]


def entry_point(argv):

#    sys.setrecursionlimit(sys.getrecursionlimit() * 10)
    clist1_w = reverse.parse_arg(0, "10000000;i:1")
    stack_w = OperandStackElement(clist1_w, None)
    stack_e = ExecutionStackElement(reverse.lamb._cursor, None)

    result = interpret(stack_e, stack_w)

#    print reverse.format_ret(result)
    print "OK"
    return 0


# _____ Define and setup target ___


def target(driver, args):
    driver.exe_name = 'minireverse-%(backend)s'
    return entry_point, None


def jitpolicy(driver):
    from rpython.jit.codewriter.policy import JitPolicy
    return JitPolicy()


if __name__ == '__main__':
    sys.exit(entry_point(sys.argv))
