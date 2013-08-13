#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys

from lamb.util.construction_helper import (lamb, ziprules, nil, mu,
                                           interpret, integer)
from lamb.stack import ExecutionStackElement, OperandStackElement
from lamb.execution import Variable, W_LambdaCursor, tag, w_constructor


_cons_2 = tag("cons", 2)
def _cons(car, cdr):
    return w_constructor(_cons_2, [car, cdr])

def setup_reverse():
    a1 = Variable("accumulator")
    a2 = Variable("accumulator")
    h = Variable("head")
    t = Variable("tail")

    reverse_acc = lamb()
    reverse_acc._name ="reverse_acc"
    reverse_acc._rules = ziprules(
        ([nil(),       a1], a1),
        ([_cons(h, t), a2], mu(reverse_acc, t, _cons(h, a2))))

    l = Variable("l")
    reverse = lamb(([l], mu(reverse_acc, l, nil())))
    reverse._name = "reverse"
    return reverse

reverse = setup_reverse()

_nums = 100000


def shape_representation(shape):
    return shape.merge_point_string()

def print_transforms_for_rpython(shape):
    num = 0
    for (index, src), dest in shape.transformation_rules.items():
        num += 1
        print num, "\t(", index, ", ", shape_representation(src), \
          u") -> ", shape_representation(dest)


# __________  Entry point  __________


def entry_point(argv):
    from lamb.shape import CompoundShape

    argno = len(argv)
    nums = _nums
    if argno >= 2:
        nums = int(argv[1])
    if argno >= 3:
        CompoundShape._config.substitution_threshold = int(argv[2])
    if argno >= 4:
        CompoundShape._config.max_storage_width = int(argv[3])
    clist1_w = nil()
    for number in range(nums):
        clist1_w = _cons(integer(number), clist1_w)
    stack_w = OperandStackElement(clist1_w, None)
    stack_e = ExecutionStackElement(W_LambdaCursor(reverse), None)

    result = interpret(stack_e, stack_w)
    # print result
    print_transforms_for_rpython(clist1_w.get_tag().default_shape)
    return 0

# _____ Define and setup target ___


def target(driver, args):
    driver.exe_name = 'lambreverse-%(backend)s'
    return entry_point, None


def jitpolicy(driver):
    from rpython.jit.codewriter.policy import JitPolicy
    return JitPolicy()


if __name__ == '__main__':
    entry_point(sys.argv)
