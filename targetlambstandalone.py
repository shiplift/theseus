#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys

from rpython.rlib import jit
from rpython.config.config import OptionDescription, BoolOption, StrOption
from rpython.config.config import Config, to_optparse

from lamb.util.construction_helper import interpret, w_nil
from lamb.stack import ExecutionStackElement, OperandStackElement
from lamb.execution import jitdriver


from lamb.shape import CompoundShape

from mu.functions import all_functions, format

default_config = {
    "Nums": 1000,
    "Verbose": False,
    "Print": True,
}

def shape_representation(shape):
    return shape.merge_point_string()

def print_transforms_for_rpython(shape):
    num = 0
    for (index, src), dest in shape.known_transformations.items():
        num += 1
        print num, "\t(", index, ", ", shape_representation(src), \
          u") -> ", shape_representation(dest)

# ___________ Helper ________________

def print_help(argv, config):
    print """Lamb
Usage: %s [-h|--help] [--jit arg] [-v|--verbose] [-np] [-s num] [-w num] [-n num] fun op ...

    -h --help        print this help and exit
       --jit arg     pass arg to the JIT, may be 'default', 'off', or 'param=value,param=value' list
    -v --verbose     turn on verbose output (is %s)
    -np              don't print the result expression (is %s)
    -s num           set substitution threshold to num (is %d)
    -w num           set maximal storage with to consider for substitution to num (is %d)
    -n num           number of repetitions (is %d)
    fun              function to run, one of %s
    op ...           operand(s) to fun
""" % (
    argv[0],
    ('on' if config["Verbose"] else 'off'),
    ('on' if config["Print"] else 'off'),
    CompoundShape._config.substitution_threshold,
    CompoundShape._config.max_storage_width,
    config["Nums"],
    fun_list_string())

def fun_list_string():
    funs = all_functions.items()
    docs = ["%s/%d\t\t%s" % (key, val.arity(), val.doc) for key, val in funs]
    return "\n\t\t" + "\n\t\t".join(docs)


def lookup_fun(fun):
    return all_functions.get(fun, None)

# TBD
# cmdline_optiondescr = OptionDescription("lamb", "the options of lamb", [
#     BoolOption("verbose", "turn on verbose output",
#                default=False, cmdline="-v --verbose"),
#     IntOption("substitiution",
#               "set substitution threshold to num",
#               default=17, cmdline="-s"),
#     IntOption("width",
#               "set maximal storage with to consider for substitution to num",
#               default=7, cmdline="-w"),
#     IntOption("repetitions",
#               "number of repetitionsset substitution threshold to num",
#                default=1000, cmdline="-s"),
#     StrOption("jit",
#               "pass arg to the JIT, may be 'default', 'off', or 'param=value,param=value' list",
#               default=None, cmdline="--jit"),
#     ])



def parse_options(argv, config):
    fun = None
    ops = []
    ret = -1
    i = 1
    to = len(argv)
    while (i < to):
        if argv[i] == "--jit":
            if len(argv) == i + 1:
                print "missing argument after --jit"
                ret = 2
                break
            jitarg = argv[i + 1]
            jit.set_user_param(jitdriver, jitarg)
            i += 1
        elif argv[i] in ["-h", "--help"]:
            # printing done by caller
            ret = 0
            break
        elif argv[i] in ["-v", "--verbose"]:
            config["Verbose"] = True
            config["Print"] = True
        elif argv[i] == "-np":
            config["Print"] = False
        elif argv[i] == "-s":
            if len(argv) == i + 1:
                print "missing argument after -s"
                ret = 2
                break
            CompoundShape._config.substitution_threshold = int(argv[i + 1])
            i += 1
        elif argv[i] == "-w":
            if len(argv) == i + 1:
                print "missing argument after -w"
                ret = 2
                break
            CompoundShape._config.max_storage_width = int(argv[i + 1])
            i += 1
        elif argv[i] == "-n":
            if len(argv) == i + 1:
                print "missing argument after -n"
                ret = 2
                break
            config["Nums"] = int(argv[i + 1])
            i += 1
        else:
            try:
                fun = lookup_fun(argv[i])
                i += 1
                k = i
                if (to - k) < fun.arity():
                    print "too few arguments for fun"
                    fun = None
                    ret = 3
                    break
                while (i < to):
                    arg = fun.parse_arg(i - k, argv[i])
                    ops.append(arg)
                    i += 1
                break
            except ValueError, e:
                print "something's wrong with the fun: ",
                print e
                ret = 4
                fun = None
                break
        i += 1

    return (fun, ops, ret, config)




# __________  Entry point  __________



def entry_point(argv):

    (fun, ops, ret, conf) = parse_options(argv, default_config)
    config  = conf

    if fun is None:
        print_help(argv, config)
        return ret # quit early.

    if config["Verbose"]:
        print "Args"
        for op in ops:
            print format(op)
        print "---"

    result = w_nil
    for _ in range(config["Nums"]):
        stack_w = None
        for op in ops:
            stack_w = OperandStackElement(op, stack_w)
        stack_e = ExecutionStackElement(fun.lamb._cursor, None)

        result = interpret(stack_e, stack_w)

    if config["Print"]:
        print fun.format_ret(result)
    if config["Verbose"]:
        print_transforms_for_rpython(result.get_tag().default_shape)
    return 0

# _____ Define and setup target ___


def target(driver, args):
    driver.exe_name = 'lamb-%(backend)s'
    return entry_point, None


def jitpolicy(driver):
    from rpython.jit.codewriter.policy import JitPolicy
    return JitPolicy()


if __name__ == '__main__':
    sys.exit(entry_point(sys.argv))
