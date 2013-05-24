#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys
import time

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
    "Stats": False,
}

# ___________ Helper ________________

def print_statistics(config, timings):
    shapes, transf = stats(config)
    total, cpu = timings
    print "Stats{"
    print "N:shapes:", shapes
    print "N:transformationrules:", transf
    print "N:iterations:", config["Nums"]
    print "Ts:total:", total
    print "Ts:cpu:", cpu
    print "}Stats"

def stats(config):
    num_transf = 0
    num_shapes = 0
    for shape in CompoundShape._shapes:
        num_shapes += 1
        num_transf += len(shape.known_transformations)
    return num_shapes, num_transf

def print_help(argv, config):
    print """Lamb
Usage: %(lamb)s [options] fun op ...

Options:
  General:
    -h --help        print this help and exit
  Printing:
    -v --verbose     turn on verbose output (is %(verbose)s)
    -S --statistics  print statistics (is %(stats)s)
    -E               don't print the result expression (is %(print)s)
  Running:
    -N num           number of repetitions (is %(nums)d)
  Altering Behavior:
       --jit arg     pass arg to the JIT, may be 'default', 'off', or 'param=value,param=value' list
    -n               ignore nils in substitution (is %(nils)s)
    -s num           set substitution threshold to num (is %(subst)d)
    -w num           set maximal storage with to consider for substitution to num (is %(width)d)

Operations:
    fun              function to run, one of %(funs)s
    op ...           operand(s) to fun
""" % {
    "lamb": argv[0],
    "verbose": ('on' if config["Verbose"] else 'off'),
    "stats": ('on' if config["Stats"] else 'off'),
    "print": ('on' if config["Print"] else 'off'),
    "subst": CompoundShape._config.substitution_threshold,
    "width": CompoundShape._config.max_storage_width,
    "nils": ('on' if CompoundShape._config.ignore_nils else 'off'),
    "nums": config["Nums"],
    "funs": fun_list_string(),
}

def fun_list_string():
    funs = all_functions.items()
    docs = ["%s/%d\t\t%s" % (key, val.arity(), val.doc) for key, val in funs]
    return "\n\t\t" + "\n\t\t".join(docs)


@jit.elidable
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
            i += 1
            jitarg = argv[i]
            jit.set_user_param(jitdriver, jitarg)
        elif argv[i] in ["-h", "--help"]:
            # printing done by caller
            ret = 0
            break
        elif argv[i] in ["-v", "--verbose"]:
            config["Verbose"] = True
            config["Print"] = True
            config["Stats"] = True
            CompoundShape._config.log_transformations = True
        elif argv[i] in ["-S", "--statistics"]:
            config["Stats"] = True
        elif argv[i] == "-E":
            config["Print"] = False
        elif argv[i] == "-s":
            if len(argv) == i + 1:
                print "missing argument after -s"
                ret = 2
                break
            i += 1
            CompoundShape._config.substitution_threshold = int(argv[i])
        elif argv[i] == "-w":
            if len(argv) == i + 1:
                print "missing argument after -w"
                ret = 2
                break
            i += 1
            CompoundShape._config.max_storage_width = int(argv[i])
        elif argv[i] == "-n":
            CompoundShape._config.ignore_nils = True
        elif argv[i] == "-N":
            if len(argv) == i + 1:
                print "missing argument after -N"
                ret = 2
                break
            i += 1
            n = int(argv[i])
            config["Nums"] = n if n > 0 else 1
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

    if config["Verbose"] and config["Print"]:
        print "Args"
        for op in ops:
            print format(op)
        print "---"


    start_time = time.time()
    start_cpu = time.clock()
    #
    # Main run stuff.
    #
    result = w_nil
    for _ in range(config["Nums"]):
        stack_w = None
        for op in ops:
            stack_w = OperandStackElement(op, stack_w)
        stack_e = ExecutionStackElement(fun.lamb._cursor, None)

        result = interpret(stack_e, stack_w)
    #
    #
    #
    stop_cpu = time.clock()
    stop_time = time.time()
    timing = (stop_time - start_time, stop_cpu - start_cpu)

    if config["Print"]:
        print fun.format_ret(result)
    if config["Verbose"]:
        for shape in CompoundShape._shapes:
            print shape.merge_point_string()
            shape.print_hist()
            shape.print_transforms()
    if config["Verbose"] or config["Stats"]:
        print_statistics(config, timing)
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
