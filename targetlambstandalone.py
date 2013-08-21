#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys
import time

from rpython.rlib import jit
from rpython.rlib.debug import debug_start, debug_stop, debug_print

# from rpython.config.config import OptionDescription, BoolOption, StrOption
# from rpython.config.config import Config, to_optparse

import mu.functions
from lamb.startup import boot
from lamb.stack import ExecutionStackElement, OperandStackElement
from lamb.execution import jitdriver
from lamb.shape import CompoundShape

default_config = {
    "Nums": 1000,
    "Verbose": False,
    "Print": True,
    "Stats": False,
    "ReadStatefile": True,
    "WriteStatefile": True,
}

# ___________ Helper ________________

def print_statistics(config, timings, fun):
    shapes, transf = stats(config)
    total, cpu = timings
    print "Stats{"
    print "B:%s:" % fun
    print "C:shapes:", shapes
    print "C:transformationrules:", transf
    print "N:iterations:", config["Nums"]
    print "Ts:total:", total
    print "Ts:cpu:", cpu
    print "}Stats"

def stats(config):
    num_transf = 0
    num_shapes = 0
    for shape in CompoundShape._shapes:
        assert isinstance(shape, CompoundShape)
        num_shapes += 1
        num_transf += len(shape.transformation_rules)
    return num_shapes, num_transf

def print_ops(ops):
    from mu.functions import format

    print "Args"
    for op in ops:
        print format(op)
    print "---"


def print_help(argv, config):
    print """Lamb
Usage: %s [options] fun op ...

Options:
  General:
    -h --help        print this help and exit
  Printing:
    -v --verbose     turn on verbose output (is %s)
    -S --statistics  print statistics (is %s)
    -E               don't print the result expression (is %s)
  Running:
    -N num           number of repetitions (is %d)
  Altering Behavior:
       --jit arg     pass arg to the JIT, may be 'default', 'off', or 'param=value,param=value' list
    -n               ignore nils in substitution (is %s)
    -s num           set substitution threshold to num (is %d)
    -w num           set maximal storage with to consider for substitution to num (is %d)

    -R               don't read .lambc statefile (is %s read)
    -W               don't write .lambc statefile (is %s read)

Operations:
    fun              function to run, one of %s
    op ...           operand(s) to fun
""" % (
    argv[0],
    ('on' if config["Verbose"] else 'off'),
    ('on' if config["Stats"] else 'off'),
    ('on' if config["Print"] else 'off'),
    config["Nums"],
    ('on' if CompoundShape._config.ignore_nils else 'off'),
    CompoundShape._config.substitution_threshold,
    CompoundShape._config.max_storage_width,
    ('do' if config["ReadStatefile"] else 'do not'),
    ('do' if config["WriteStatefile"] else 'do not'),
    fun_list_string(),
)

def fun_list_string():
    from mu.functions import all_functions
    funs = all_functions.items()
    docs = ["%s/%d\t\t%s" % (key, val.arity(), val.doc) for key, val in funs]
    return "\n\t\t" + "\n\t\t".join(docs)


@jit.elidable
def lookup_fun(fun):
    from mu.functions import all_functions
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
    fun_name = None
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
            jit.set_user_param(jitdriver(), jitarg)
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
        elif argv[i] == "-R":
            config["ReadStatefile"] = False
        elif argv[i] == "-W":
            config["WriteStatefile"] = False
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
            fun_name = argv[i]
            if len(argv) > i:
                ops = argv[i+1:]
            break
        i += 1

    return (fun_name, ops, ret, config)

def do_come_up(fun):
    from lamb.util.serialize import come_up
    come_up(fun)

def do_settle(fun):
    from lamb.util.serialize import settle
    settle(fun)

def retrieve_fun_args(fun_name, argv):
    ret = 0
    ops = []
    fun = None

    try:
        fun = lookup_fun(fun_name)
        if fun is None:
            print "I don't know this func:", fun_name
            ret = 5
            return (fun, ret, ops)

        if len(argv) < fun.arity():
            print "too few arguments for fun"
            fun = None
            ret = 3
            return (fun, ret, ops)

        for i, fun_arg in enumerate(argv):
            arg = fun.parse_arg(i, fun_arg)
            ops.append(arg)
            ops.reverse()

    except ValueError, e:
        print "something's wrong with the fun: ",
        print e
        ret = 4
        fun = None

    return (fun, ret, ops)


# __________  Entry points  __________

def entry_point(argv, debug=False, debug_callback=None):

    (fun_name, fun_ops, ret, conf) = parse_options(argv, default_config)
    config = conf

    if config["ReadStatefile"] and fun_name is not None:
        do_come_up(fun_name)

    boot()

    if fun_name is None:
        print_help(argv, config)
        return ret # quit early.

    (fun, ret, ops) = retrieve_fun_args(fun_name, fun_ops)

    if fun is None:
        print_help(argv, config)
        return ret # quit early.

    if config["Verbose"] and config["Print"]:
        print_ops(ops)

    (result, timing) = run(config, fun, ops, debug, debug_callback)

    if config["WriteStatefile"]:
        do_settle(fun_name)

    if config["Print"]:
        print fun.format_ret(result)
    if config["Verbose"]:
        for shape in CompoundShape._shapes:
            print shape.merge_point_string()
            shape.print_hist()
            shape.print_transforms()
    if config["Verbose"] or config["Stats"]:
        print_statistics(config, timing, fun.lamb._name)
    return 0

def entry_point_normal(argv):
    return entry_point(argv, False, None)

def entry_point_n(argv):
    CompoundShape._config._inhibit_all= True
    return entry_point(argv)


def entry_point_i(argv):
    from mu.lists import _setup_shapes as lists_setup
    from mu.peano import _setup_shapes as peano_setup
    CompoundShape._config._inhibit_recognition = True
    lists_setup()
    peano_setup()

    return entry_point(argv)

def entry_point_t(argv):
    from lamb.util.transformation import \
        record_predicates, print_transformations
    ret = entry_point(argv, True, record_predicates)
    print_transformations()
    return ret


def run(config, fun, ops, debug=False, debug_callback=None):

    from lamb.util.construction_helper import interpret, nil

    start_time = time.time()
    start_cpu = time.clock()
    #
    # Main run stuff.
    #
    result = nil()
    for _ in range(config["Nums"]):
        stack_w = None
        for op in ops:
            stack_w = OperandStackElement(op, stack_w)
        stack_e = ExecutionStackElement(fun.lamb._cursor, None)

        result = interpret(stack_e, stack_w, debug, debug_callback)
    #
    #
    #
    stop_cpu = time.clock()
    stop_time = time.time()

    timing = (stop_time - start_time, stop_cpu - start_cpu)

    return (result, timing)


# _____ Define and setup target ___


def target(driver, args):
    if "--inhibit-recognition" in args:
        args.remove("--inhibit-recognition")
        driver.exe_name = 'lambi-%(backend)s'
        return entry_point_i, None
    elif "--inhibit-all" in args:
        args.remove("--inhibit-all")
        driver.exe_name = 'lambn-%(backend)s'
        return entry_point_n, None
    elif "--record-transformations" in args:
        args.remove("--record-transformations")
        from lamb import execution
        execution.use_jitdriver_with_tracing = True
        driver.exe_name = 'lambt-%(backend)s'
        return entry_point_t, None
    else:
        driver.exe_name = 'lamb-%(backend)s'
        return entry_point_normal, None


def jitpolicy(driver):
    from rpython.jit.codewriter.policy import JitPolicy
    return JitPolicy()


if __name__ == '__main__':
    from rpython.translator.driver import TranslationDriver
    f, _ = target(TranslationDriver(), sys.argv)
    sys.exit(f(sys.argv))
