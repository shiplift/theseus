#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys
import time

from rpython.rlib import jit
from rpython.rlib.debug import debug_start, debug_stop, debug_print

# from rpython.config.config import OptionDescription, BoolOption, StrOption
# from rpython.config.config import Config, to_optparse


from rpython.rlib.objectmodel import we_are_translated


take_options = True

from lamb.startup import boot
from lamb.stack import op_push, ex_push
from lamb.execution import jitdriver, toplevel_bindings
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

def print_statistics(timings, fun):
    shapes, transf = stats()
    total, cpu = timings
    print "Stats{"
    print "B:%s:" % fun
    print "RESULT-shapes:", shapes
    print "RESULT-transformationrules:", transf
    print "RESULT-total:", total
    print "RESULT-cpu:", cpu
    print "}Stats"

def stats():
    num_transf = 0
    num_shapes = 0
    for shape in CompoundShape._shapes:
        assert isinstance(shape, CompoundShape)
        num_shapes += 1
        num_transf += len(shape.transformation_rules)
    return num_shapes, num_transf


def print_help(argv, config):
    print """Lamb
Usage: %s [options] file

Options:
  General:
    -h --help        print this help and exit
  Printing:
    -v --verbose     turn on verbose output (is %s)
    -S --statistics  print statistics (is %s)
    -E               don't print the result expression (is %s print)
  Altering Behavior:
       --jit arg     pass arg to the JIT, may be 'default', 'off', or 'param=value,param=value' list
    -n               ignore nils in substitution (is %s)
    -s num           set substitution threshold to num (is %d)
    -w num           set maximal storage with to consider for substitution to num (is %d)

    -R               don't read .lambc statefile (is %s read)
    -W               don't write .lambc statefile (is %s write)

Operations:
    file             file to run
""" % (
    argv[0],
    ('on' if config["Verbose"] else 'off'),
    ('on' if config["Stats"] else 'off'),
    ('do' if config["Print"] else 'do not'),
    ('on' if CompoundShape._config.ignore_nils else 'off'),
    CompoundShape._config.substitution_threshold,
    CompoundShape._config.max_storage_width,
    ('do' if config["ReadStatefile"] else 'do not'),
    ('do' if config["WriteStatefile"] else 'do not'),
)



def parse_options(argv, config):
    filename = None
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
        else:
            filename = argv[i]
            assert not len(argv) - 1 > i
            break
        i += 1

    return (filename, ret, config)

def do_come_up(f):
    from lamb.util.serialize import come_up
    come_up(f)

def do_settle(f):
    from lamb.util.serialize import settle
    settle(f)

# __________  Entry points  __________

def entry_point(argv, debug=False):

    (filename, ret, conf) = parse_options(argv, default_config)
    config = conf

    if config["ReadStatefile"] and filename is not None:
        do_come_up(filename)

    boot()

    if filename is None:
        print_help(argv, config)
        return ret # quit early.

    (result, timing) = run(config, filename, debug)

    if config["WriteStatefile"]:
        do_settle(filename)

    if config["Print"]:
        print result
    if config["Verbose"]:
        for shape in CompoundShape._shapes:
            print shape.merge_point_string()
            shape.print_hist()
            shape.print_transforms()
    if config["Verbose"] or config["Stats"]:
        print_statistics(timing, filename)
    return 0

def entry_point_normal(argv):
    return entry_point(argv, False)

def entry_point_d(argv):
    return entry_point(argv, True)

def entry_point_n(argv):
    CompoundShape._config._inhibit_all= True
    return entry_point(argv)


def entry_point_i(argv):
    CompoundShape._config._inhibit_recognition = True
    return entry_point(argv)

def entry_point_t(argv):
    from lamb.util.transformation import print_transformations
    ret = entry_point(argv, True)
    print_transformations()
    return ret


def run(config, filename, debug=False):

    from lamb.util.construction_helper import interpret, nil
    from lamb.parser import parse_file
    from lamb.execution import toplevel_bindings

    expressions, bindings = parse_file(filename)
    toplevel_bindings.set_bindings(bindings)

    start_time = time.time()
    start_cpu = time.clock()
    #
    # Main run stuff.
    #
    stack_w = op_push(None, nil())
    stack_e = None
    for exp in reversed(expressions):
        stack_e = ex_push(stack_e, exp)

    result = interpret(stack_e, stack_w, debug)
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
        driver.exe_name = 'lambi'
        ep = entry_point_i
    elif "--inhibit-all" in args:
        args.remove("--inhibit-all")
        driver.exe_name = 'lambn'
        ep = entry_point_n
    elif "--record-transformations" in args:
        args.remove("--record-transformations")
        from lamb.util.transformation import record_predicates
        from lamb import execution
        execution._debug_callback = record_predicates
        driver.exe_name = 'lambt'
        ep = entry_point_t
    elif "--debug-lamb" in args:
        args.remove("--debug-lamb")
        if we_are_translated():
            assert False, "only for hosted debugging"
        from lamb import execution
        from lamb.util.debug import debug_stack
        execution._debug_callback = debug_stack
        ep = entry_point_d
    else:
        driver.exe_name = 'lamb'
        ep = entry_point_normal
    if driver.exe_name is not None:
        driver.exe_name = 'bin/' + driver.exe_name
    return ep, None


def jitpolicy(driver):
    from rpython.jit.codewriter.policy import JitPolicy
    return JitPolicy()


if __name__ == '__main__':
    assert not we_are_translated()
    import lamb.util.debug
    from rpython.translator.driver import TranslationDriver
    f, _ = target(TranslationDriver(), sys.argv)
    try:
        sys.exit(f(sys.argv))
    except SystemExit:
        pass
    except:
        import pdb, traceback
        _type, value, tb = sys.exc_info()
        traceback.print_exception(_type, value, tb)
        pdb.post_mortem(tb)
