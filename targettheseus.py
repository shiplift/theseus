#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys
import time

from rpython.rlib import jit
from rpython.rlib.debug import debug_start, debug_stop, debug_print
from rpython.rlib.objectmodel import we_are_translated


take_options = True

from theseus.startup import boot
from theseus.execution import jitdriver, toplevel_bindings
from theseus.shape import CompoundShape

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
    print "B:%s:" % fun
    print "0:RESULT-shapes:num:", shapes
    print "0:RESULT-transformationrules:num:", transf
    print "0:RESULT-total:ms:", total
    print "0:RESULT-cpu:ms:", cpu

def stats():
    num_transf = 0
    num_shapes = 0
    for shape in CompoundShape._shapes:
        assert isinstance(shape, CompoundShape)
        num_shapes += 1
        num_transf += len(shape.transformation_rules)
    return num_shapes, num_transf


def print_help(argv, config):
    print """Theseus
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
    -s num           set substitution threshold to num (is %d)
    -w num           set maximal storage with to consider for substitution to num (is %d)
    -d num           set maximal shape depth to create to num (is %d)

    -R               don't read .docked statefile (is %s read)
    -W               don't write .docked statefile (is %s write)

Operations:
    file             file to run
""" % (
    argv[0],
    ('on' if config["Verbose"] else 'off'),
    ('on' if config["Stats"] else 'off'),
    ('do' if config["Print"] else 'do not'),
    CompoundShape._config.substitution_threshold,
    CompoundShape._config.max_storage_width,
    CompoundShape._config.max_shape_depth,
    ('do' if config["ReadStatefile"] else 'do not'),
    ('do' if config["WriteStatefile"] else 'do not'),
)



def parse_options(argv, config):
    filename = None
    args = []
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
            jit.set_user_param(None, jitarg)
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
            s_t = int(argv[i])
            if s_t <= 1:
                print "substitution threshold must be greater than 1"
                ret = 2
                break
            CompoundShape._config.substitution_threshold = s_t
        elif argv[i] == "-w":
            if len(argv) == i + 1:
                print "missing argument after -w"
                ret = 2
                break
            i += 1
            CompoundShape._config.max_storage_width = int(argv[i])
        elif argv[i] == "-d":
            if len(argv) == i + 1:
                print "missing argument after -d"
                ret = 2
                break
            i += 1
            CompoundShape._config.max_shape_depth = int(argv[i])
        else:
            filename = argv[i]
            if len(argv) > i:
                args = argv[i+1:]
            break
        i += 1

    return (filename, ret, args, config)

def convert_arguments(arguments):
    from theseus.util.construction_helper import conslist
    from theseus import model
    return conslist([model.w_string(arg) for arg in arguments])

def do_come_up(f):
    from theseus.util.serialize import come_up
    come_up(f)

def do_settle(f):
    from theseus.util.serialize import settle
    settle(f)

# __________  Entry points  __________

def entry_point(argv):
    if we_are_translated():
        from rpython.rlib import rstack
        rstack._stack_set_length_fraction(50.0)
    else:
        import sys
        sys.setrecursionlimit(100000)

    (filename, ret, args, conf) = parse_options(argv, default_config)
    config = conf

    if config["ReadStatefile"] and filename is not None:
        do_come_up(filename)

    boot()

    if filename is None:
        print_help(argv, config)
        return ret # quit early.

    (result, timing) = run(config, filename, args)

    if config["WriteStatefile"]:
        do_settle(filename)

    if config["Print"]:
        print result
    if config["Verbose"]:
        CompoundShape.print_verbose()
    if config["Verbose"] or config["Stats"]:
        print_statistics(timing, filename)
    return 0

def entry_point_normal(argv):
    return entry_point(argv)

def entry_point_n(argv):
    CompoundShape._config._inhibit_all= True
    return entry_point(argv)


def entry_point_i(argv):
    CompoundShape._config._inhibit_recognition = True
    return entry_point(argv)

def entry_point_t(argv):
    from theseus.util.transformation import print_transformations
    ret = entry_point(argv)
    print_transformations()
    return ret


def run(config, filename, args):

    from theseus.util.construction_helper import interpret_expression, nil
    from theseus.parser import parse_file
    from theseus.execution import toplevel_bindings

    w_argv = convert_arguments(args)
    expressions, bindings = parse_file(filename, w_argv)
    toplevel_bindings.set_bindings(bindings)

    start_time = time.time()
    start_cpu = time.clock()
    #
    # Main run stuff.
    #
    result = None
    for exp in expressions:
        result = interpret_expression(exp)
    #
    #
    #
    stop_cpu = time.clock()
    stop_time = time.time()

    timing = (stop_time - start_time, stop_cpu - start_cpu)

    return (result, timing)


# _____ Define and setup target ___


def target(driver, args):
    driver.config.translation.suggest(**{
        "jit": True,
        "jit_opencoder_model": "big",
    })
    driver.config.translation.set(gcrootfinder="shadowstack")

    exe_name = 'theseus'
    ep = entry_point_normal
    if "--inhibit-recognition" in args:
        args.remove("--inhibit-recognition")
        exe_name += 'i'
        ep = entry_point_i
    elif "--inhibit-all" in args:
        args.remove("--inhibit-all")
        exe_name += 'n'
        ep = entry_point_n
    elif "--record-transformations" in args:
        args.remove("--record-transformations")
        from theseus.util.transformation import record_predicates
        from theseus import execution
        execution._debug_callback = record_predicates
        exe_name += 't'
        ep = entry_point_t

    driver.exe_name = 'bin/' + exe_name
    return ep, None


def jitpolicy(driver):
    from rpython.jit.codewriter.policy import JitPolicy
    return JitPolicy()


if __name__ == '__main__':
    assert not we_are_translated()
    import theseus.util.debug
    from rpython.translator.driver import TranslationDriver
    f, _ = target(TranslationDriver(), sys.argv)
    try:
        sys.exit(f(sys.argv))
    except SystemExit:
        pass
    except:
        if hasattr(sys, 'ps1') or not sys.stderr.isatty():
            # we are in interactive mode or we don't have a tty-like
            # device, so we call the default hook
            sys.__excepthook__(type, value, tb)
        else:
            import pdb, traceback
            _type, value, tb = sys.exc_info()
            traceback.print_exception(_type, value, tb)
            pdb.post_mortem(tb)
