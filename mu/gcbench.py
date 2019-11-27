#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
This is adapted from a benchmark written by John Ellis and Pete Kovac
of Post Communications.
It was modified by Hans Boehm of Silicon Graphics.
Adapted to theseus by Tobias Pape

    This is no substitute for real applications.  No actual application
    is likely to behave in exactly this way.  However, this benchmark was
    designed to be more representative of real applications than other
    Java GC benchmarks of which we are aware.
    It attempts to model those properties of allocation requests that
    are important to current GC techniques.
    It is designed to be used either to obtain a single overall performance
    number, or to give a more detailed estimate of how collector
    performance varies with object lifetimes.  It prints the time
    required to allocate and collect balanced binary trees of various
    sizes.  Smaller trees result in shorter object lifetimes.  Each cycle
    allocates roughly the same amount of memory.
    Two data structures are kept around during the entire process, so
    that the measured performance is representative of applications
    that maintain some live in-memory data.  One of these is a tree
    containing many pointers.  The other is a large array containing
    double precision floating point numbers.  Both should be of comparable
    size.

    The results are only really meaningful together with a specification
    of how much memory was used.  It is possible to trade memory for
    better time performance.  This benchmark should be run in a 32 MB
    heap, though we don't currently know how to enforce that uniformly.

    Unlike the original Ellis and Kovac benchmark, we do not attempt
    measure pause times.  This facility should eventually be added back
    in.  There are several reasons for omitting it for now.  The original
    implementation depended on assumptions about the thread scheduler
    that don't hold uniformly.  The results really measure both the
    scheduler and GC.  Pause time measurements tend to not fit well with
    current benchmark suites.  As far as we know, none of the current
    commercial Java implementations seriously attempt to minimize GC pause
    times.

    Known deficiencies:
            - No way to check on memory use
            - No cyclic data structures
            - No attempt to measure variation with object size
            - Results are sensitive to locking cost, but we dont
              check for proper locking
"""

import time
from theseus.expression import Variable
from theseus.startup import startup

from theseus.model import tag
from theseus.shape import CompoundShape, in_storage_shape
from theseus.util.construction_helper import (pattern as p, expression as e,
                                           lamb, mu, cons, integer,
                                           plist, conslist, rules,
                                           nil)

java = """
class Node {
        Node left, right;
        int i, j;
        Node(Node l, Node r) { left = l; right = r; }
        Node() { }
}

public class GCBench {

        public static final int kStretchTreeDepth    = 18;      // about 16Mb
        public static final int kLongLivedTreeDepth  = 16;  // about 4Mb
        public static final int kArraySize  = 500000;  // about 4Mb
        public static final int kMinTreeDepth = 4;
        public static final int kMaxTreeDepth = 16;

        // Nodes used by a tree of a given size
        static int TreeSize(int i) {
                return ((1 << (i + 1)) - 1);
        }

        // Number of iterations to use for a given tree depth
        static int NumIters(int i) {
                return 2 * TreeSize(kStretchTreeDepth) / TreeSize(i);
        }

        // Build tree top down, assigning to older objects. 
        static void Populate(int iDepth, Node thisNode) {
                if (iDepth<=0) {
                        return;
                } else {
                        iDepth--;
                        thisNode.left  = new Node();
                        thisNode.right = new Node();
                        Populate (iDepth, thisNode.left);
                        Populate (iDepth, thisNode.right);
                }
        }

        // Build tree bottom-up
        static Node MakeTree(int iDepth) {
                if (iDepth<=0) {
                        return new Node();
                } else {
                        return new Node(MakeTree(iDepth-1),
                                        MakeTree(iDepth-1));
                }
        }

        static void PrintDiagnostics() {
                long lFreeMemory = Runtime.getRuntime().freeMemory();
                long lTotalMemory = Runtime.getRuntime().totalMemory();

                System.out.print(" Total memory available="
                                 + lTotalMemory + " bytes");
                System.out.println("  Free memory=" + lFreeMemory + " bytes");
        }

        static void TimeConstruction(int depth) {
                Node    root;
                long    tStart, tFinish;
                int     iNumIters = NumIters(depth);
                Node    tempTree;

                System.out.println("Creating " + iNumIters +
                                   " trees of depth " + depth);
                tStart = System.currentTimeMillis();
                for (int i = 0; i < iNumIters; ++i) {
                        tempTree = new Node();
                        Populate(depth, tempTree);
                        tempTree = null;
                }
                tFinish = System.currentTimeMillis();
                System.out.println("\tTop down construction took "
                                   + (tFinish - tStart) + "msecs");
                tStart = System.currentTimeMillis();
                for (int i = 0; i < iNumIters; ++i) {
                        tempTree = MakeTree(depth);
                        tempTree = null;
                }
                tFinish = System.currentTimeMillis();
                System.out.println("\tBottom up construction took "
                                   + (tFinish - tStart) + "msecs");
                
        }

        public static void main(String args[]) {
                Node    root;
                Node    longLivedTree;
                Node    tempTree;
                long    tStart, tFinish;
                long    tElapsed;


                System.out.println("Garbage Collector Test");
                System.out.println(
                        " Stretching memory with a binary tree of depth "
                        + kStretchTreeDepth);
                PrintDiagnostics();
                tStart = System.currentTimeMillis();

                // Stretch the memory space quickly
                tempTree = MakeTree(kStretchTreeDepth);
                tempTree = null;

                // Create a long lived object
                System.out.println(
                        " Creating a long-lived binary tree of depth " +
                        kLongLivedTreeDepth);
                longLivedTree = new Node();
                Populate(kLongLivedTreeDepth, longLivedTree);

                // Create long-lived array, filling half of it
                System.out.println(
                        " Creating a long-lived array of "
                        + kArraySize + " doubles");
                double array[] = new double[kArraySize];
                for (int i = 0; i < kArraySize/2; ++i) {
                        array[i] = 1.0/i;
                }
                PrintDiagnostics();

                for (int d = kMinTreeDepth; d <= kMaxTreeDepth; d += 2) {
                        TimeConstruction(d);
                }

                if (longLivedTree == null || array[1000] != 1.0/1000)
                        System.out.println("Failed");
                                        // fake reference to LongLivedTree
                                        // and array
                                        // to keep them from being optimized away

                tFinish = System.currentTimeMillis();
                tElapsed = tFinish-tStart;
                PrintDiagnostics();
                System.out.println("Completed in " + tElapsed + "ms.");
        }
} // class JavaGC
"""

#
# Pseudo-primitives
#
def prim_currentmilliseconds(w_args):
    assert len(w_args) == 0
    return integer(int(time.clock()*1000))

def make_prim_currentmilliseconds():
    from theseus.model import W_Primitive
    return W_Primitive(prim_currentmilliseconds, 0, "currentmilliseconds")

def prim_minus(w_args):
    from theseus.model import W_Integer
    assert len(w_args) == 2
    w_arg0 = w_args[0]
    assert isinstance(w_arg0, W_Integer)
    w_arg1 = w_args[1]
    assert isinstance(w_arg1, W_Integer)

    return integer(w_arg0.value() - w_arg1.value())

def make_prim_minus():
    from theseus.model import W_Primitive
    return W_Primitive(prim_minus, 2, "minus")

def prim_print_int(w_args):
    from theseus.model import W_Integer
    assert len(w_args) == 1
    w_arg0 = w_args[0]
    assert isinstance(w_arg0, W_Integer)

    print w_arg0.value()

    return nil()

def make_prim_print_int():
    from theseus.model import W_Primitive
    return W_Primitive(prim_print_int, 1, "print_int")

# def prim_display(w_args):
#     from theseus.model import W_String
#     assert len(w_args) == 1
#     w_arg0 = w_args[0]
#     assert isinstance(w_arg0, W_String)


def make_gc_bench():
    w_tStart_v0 = Variable("tStart")
    w_tStart_v1 = Variable("tStart")
    w_tStart_v2 = Variable("tStart")
    w_tFinish_v0 = Variable("tFinish")
    w_root_v0 = Variable("root")
    w_root_v1 = Variable("root")
    w_kStretchTreeDepth_v0 = Variable("kStretchTreeDepth")
    w_iDepth_v0 = Variable("iDepth")

    w_Make_Tree = lamb()
    w_Make_Tree._name = "MakeTree"
    w_Make_Tree._rules = rules([
        ([p(integer(0)) ], e(cons("Node", nil(), nil()))),
        ([p(w_iDepth_v0)], e(cons("Node",
                mu(w_Make_Tree, [mu(_minus(), [w_iDepth_v0, integer(1)])]),
                mu(w_Make_Tree, [mu(_minus(), [w_iDepth_v0, integer(1)])]))))
        ])

    w_gc_bench_cont1 = lamb()
    w_gc_bench_cont1._name = "gc_bench$cont0"
    w_gc_bench_cont1._rules = rules([
        ([p(w_tStart_v2),
          p(w_tFinish_v0),
          p(w_root_v1)], # we 'un-reference'

        e(mu(_print_int(), [mu(_minus(), [w_tFinish_v0, w_tStart_v2])])))])

    w_gc_bench_cont0 = lamb()
    w_gc_bench_cont0._name = "gc_bench$cont0"
    w_gc_bench_cont0._rules = rules([
        ([p(w_tStart_v1),
          p(w_root_v0)],

         e(mu(w_gc_bench_cont1, [
             w_tStart_v1,
             mu(_currentmilliseconds(), []),
             w_root_v0,
             ])))])

    w_gc_bench_let0 = lamb()
    w_gc_bench_let0._name = "gc_bench$let0"
    w_gc_bench_let0._rules = rules([
        ([p(w_kStretchTreeDepth_v0),
          p(w_tStart_v0)],

         e(mu(w_gc_bench_cont0, [
             w_tStart_v0,
             mu(w_Make_Tree, [w_kStretchTreeDepth_v0])
         ])))])

    w_gc_bench = lamb()
    w_gc_bench._name = "gc_bench"
    w_gc_bench._rules = rules([
        ([], e(mu(w_gc_bench_let0, [
            integer(18),    # kStretchTreeDepth
            mu(_currentmilliseconds(), []), # tStart
            ])))])
    return w_gc_bench

# g = {'functions':{}}
# functions = g['functions']
functions = {}
@startup
def startup_gc_bench():
    if len(functions) != 0:
        return
    #prims
    functions['currentmilliseconds'] = make_prim_currentmilliseconds()
    functions['minus'] = make_prim_minus()
    functions['print_int'] = make_prim_print_int()

    functions['gc_bench'] = make_gc_bench()

def _gc_bench():            return functions.get('gc_bench', None)
def _currentmilliseconds(): return functions.get('currentmilliseconds', None)
def _minus():               return functions.get('minus', None)
def _print_int():           return functions.get('print_int', None)
