#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Startup registry for lamb.
"""

from rpython.rlib import jit
from rpython.rlib.debug import debug_start, debug_stop, debug_print

from lamb.object import Object

class StartupRegistry(Object):

    def __init__ (self):
        self.triggers = []

    def add_trigger(self, trigger):
        self.triggers.append(trigger)

    @jit.unroll_safe
    def boot(self):
        for trigger in self.triggers:
            trigger()


the_startup_registry = StartupRegistry()

def boot():
    debug_start("lamb-startup")
    the_startup_registry.boot()
    debug_stop("lamb-startup")

def startup(fun):
    # debug_print("register %s for startup" % fun)
    the_startup_registry.add_trigger(fun)
    return fun