#!/usr/bin/env python
# -*- coding: utf-8 -*-

from lamb.object import Object

from lamb.util.repr import urepr, uni

class StackElement(Object):

    _attrs_ = ['_data', '_next']

    def __init__(self, data=None, next=None):
        self._data = data
        self._next = next

    def pop(self):
        return (self._data, self._next)

class ExecutionStackElement(StackElement):
    def push(self, val):
        return ExecutionStackElement(val, self)

def ex_push(es, val):
    return es.push(val) if es else ExecutionStackElement(val)

class OperandStackElement(StackElement):
    def push(self, val):
        return OperandStackElement(val, self)

def op_push(op, val):
    return op.push(val) if op else OperandStackElement(val)

class Stack(Object):
    def __init__(self, ex, op):
        self.execution_stack = ex
        self.operand_stack = op
