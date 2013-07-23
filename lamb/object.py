#!/usr/bin/python
# -*- coding: utf-8 -*-


from rpython.tool.pairtype import extendabletype

from lamb.util.testing import TestHelperMixin
from lamb.util.view import DebugVizualizationMixin

class Object(TestHelperMixin, DebugVizualizationMixin):
    _mixin_ = True
    _attrs_ = []
    __metaclass__ = extendabletype
