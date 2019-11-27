#!/usr/bin/python
# -*- coding: utf-8 -*-


from rpython.tool.pairtype import extendabletype

from theseus.util.testing import TestHelperMixin
from theseus.util.view import DebugVizualizationMixin

class Object(TestHelperMixin, DebugVizualizationMixin):
    _attrs_ = []
    __metaclass__ = extendabletype
