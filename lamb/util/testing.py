#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Testing helper
#

from lamb.util.view import DebugVizualizationMixin
#
# Helper for equality testing in tests
#
class HelperMixin(DebugVizualizationMixin):
    _mixin_ = True
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        r = self.to_repr(set())
        return r if isinstance(r, str) else r.encode("utf-8")
        