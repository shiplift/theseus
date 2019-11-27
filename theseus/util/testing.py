#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Helper for equality testing in tests
#
class TestHelperMixin(object):

    _mixin_ = True
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self == other

    def shape(self):
        # for non-W_Objects to act as such during pattern generation
        from theseus.shape import in_storage_shape
        return in_storage_shape
