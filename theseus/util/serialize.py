#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""

serialize

provide means to persist and recreate the currently known
set of W_Tags and all shapes and transformations reachable
from there.

The rmarshal modules is used for serialization; the format is

marshal_proto = (
    int, # number of shapes
    [ # shape list
        ( # a shape
            int, # id
            (str, int), # tag
            [int], # structure: list of id's
            { # _hist
                (int, int) : # index, id
                int # count
            },
            { # transformation_rules
                (int, int) : # index, id
                int # id
            }
        )
    ],
    {
        (str, int) : # name arity
        int #id
    }
)

The serialized tree is written to a '.docked' files

"""
import os.path
from rpython.rlib.streamio import open_file_as_stream
from rpython.rlib.rmarshal import get_marshaller, get_unmarshaller
from rpython.rlib.debug import debug_start, debug_stop, debug_print

from theseus.model import W_Tag
from theseus.shape import in_storage_shape, CompoundShape

marshal_proto = (
    int, # number of shapes
    [ # shape list
        ( # a shape
            int, # id
            (str, int), # tag
            [int], # structure: list of id's
            { # _hist
                (int, int) : # index, id
                int # count
            },
            { # transformation_rules
                (int, int) : # index, id
                int # id
            }
        )
    ],
    {
        (str, int) : # name arity
        int #id
    }
)

marshaller = get_marshaller(marshal_proto)
unmarshaller = get_unmarshaller(marshal_proto)

def punch_shape(s, registry):
    """
    Punch a shape to a tuple for marshalling.
    See slurp_shapes, configure_shapes for inverse.
    Format is
        ( # a shape
            int, # id
            (str, int), # tag
            [int], # structure: list of id's
            { # _hist
                (int, int) : # index, id
                int # count
            },
            { # transformation_rules
                (int, int) : # index, id
                int # id
            }
        )
    """
    if s == in_storage_shape:
        return (0, ('', 0), [], {}, {})
    else:
        assert isinstance(s, CompoundShape)

    my_index = registry.index(s)

    hist = {}
    for (index, shape), count in s._hist.items():
        shape_id = registry.index(shape)
        hist[(index, shape_id)] = count
    trans = {}
    for (index, shape), to_shape in s.transformation_rules.items():
        shape_id = registry.index(shape)
        to_shape_id = registry.index(to_shape)
        trans[(index, registry.index(shape))] = registry.index(to_shape)

    punchee = (
        registry.index(s),
        (s._tag.name, s._tag.arity()),
        [registry.index(subshape) for subshape in s._structure],
        hist,
        trans
    )
    return punchee


def recreate_shape(shape_desc, tags, registry):
    """
    Recreate a shape from its punched format; see punch_shape.
    Does not handle history and transformations.
    See configure_shape(s).
    """
    id, tag, structure_ids = shape_desc

    structure = [None] * len(structure_ids)
    for structure_index, sub_id in enumerate(structure_ids):
        assert sub_id < id
        subshape = registry[sub_id]
        assert subshape is not None
        structure[structure_index] = subshape

    return CompoundShape(tags[tag], structure)


def configure_shape(shape, hist, trans, registry):
    """
    Reconfigure a shape from its punched format; see punch_shape.
    Does _only_ handle history and transformations.
    See configure_shapes.
    """
    assert isinstance(shape, CompoundShape)
    shape._hist = {}
    for (index, s_id), count in hist.items():
        k = (index, registry[s_id])
        shape._hist[k] = count
    shape.transformation_rules = {}
    for (index, s_id), to_s_id in trans.items():
        k = (index, registry[s_id])
        shape.transformation_rules[k] = registry[to_s_id]

def configure_shapes(shapes, registry):
    """
    Reconfigure all shapes.
    Does _only_ handle history and transformations.
    See configure_shapes.
    """
    for id, _tag, _structure_ids, hist, trans in shapes:
        if id == 0: continue # in_storage_shape, no configure
        configure_shape(registry[id], hist, trans, registry)


def slurp_registry(shapes, registry, tags_slurp, tags):
    """
    Slurp all shapes from their punched format (see punch_shape)
    not including history or transformation
    """
    known_ids = [0]

    for default_id in tags_slurp.values():
        known_ids.append(default_id)

    for id, tag, structure_ids, _hist, _trans in shapes:
        if id in known_ids: continue
        assert registry[id] is None
        registry[id] = recreate_shape((id, tag, structure_ids), tags, registry)

def punch_tags(tags):
    """
    Punch all tags into marshallable format:
    (
        int, # number of shapes
        [ # shape list
        ],
        {
            (str, int) : # name arity
            int #id
        }
    )
    """
    reg = [in_storage_shape] + CompoundShape._shapes
    punch_reg = [punch_shape(s, reg) for s in reg]
    res = {}
    for key, value in tags.items():
        res[key] = reg.index(value.default_shape)
    return (len(punch_reg), punch_reg, res)

def slurp_tags(un_tags):
    """
    Slurp all tags from their punched format (see punch_tag).
    Recursively slurps shapes and then configures them.
    """
    num_shapes, shapes_slurp, tags_slurp = un_tags

    registry = [None] * num_shapes
    registry[0] = in_storage_shape

    tags = {}
    for (name, arity), default_id in tags_slurp.items():
        tag = W_Tag(name, arity)
        tags[(name, arity)] = tag
        registry[default_id] = tag.default_shape

    slurp_registry(shapes_slurp, registry, tags_slurp, tags)
    configure_shapes(shapes_slurp, registry)
    return tags

def come_up(basename):
    """
    Bring up previously marshalled Tags, shapes and transformations
    from '.docked' file un-marshalling, slurping and replacement of
    current Tags.
    """
    from theseus.shape import CompoundShape
    # later
    # from os import stat
    # statres = stat(path)
    debug_start("theseus-come-up")

    path = basename + '.docked'
    if not os.path.exists(path):
        return
    try:
        f = open_file_as_stream(path, buffering=0)
    except OSError as e:
        os.write(2, "Error(come_up)%s -- %s\n" % (os.strerror(e.errno), path))
        return
    try:
        res = unmarshaller(f.readall())
    finally:
        f.close()
    del CompoundShape._shapes[:]
    W_Tag.tags.clear()
    new_tags = slurp_tags(res)
    for key, value in new_tags.items():
        W_Tag.tags[key] = value
    debug_stop("theseus-come-up")

def settle(basename):
    """
    Settle Tags, shapes and transformations to a '.docked' file
    punching and marshalling all current Tags.
    """
    debug_start("theseus-settle")

    path = basename + '.docked'
    buf = []
    marshaller(buf, punch_tags(W_Tag.tags))
    try:
        f = open_file_as_stream(path, mode="w", buffering=0)
    except OSError as e:
        os.write(2, "Error(settle)%s -- %s\n" % (os.strerror(e.errno), path))
        return
    try:
        f.write(''.join(buf))
    finally:
        f.close()
    debug_stop("theseus-settle")
