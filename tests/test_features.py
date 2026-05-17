"""Unit tests for features.py — no radare2 required."""
import pytest

from func_finder.cfg import CFG, Function
from func_finder.features import get_signature, grab_features


def test_get_signature_empty_cfg():
    cfg = CFG([])
    assert get_signature(cfg.first, []) == []


def test_get_signature_single_block(minimal_agj):
    # Isolate just the first block by temporarily cutting edges
    cfg = CFG(minimal_agj)
    first = cfg.first
    saved_jump, saved_fail = first.jump, first.fail
    first.jump = None
    first.fail = None

    sig = get_signature(first, [])
    assert len(sig) == 1
    assert sig[0] == first.opcode_hash()

    first.jump = saved_jump
    first.fail = saved_fail


def test_get_signature_visits_both_edges(minimal_agj):
    cfg = CFG(minimal_agj)
    sig = get_signature(cfg.first, [])
    # 3 blocks → 3 hashes (DFS: first, jump, fail)
    assert len(sig) == 3


def test_get_signature_no_duplicate_visits(minimal_agj):
    """A block reachable via multiple paths should only be hashed once."""
    from func_finder.cfg import Block

    # Diamond: A -> B -> D, A -> C -> D
    ops = lambda label: [{"offset": 0, "opcode": label}]
    a = Block(0x100, ops("NOP"))
    b = Block(0x200, ops("CMP"))
    c = Block(0x300, ops("LDA"))
    d = Block(0x400, ops("RTS"))
    a.jump = b
    a.fail = c
    b.jump = d
    c.jump = d

    sig = get_signature(a, [])
    # 4 unique blocks
    assert len(sig) == 4
    # D's hash appears exactly once
    assert sig.count(d.opcode_hash()) == 1


def test_grab_features_key_format(minimal_agj):
    cfg = CFG(minimal_agj)
    func = Function(0x9300, cfg)
    result = grab_features(func, [])
    assert "0x9300" in result


def test_grab_features_value_is_list_of_strings(minimal_agj):
    cfg = CFG(minimal_agj)
    func = Function(0x9300, cfg)
    result = grab_features(func, [])
    hashes = result["0x9300"]
    assert isinstance(hashes, list)
    assert all(isinstance(h, str) and len(h) == 32 for h in hashes)


def test_grab_features_includes_children(minimal_agj):
    cfg = CFG(minimal_agj)
    parent = Function(0x9300, cfg)
    child_cfg = CFG([])
    child = Function(0x93C1, child_cfg)
    parent.push_child(child)

    result = grab_features(parent, [])
    assert "0x9300" in result
    assert "0x93c1" in result


def test_grab_features_no_duplicate_on_cycle(minimal_agj):
    """Mutually-calling functions should not recurse infinitely."""
    cfg_a = CFG(minimal_agj)
    cfg_b = CFG([])
    fa = Function(0x9300, cfg_a)
    fb = Function(0x93C1, cfg_b)
    fa.push_child(fb)
    fb.push_child(fa)  # cycle

    result = grab_features(fa, [])
    assert "0x9300" in result
    assert "0x93c1" in result


def test_grab_features_empty_cfg_gives_empty_list():
    cfg = CFG([])
    func = Function(0x9300, cfg)
    result = grab_features(func, [])
    assert result == {"0x9300": []}
