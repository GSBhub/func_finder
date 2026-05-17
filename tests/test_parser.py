"""Unit tests for parser helpers — no radare2 required."""
import pytest

from func_finder.parser import get_children, _parse_afl, _build_cfg


def test_get_children_unrecognised_address():
    disasm = "0x9300  JSR 0x93c1"
    assert 0x93C1 in get_children(disasm)


def test_get_children_radare_named_function():
    disasm = "0x9300  JSR fcn.000093c1"
    assert 0x93C1 in get_children(disasm)


def test_get_children_no_jsr():
    disasm = "0x9300  CMP al #0xf0\n0x9302  BNE 0x930c"
    assert get_children(disasm) == []


def test_get_children_two_jsr_same_target():
    # Same target on two lines → appears twice (caller deduplicates via visited dict)
    disasm = "     JSR 0x93c1\n     JSR 0x93c1"
    children = get_children(disasm)
    assert children.count(0x93C1) == 2


def test_parse_afl_extracts_addresses():
    afl = (
        "0x00009300    1    16 sym.reset\n"
        "0x0000930d    2    39 fcn.0000930d\n"
        "0x00009380    1     8 fcn.00009380\n"
    )
    addrs = _parse_afl(afl)
    assert 0x9300 in addrs
    assert 0x930D in addrs
    assert 0x9380 in addrs


def test_parse_afl_skips_below_0x9000():
    # Addresses below ROM region should be ignored
    afl = "0x00001234    1    8 sym.low\n0x00009300    1   16 sym.reset\n"
    addrs = _parse_afl(afl)
    assert 0x1234 not in addrs
    assert 0x9300 in addrs


def test_parse_afl_skips_bad_lines():
    afl = "not a hex line\n0x00009300    1    16 sym.reset\n"
    addrs = _parse_afl(afl)
    assert addrs == [0x9300]


def test_build_cfg_bad_json_returns_empty_cfg():
    cfg = _build_cfg("not json {{{")
    assert cfg.first is None


def test_build_cfg_valid_json(minimal_agj):
    import json
    cfg = _build_cfg(json.dumps(minimal_agj))
    assert cfg.first is not None
    assert cfg.first.addr == 0x9300
