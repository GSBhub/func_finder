"""Unit tests for cfg.py — no radare2 required."""
import hashlib
import pytest

from func_finder.cfg import CFG, Block, Function, Instruction


def test_instruction_parses_opcode_and_params():
    inst = Instruction(0x9300, "CMP al #0xf0")
    assert inst.opcode == "CMP"
    assert inst.params == ["al", "#0xf0"]
    assert inst.addr == 0x9300


def test_instruction_no_params():
    inst = Instruction(0x9308, "RTS")
    assert inst.opcode == "RTS"
    assert inst.params == []


def test_block_hash_is_deterministic():
    ops = [
        {"offset": 0x9300, "opcode": "CMP al #0xf0"},
        {"offset": 0x9302, "opcode": "RTS"},
    ]
    b1 = Block(0x9300, ops)
    b2 = Block(0x9300, ops)
    assert b1.opcode_hash() == b2.opcode_hash()


def test_block_hash_differs_for_different_opcodes():
    ops_a = [{"offset": 0x9300, "opcode": "CMP al #0xf0"}]
    ops_b = [{"offset": 0x9300, "opcode": "NOP"}]
    assert Block(0x9300, ops_a).opcode_hash() != Block(0x9300, ops_b).opcode_hash()


def test_block_hash_matches_manual_md5():
    ops = [
        {"offset": 0x9300, "opcode": "CMP al #0xf0"},
        {"offset": 0x9302, "opcode": "RTS"},
    ]
    block = Block(0x9300, ops)
    expected = hashlib.md5("CMPRTS".encode("utf-8")).hexdigest()
    assert block.opcode_hash() == expected


def test_cfg_empty_on_empty_input():
    cfg = CFG([])
    assert cfg.first is None


def test_cfg_empty_on_missing_blocks():
    cfg = CFG([{"offset": 0x9300}])
    assert cfg.first is None


def test_cfg_builds_from_minimal_agj(minimal_agj):
    cfg = CFG(minimal_agj)
    assert cfg.first is not None
    assert cfg.first.addr == 0x9300
    assert len(cfg.first.instructions) == 3


def test_cfg_wires_jump_and_fail_edges(minimal_agj):
    cfg = CFG(minimal_agj)
    first = cfg.first
    assert first.jump is not None
    assert first.fail is not None
    assert first.jump.addr == 0x930C
    assert first.fail.addr == 0x9308


def test_cfg_terminal_blocks_have_no_edges(minimal_agj):
    cfg = CFG(minimal_agj)
    terminal_fail = cfg.first.fail
    terminal_jump = cfg.first.jump
    assert terminal_fail.jump is None
    assert terminal_fail.fail is None
    assert terminal_jump.jump is None
    assert terminal_jump.fail is None


def test_function_push_child():
    cfg_a = CFG([])
    cfg_b = CFG([])
    parent = Function(0x9300, cfg_a)
    child = Function(0x93c1, cfg_b)
    parent.push_child(child)
    assert 0x93c1 in parent.children
    assert parent.children[0x93c1] is child
