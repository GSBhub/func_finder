"""
Data structures for M7700 control-flow graphs.

Instruction → Block → CFG → Function mirrors the hierarchy in the original
func_finder.py, but stores addresses as int throughout and hashes lazily.
"""
from __future__ import annotations

import hashlib
from collections import OrderedDict


class Instruction:
    def __init__(self, addr: int, opcode: str) -> None:
        self.addr = addr
        parts = opcode.split()
        self.opcode = parts[0]
        self.params = parts[1:]

    def __str__(self) -> str:
        if self.params:
            return f"OP: {self.opcode}\nParams: {self.params}\n"
        return f"OP: {self.opcode}\n"


class Block:
    def __init__(self, addr: int, ops_json: list) -> None:
        self.addr = addr
        self.fail: Block | None = None
        self.jump: Block | None = None
        self.instructions: OrderedDict[int, Instruction] = OrderedDict()
        for op in ops_json:
            self.instructions[op["offset"]] = Instruction(op["offset"], op["opcode"])

    def opcode_hash(self) -> str:
        opcodes = "".join(inst.opcode for inst in self.instructions.values())
        return hashlib.md5(opcodes.encode("utf-8")).hexdigest()

    def opcode_seq(self) -> str:
        return "".join(inst.opcode for inst in self.instructions.values())

    def __str__(self) -> str:
        ret = f"Block @ 0x{self.addr:04x}\n"
        if self.fail:
            ret += f"\tFail -> 0x{self.fail.addr:04x}\n"
        if self.jump:
            ret += f"\tJump -> 0x{self.jump.addr:04x}\n"
        return ret


class CFG:
    """Control-flow graph for a single function, built from radare2 agj output."""

    def __init__(self, agj: list) -> None:
        self.addr: int = 0
        self.first: Block | None = None

        if not agj:
            return
        entry = agj[0]
        if "offset" not in entry or "blocks" not in entry:
            return

        self.addr = entry["offset"]
        raw_blocks: list = entry["blocks"]

        block_map: dict[int, Block] = {}
        for blk in raw_blocks:
            block_map[blk["offset"]] = Block(blk["offset"], blk.get("ops", []))

        for blk in raw_blocks:
            obj = block_map[blk["offset"]]
            fail_addr = blk.get("fail")
            jump_addr = blk.get("jump")
            if fail_addr is not None and fail_addr in block_map:
                obj.fail = block_map[fail_addr]
            if jump_addr is not None and jump_addr in block_map:
                obj.jump = block_map[jump_addr]

        self.first = block_map[raw_blocks[0]["offset"]]


class Function:
    def __init__(self, addr: int, cfg: CFG) -> None:
        self.addr = addr
        self.cfg = cfg
        self.children: dict[int, Function] = {}
        self.parents: dict[int, Function] = {}

    def push_child(self, func: Function) -> None:
        self.children[func.addr] = func

    def __str__(self) -> str:
        ret = f"0x{self.addr:04x}\n"
        for child in self.children.values():
            ret += f"\t{child}"
        return ret
