"""
Radare2-backed parser for M7700 binaries.

Replaces the global-state design of the original func_finder.py:
- `visited` is passed explicitly rather than living as a module-level dict
- all Python 2 string / md5 / print idioms are gone
"""
from __future__ import annotations

import json
import logging
import re
from collections import OrderedDict

import r2pipe

from .cfg import CFG, Function
from .features import grab_features

log = logging.getLogger(__name__)


def get_rst(r2) -> int:
    """Read the M7700 reset vector from 0xFFFE (little-endian 16-bit)."""
    r2.cmd("s 0xfffe")
    raw = str(r2.cmd("px0"))
    if raw and len(raw) >= 4:
        return int(f"{raw[2:4]}{raw[:2]}", 16)
    return 0


def get_start(infile: str) -> int:
    """Heuristic: find the first CMP instruction that marks the init routine."""
    try:
        r2 = r2pipe.open(infile, ["-2"])
        r2.cmd("e asm.arch=m7700")
        val = r2.cmd("/c CMP al #0xf0")
        if not val:
            val = r2.cmd("/c CMP ax #0xf0f0")
        parts = val.split()
        if parts:
            r2.cmd(f"s {parts[0]}")
        addr = int(r2.cmd("s"), 16)
        r2.quit()
        return addr
    except (IOError, ValueError):
        return 0


def get_children(disasm: str) -> list[int]:
    """Extract JSR targets from a radare2 pdf disassembly string."""
    # Unrecognised function addresses already formatted as 0xNNNN.
    # [^$\n] ensures we don't consume a newline and match an address from the
    # next line (the original [^$] check excludes indirect calls like "JSR $sym").
    hits: list[str] = re.findall(r"JSR.*[^$\n](0x[0-9a-fA-F]{4})", disasm)
    # Radare-named functions like fcn.00009300 → extract the 4-digit suffix
    hits += [
        f"0x{m}"
        for m in re.findall(r"JSR.*fcn\.0000([0-9a-fA-F]{4})", disasm)
    ]
    result: list[int] = []
    for h in hits:
        try:
            result.append(int(h, 16))
        except (TypeError, ValueError):
            log.debug("Could not parse child address: %r", h)
    return result


def _build_cfg(agj_str: str) -> CFG:
    try:
        data = json.loads(agj_str, object_pairs_hook=OrderedDict)
    except (json.JSONDecodeError, ValueError):
        data = []
    return CFG(data)


def recursive_parse_func(addr: int, r2, visited: dict[int, Function]) -> Function:
    """
    Recursively parse a function at `addr` and all functions it calls.
    Already-visited addresses are returned immediately to handle cycles.
    """
    r2.cmd(f"s 0x{addr:04x}")
    r2.cmd("aa")
    r2.cmd("sf.")
    addr = int(r2.cmd("s"), 16)

    if addr in visited:
        return visited[addr]

    cfg = _build_cfg(r2.cmd("agj"))
    func = Function(addr, cfg)
    visited[addr] = func

    children = get_children(r2.cmd("pdf"))
    for child_addr in children:
        if child_addr not in visited:
            visited[child_addr] = recursive_parse_func(child_addr, r2, visited)
        child = visited[child_addr]
        child.parents[addr] = func
        func.push_child(child)

    return func


def _parse_afl(afl_str: str) -> list[int]:
    """Parse `afl` output into a list of function entry addresses >= 0x9000."""
    result: list[int] = []
    for line in afl_str.splitlines():
        try:
            addr = int(line[:10], 16)
        except (TypeError, ValueError):
            continue
        if addr >= 0x9000:
            result.append(addr)
    return result


def linear_parse_func(func: Function | None, r2, visited: dict[int, Function]) -> list[Function]:
    """
    Supplement recursive parse by asking radare2 for all identified functions
    and recursing into any that were missed.
    """
    r2.cmd("aaa")
    addrs = _parse_afl(r2.cmd("afl"))
    result: list[Function] = []
    for addr in addrs:
        if addr not in visited:
            result.append(recursive_parse_func(addr, r2, visited))
    return result


def parse_rom(infile: str) -> dict[str, list[str]]:
    """
    Full pipeline: open binary in r2, extract all functions, return feature dict.

    Output format: ``{"0x9300": ["<md5>", "<md5>", ...], ...}``
    (one entry per function; each value is a list of per-block opcode hashes)
    """
    print(f"Loading '{infile}' into R2...")
    start = get_start(infile)

    r2 = r2pipe.open(infile, ["-2"])
    r2.cmd("e asm.arch=m7700")
    log.info("R2 arch: %s", r2.cmd("e asm.arch"))

    rst = get_rst(r2)
    log.info("Reset vector: 0x%04x", rst)
    if rst and rst < start:
        start = rst

    r2.cmd("e anal.limits=true")
    r2.cmd(f"e anal.from=0x{start:04x}")
    r2.cmd("e anal.to=0xffd0")

    visited: dict[int, Function] = {}
    func_list: list[Function] = []

    try:
        root = recursive_parse_func(rst, r2, visited)
        func_list.append(root)
    except ValueError as exc:
        log.warning("Recursive parse failed: %s", exc)

    try:
        func_list.extend(linear_parse_func(func_list[0] if func_list else None, r2, visited))
    except ValueError as exc:
        log.warning("Linear parse failed: %s", exc)

    features: dict[str, list[str]] = {}
    for f in func_list:
        features.update(grab_features(f, []))

    r2.quit()
    print(f"Done. Found {len(features)} functions.")
    return features
