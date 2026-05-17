"""
Feature extraction: walk a CFG and return an ordered list of block hashes
that form the function's signature.
"""
from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .cfg import Block, Function


def get_signature(block: "Block | None", visited: list) -> list[str]:
    """DFS over CFG blocks; return each block's opcode hash in traversal order."""
    if block is None or block in visited:
        return []
    visited.append(block)
    result = [block.opcode_hash()]
    if block.jump:
        result.extend(get_signature(block.jump, visited))
    if block.fail:
        result.extend(get_signature(block.fail, visited))
    return result


def grab_features(func: "Function", visited_funcs: list) -> dict[str, list[str]]:
    """Collect signatures for func and all of its children (recursively)."""
    if func in visited_funcs:
        return {}
    visited_funcs.append(func)
    result: dict[str, list[str]] = {
        f"0x{func.addr:04x}": get_signature(func.cfg.first, [])
    }
    for child in func.children.values():
        result.update(grab_features(child, visited_funcs))
    return result
