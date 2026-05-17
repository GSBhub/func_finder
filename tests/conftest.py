"""
Shared fixtures.  The minimal_agj fixture provides a two-block CFG that
exercises both the true-edge (jump) and false-edge (fail) paths without
needing a real binary or radare2 session.
"""
import pytest
from collections import OrderedDict


@pytest.fixture
def minimal_agj() -> list:
    """
    Two-block CFG for a hypothetical function at 0x9300:

        Block A (0x9300): CMP BNE LDA  -> jump=0x930C, fail=0x9308
        Block B (0x9308): STA RTS       (terminal)
        Block C (0x930C): NOP RTS       (terminal, jump target)
    """
    return [
        {
            "offset": 0x9300,
            "name": "fcn.00009300",
            "blocks": [
                {
                    "offset": 0x9300,
                    "ops": [
                        {"offset": 0x9300, "opcode": "CMP al #0xf0"},
                        {"offset": 0x9302, "opcode": "BNE 0x930c"},
                        {"offset": 0x9304, "opcode": "LDA #0x01"},
                    ],
                    "jump": 0x930C,
                    "fail": 0x9308,
                },
                {
                    "offset": 0x9308,
                    "ops": [
                        {"offset": 0x9308, "opcode": "STA 0x1234"},
                        {"offset": 0x930B, "opcode": "RTS"},
                    ],
                },
                {
                    "offset": 0x930C,
                    "ops": [
                        {"offset": 0x930C, "opcode": "NOP"},
                        {"offset": 0x930D, "opcode": "RTS"},
                    ],
                },
            ],
        }
    ]


@pytest.fixture
def binary_path(tmp_path) -> str:
    """Path to the test ROM bundled with the repo."""
    import os
    repo_root = os.path.dirname(os.path.dirname(__file__))
    return os.path.join(repo_root, "742521-1994-USDM-SVX-EG33.bin")
