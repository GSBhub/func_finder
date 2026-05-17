"""
Integration tests — require radare2 with the r2-m7700 plugin installed.

Run with:  pytest -m integration
Skip with: pytest -m "not integration"
"""
import os
import pytest

pytestmark = pytest.mark.integration


@pytest.fixture
def rom_path():
    repo_root = os.path.dirname(os.path.dirname(__file__))
    path = os.path.join(repo_root, "742521-1994-USDM-SVX-EG33.bin")
    if not os.path.exists(path):
        pytest.skip(f"Test ROM not found: {path}")
    return path


def test_parse_rom_returns_nonempty_dict(rom_path):
    from func_finder import parse_rom
    result = parse_rom(rom_path)
    assert isinstance(result, dict)
    assert len(result) > 0, "Expected at least one function in the ROM"


def test_parse_rom_keys_are_hex_addresses(rom_path):
    from func_finder import parse_rom
    result = parse_rom(rom_path)
    for key in result:
        assert key.startswith("0x"), f"Key {key!r} is not a hex address"
        int(key, 16)  # must be parseable


def test_parse_rom_values_are_hash_lists(rom_path):
    from func_finder import parse_rom
    result = parse_rom(rom_path)
    for addr, hashes in result.items():
        assert isinstance(hashes, list), f"{addr}: expected list, got {type(hashes)}"
        for h in hashes:
            assert isinstance(h, str) and len(h) == 32, (
                f"{addr}: hash {h!r} is not a 32-char MD5 hex string"
            )


def test_parse_rom_contains_reset_vector_function(rom_path):
    from func_finder import parse_rom
    result = parse_rom(rom_path)
    # The reset vector for 742521 is 0x93c1 per the thesis data
    assert "0x93c1" in result, (
        f"Expected reset-vector function 0x93c1 in results; got keys: {sorted(result)[:10]}"
    )
