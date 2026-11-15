"""Tests for the provenance helper and the shared PARI instance."""

import json
from fractions import Fraction

from langlandscape import results
from langlandscape.pari import get_pari


def test_results_roundtrip():
    relpath = "s01/_test_roundtrip.json"
    data = {"a": [1, 2, 3], "f": Fraction(1, 3), "s": {"y", "x"}}
    path = None
    try:
        path = results.write(
            relpath, data, script="test", params={"k": 1}, runtime_s=0.0, notes="roundtrip"
        )
        back = results.read(relpath)
        prov = back["provenance"]
        for key in ("script", "commit", "params", "date", "runtime_s", "python", "pari_version", "notes"):
            assert key in prov
        assert back["data"]["a"] == [1, 2, 3]
        assert back["data"]["f"] == "1/3"
        assert back["data"]["s"] == ["x", "y"]
        assert json.loads(path.read_text(encoding="utf-8")) == back
    finally:
        if path is not None and path.exists():
            path.unlink()


def test_get_pari():
    pari = get_pari()
    assert pari("2+2") == 4
