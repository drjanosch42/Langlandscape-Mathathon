# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-B0: the free_block_z export (code/python/langlandscape/hacs_bridge/brandt_export.py) against plan/hacs/freeblockz-export-format.md (v2)."""

import importlib.util
import json
import pathlib
import subprocess
import sys

import pytest

REPO = pathlib.Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location("brandt_export", REPO / "code" / "python" / "langlandscape" / "hacs_bridge" / "brandt_export.py")
be = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(be)

OUT = REPO / "code" / "results" / "s06" / "brandt_free_block_z"
REQUIRED = ("schema", "status", "D", "M", "k", "n", "N", "rank", "ops", "F", "F_fnv", "proof", "basis_rule", "convention",
            "lattice", "tag")


def test_fnv_matches_hacs_printed_hash():
    # code/hacs/src/hacs/Console/scripts/061_s25_module_z_exact.expected l. 5-6 (level 1, n = 10, T_2)
    F = [[-24, 0, 68040], [0, -24, 0], [0, 0, 2049]]
    assert be.matrix_text(F) == "-24,0,68040;0,-24,0;0,0,2049"
    assert be.f_fnv(F) == "0xb69e2fb38c33b922"
    assert be.f_fnv([]) == "0xcbf29ce484222325"          # MatrixFnv({}, 0): the rank-0 hash


def test_fnv_hacs_expected_file_still_says_so():
    exp = (REPO / "code/hacs/src/hacs/Console/scripts/061_s25_module_z_exact.expected").read_text().splitlines()
    assert 'T_2: F = [["-24", "0", "68040"], ["0", "-24", "0"], ["0", "0", "2049"]]' in exp[4]
    assert "F_fnv 0xb69e2fb38c33b922" in exp[5]


def test_b11_k2_spec_example():
    r = be.k2_record(11, 1, [2, 3, 5])
    assert all(f in r for f in REQUIRED)
    assert r["rank"] == 2 and r["N"] == 11 and r["n"] == 0 and r["gammas"] == [4, 6]
    assert r["F"] == [[["1", "2"], ["3", "0"]], [["2", "2"], ["3", "1"]], [["4", "2"], ["3", "3"]]]
    assert r["F_fnv"] == ["0x12097637b2c137e0", "0xfee36f1e9928151a", "0x825d45ddc0a53cba"]
    assert r["charpoly_Z"] == [["-6", "-1", "1"], ["-4", "-3", "1"], ["6", "-7", "1"]]
    assert r["d_algebra"] == 2 and r["e_eis"] == 1 and r["bits_F"] == [2, 2, 3]
    chk = be.check_record(r)
    assert chk["fnv"] and chk["commute"] and chk["row_sums"] and chk["symmetry"] and chk["charpoly"]


def test_column_convention_constant_function_is_eisenstein():
    r = be.k2_record(11, 1, [2, 3])
    for F, p in zip(r["F"], r["ops"]):
        A = [[int(x) for x in row] for row in F]
        assert [sum(row) for row in A] == [p + 1] * len(A)        # F (1,..,1)^T = (p+1)(1,..,1)^T


def test_symn_k4_integral_lattice():
    r = be.symn_record(11, 4, [2, 3, 5])
    assert r["status"] == "ok" and r["rank"] == 2
    chk = be.check_record(r)
    assert chk["fnv"] and chk["commute"] and chk["charpoly"]
    grid = json.loads((REPO / "code/results/s01/symn.json").read_text())["data"]["grid"]
    assert be.symn_charpoly_check(r, grid)


def test_odd_k_rank0():
    r = be.symn_record(5, 5, [2, 3])
    assert r["status"] == "rank0" and r["rank"] == 0 and r["F_fnv"] == ["0xcbf29ce484222325"] * 2
    assert r["proof"] == ["rank0", "rank0"]


@pytest.mark.skipif(not (OUT / "index.json").exists(), reason="records not exported yet")
def test_exported_records():
    idx = json.loads((OUT / "index.json").read_text())["data"]
    assert idx["schema"] == "langlandscape_brandt/v2" and idx["writer"].startswith("python:brandt_export@")
    total = 0
    for c in idx["cells"]:
        path = OUT / c["file"]
        total += path.stat().st_size
        d = json.loads(path.read_text())["data"]
        r = d["free_block_z"]
        assert d["schema"] == "langlandscape_brandt/v2" and "writer" in d and r["schema"] == "langlandscape_brandt/v2"
        assert all(f in r for f in REQUIRED)
        chk = be.check_record(r)
        assert all(v is not False for v in chk.values()), (c["file"], chk)
        if r["status"] == "ok" and r["k"] == 2:
            assert chk["row_sums"] and chk["symmetry"]
            assert r["basis_rule"].startswith("brandt_k2_canonical/v2") and "canonical" not in r
            assert r["gammas"] == sorted(r["gammas"]) and "order_ties" in r
        if r["k"] > 2:
            assert r["canonical"] is False
        assert d["checks"].get("symn_charpoly") is not False
    assert total < 10 * 2 ** 20


def test_canonical_order_ties():
    from langlandscape import brandt
    assert be.canonical_order(brandt.module(37))[1] == [[0, 1]]
    assert be.canonical_order(brandt.module(43))[1] == [[0, 1]]
    assert be.canonical_order(brandt.module(41))[1] == []


_PROBE = """
import importlib.util, json, sys
sp = importlib.util.spec_from_file_location("be", sys.argv[1]); be = importlib.util.module_from_spec(sp); sp.loader.exec_module(be)
from langlandscape import brandt
for D in json.loads(sys.argv[2]):
    brandt.module(D)
out = {}
for D, k in json.loads(sys.argv[3]):
    r = be.symn_record(D, k) if k > 2 else be.k2_record(D, 1, be.primes_below(30, D))
    out[f"{D},{k}"] = [r["F_fnv"], r["gammas"]]
print(json.dumps(out))
"""
_CELLS = [[17, 2], [37, 2], [41, 2]]


def _probe(warm, cells):
    res = subprocess.run([sys.executable, "-c", _PROBE, str(REPO / "code/python/langlandscape/hacs_bridge/brandt_export.py"),
                          json.dumps(warm), json.dumps(cells)], cwd=REPO / "code" / "python", capture_output=True, text=True,
                         check=True)
    return json.loads(res.stdout.strip().splitlines()[-1])


def test_class_order_is_process_independent():
    """MAJ-1: the same F_fnv in two fresh processes and in one warmed up on other D (D = 2..13 flips brandt.py's BFS order)."""
    a = _probe([], _CELLS)
    b = _probe([], _CELLS)
    c = _probe([2, 3, 5, 7, 11, 13, 19, 23], _CELLS)
    assert a == b == c
    assert a["17,2"][1] == [2, 6]
