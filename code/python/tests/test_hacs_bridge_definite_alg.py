# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-A2 tests: pure-Python local invariants on hand-made algebras; integration (skipped without HACS) on B_11, l = 5."""

from fractions import Fraction

import pytest

from langlandscape.hacs_bridge import HacsNotFound, definite_alg as da, find_hacs


def _have_hacs():
    try:
        find_hacs()
        return True
    except HacsNotFound:
        return False


needs_hacs = pytest.mark.skipif(not _have_hacs(), reason="HACS binary not available")


def _m(l, rows):
    return da._nm(rows, l)


def test_dual_numbers_local_nonetale_gorenstein():
    x = _m(5, [[0, 0], [1, 0]])  # F_5[x]/(x^2), regular representation
    inv = da.local_invariants([x], 5)
    assert inv["dim"] == 2 and inv["local"] and inv["residue_degree"] == 1
    assert inv["dim_radical"] == 1 and inv["nilpotency_index"] == 2
    assert inv["dim_socle"] == 1 and inv["gorenstein"] and inv["dim_tangent"] == 1


def test_two_variable_square_zero_not_gorenstein():
    u = _m(5, [[0, 0, 0], [1, 0, 0], [0, 0, 0]])  # F_5[u,v]/(u,v)^2 on <1,u,v>
    v = _m(5, [[0, 0, 0], [0, 0, 0], [1, 0, 0]])
    inv = da.local_invariants([u, v], 5)
    assert inv["local"] and inv["dim"] == 3 and inv["dim_radical"] == 2
    assert inv["dim_socle"] == 2 and not inv["gorenstein"] and inv["dim_tangent"] == 2


def test_truncated_polynomial_loewy():
    x = _m(7, [[0, 0, 0], [1, 0, 0], [0, 1, 0]])  # F_7[x]/(x^3)
    inv = da.local_invariants([x], 7)
    assert inv["nilpotency_index"] == 3 and inv["radical_power_dims"] == [2, 1] and inv["gorenstein"]


def test_field_extension_is_etale_residue_degree_two():
    a = _m(7, [[0, 6], [1, 0]])  # F_49 = F_7[x]/(x^2+1)
    inv = da.local_invariants([a], 7)
    assert inv["local"] and inv["dim_radical"] == 0 and inv["residue_degree"] == 2 and inv["gorenstein"]


def test_galois_conjugate_trap_two_components_and_split():
    l = 7
    a = _m(l, [[0, 6, 0, 0], [1, 0, 0, 0], [0, 0, 0, 6], [0, 0, 1, 0]])
    b = _m(l, [[0, 6, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 6, 0]])
    inv = da.local_invariants([a, b], l)
    assert inv["components"] == 2 and not inv["local"]
    blocks = da.split_local([a, b], l)
    assert len(blocks) == 2 and all(da.local_invariants(B, l)["local"] for B in blocks)


def test_split_mixed_product():
    # F_5[x]/(x^2)  x  F_5  (block diagonal): two maximal ideals, one non-etale
    l = 5
    x = _m(l, [[0, 0, 0], [1, 0, 0], [0, 0, 2]])
    blocks = da.split_local([x], l)
    invs = sorted((da.local_invariants(B, l) for B in blocks), key=lambda i: i["dim"])
    assert [i["dim"] for i in invs] == [1, 2] and [i["dim_radical"] for i in invs] == [0, 1]


def test_z_algebra_brandt_b11():
    # B_11 weight 2, T_2 = [[1, 2], [3, 0]]: Z[T_2] has Z-rank 2, index-5 inside Z x Z
    T = [[Fraction(1), Fraction(2)], [Fraction(3), Fraction(0)]]
    basis = da.z_algebra([T])
    assert len(basis) == 2
    C = da.regular_rep(basis, [T])[0]
    # T/5 is F_5[x]/(x-?)^2: local, non-etale
    l = 5
    inv = da.local_invariants([_m(l, C)], l)
    assert inv["local"] and inv["dim_radical"] == 1


def test_legendre_kind():
    assert da._legendre_kind(-11, 11) == "ramified"
    assert da._legendre_kind(-3, 2) == "inert"
    assert da._legendre_kind(-1, 5) == "split"


@needs_hacs
def test_b11_k2_l5_eisenstein_non_etale():
    rec = da.run_cell(11, 2, 5)
    assert rec["python_hacs_agree"] and rec["rank_T"] == 2 and rec["n_max_ideals"] == 1
    b = rec["blocks"][0]
    assert b["eisenstein"] and not b["etale"] and b["gorenstein"] and b["dim"] == 2
    assert rec["eisenstein_non_etale"] and rec["stable_under_extra_primes"]
    assert rec["generation"]["method"] == "saturation" and rec["generation"]["certified_equal"]
    assert rec["free_block_z"]["see"].endswith("D11_M1_k2.json") and "anemic" in rec["algebra"]


@needs_hacs
def test_b3_k12_l17_negative_control():
    rec = da.run_cell(3, 12, 17)
    assert rec["python_hacs_agree"] and not rec["has_non_etale"]
