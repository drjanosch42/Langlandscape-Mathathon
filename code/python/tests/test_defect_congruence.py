# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C1 tests: Hecke-algebra toolkit, congruence ideals, Gorenstein test, Thm E (stage-06 ``ss:s06-ca``)."""

import numpy as np
import pytest

from langlandscape import results
from langlandscape.defect.congruence import (Character, defect, eta, example_level3_weight12, image_ideal, ord_at,
                                             place_info, toy_l10a, toy_non_gorenstein, toy_ramified)
from langlandscape.defect.hecke_alg import (HeckeAlgebra, ZOrder, find_maximal_ideal, gorenstein_test,
                                            local_length, maximal_ideals, mf_integral_hecke, mf_qnew_qold)


@pytest.mark.parametrize("p", [3, 5, 7])
@pytest.mark.parametrize("t", [1, 2, 3])
def test_l10a_toy(p, t):
    """Toy of L10a: S = {(x,y) : x = y mod p^t}: eta = c = p^t (exactly, as ideals of Z), eta_new = 1."""
    T, chi, m = toy_l10a(p, t)
    b = T.kernel_of_rep("old")
    assert eta(chi).basis == [[p ** t]]
    assert image_ideal(chi, b).basis == [[p ** t]]
    r = defect(T, chi, m)
    assert r["ord"] == {"eta": t, "c": t, "eta_new": 0, "eta_no_base_change": t}
    assert r["gorenstein"]["S_m"]["gorenstein"] and r["gorenstein"]["S_m"]["trace_witness_found"]
    assert r["thm_E_identity"]
    assert all(r["lemma_D"].values())
    assert r["congruence_module_length"] == r["check_length_S_mod_a_plus_b"] == t


@pytest.mark.parametrize("p", [3, 5])
def test_non_gorenstein_detected(p):
    """S = {x = y = z mod p}: socle of S/p has dim 2 > f = 1; Thm E's identity fails (eta = p, c * eta_new = p^2)."""
    T, chi, m = toy_non_gorenstein(p)
    g = gorenstein_test(m)
    assert not g["gorenstein"] and g["socle_dim"] == 2 and g["residue_degree"] == 1 and g["local_rank"] == 3
    r = defect(T, chi, m)
    assert r["gorenstein"]["S_new_m"]["gorenstein"]
    assert r["ord"]["eta"] == 1 and r["ord"]["c"] == 1 and r["ord"]["eta_new"] == 1
    assert not r["thm_E_identity"]
    assert all(r["lemma_D"].values())          # Lemma D(a) needs no Gorenstein hypothesis


@pytest.mark.parametrize("p", [3, 5, 7])
def test_ramified_base_change(p):
    """S = Z[T]/(T(T^2 - p)), mu: T -> sqrt p: base change is needed (ord eta = 2, without base change 1)."""
    T, chi, m = toy_ramified(p)
    v = chi.place(m)
    info = place_info(v)
    assert info["dvr"] and info["ramification_index"] == 2 and info["residue_degree"] == 1
    r = defect(T, chi, m)
    assert r["ord"] == {"eta": 2, "c": 1, "eta_new": 1, "eta_no_base_change": 1}
    assert r["thm_E_identity"]
    # same character given by values in O = Z[x]/(x^2 - p)
    O = ZOrder.from_polynomial([1, 0, -p])
    chi2 = Character.from_values(T, O, {"T": [0, 1]})
    w = chi2.place(m)
    assert ord_at(eta(chi2), w) == 2
    with pytest.raises(ValueError):
        Character.from_values(T, O, {"T": [1, 1]})      # 1 + sqrt p is not a root of T(T^2 - p)


def test_maximal_ideals_and_idempotents():
    T = HeckeAlgebra({"T": [[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 0, 3], [0, 0, 1, 0]]})   # 1, 2, sqrt 3
    ms = maximal_ideals(T, 5)
    assert sorted((m.local_rank, m.residue_degree) for m in ms) == [(1, 1), (1, 1), (2, 2)]
    m2 = find_maximal_ideal(T, 5, {"T": [1, 0, 2]})       # x^2 - 3 = x^2 + 2 mod 5, irreducible
    assert m2.residue_degree == 2 and gorenstein_test(m2)["gorenstein"]
    q = 5 ** 6
    es = [m.idempotent(6) for m in ms]
    for e in es:
        assert all(T.mul_mod(e, e, q) == e)
    assert all(sum(es) % q == np.array(T.one, dtype=object) % q)
    with pytest.raises(ValueError):
        find_maximal_ideal(T, 7, {"T": 5})


def test_ideal_arithmetic():
    T, chi, m = toy_l10a(3, 2)
    a, b = T.kernel_of_rep("new"), T.kernel_of_rep("old")
    assert a.intersect(b).rank == 0 and a.ann() == b and b.ann() == a
    assert (a + b).index_in(T.whole()) == 9 and (a * b).rank == 0
    assert a <= T.whole() and not T.whole() <= a and a.is_saturated()
    I = T.ideal([T.scalar(3)])
    assert I.index_in(T.whole()) == 9 and local_length(T.whole(), I, m) == 2
    O, q = T.quotient(a)
    assert O.d == 1 and q.kernel() == a
    # Z[i] from a multiplication table: 2 = -i (1 + i)^2 ramifies; p = 5 splits
    Zi = ZOrder.from_table([[[1, 0], [0, 1]], [[0, 1], [-1, 0]]], [1, 0], {"i": [0, 1]})
    assert len(maximal_ideals(Zi, 5)) == 2 and [m.local_rank for m in maximal_ideals(Zi, 2)] == [2]


def test_level1_weight12_delta():
    """T4-style length: T(1)_m/(delta) at p = 17, k = 12, delta = 3^10 (q+1)^2 - T_3^2: tau(3) = 252, ord_17 = 1."""
    mats, _ = mf_integral_hecke(1, 12, [2, 3])
    T = HeckeAlgebra(mats)
    assert T.d == 1 and T.gen("T3") == [252]
    m = maximal_ideals(T, 17)[0]
    x = T.gen("T3")
    delta = T.sub(T.scalar(3 ** 10 * 16), T.mul(x, x))
    assert local_length(T.whole(), T.ideal([delta]), m) == 1


def test_level3_weight12_p17():
    """S_12(Gamma_0(3)), p = 17 (branch through Delta): ord c_3 = 1 (seed T4 prediction at k = 12), Thm E holds."""
    T, chi, m = example_level3_weight12()
    r = defect(T, chi, m)
    assert r["ranks"] == {"S_m": 2, "S_new_m": 1, "S_old_m": 1, "O": 1}
    assert r["ord"]["c"] == 1 and r["ord"]["eta"] == 1 and r["ord"]["eta_new"] == 0
    assert r["gorenstein"]["S_m"]["gorenstein"] and r["thm_E_identity"]


@pytest.mark.parametrize("N,k,p", [(3, 28, 17), (5, 12, 29), (5, 16, 31)])
def test_mf_orbits(N, k, p):
    """Eigenform orbits of degree <= 2 as O: ord c = 1 at the congruent orbit, eta = c * eta_new."""
    D = mf_qnew_qold(N, k, N)
    reps = {"new": D["new"], "old": D["old"]}
    reps.update({f"f{i}": o["rep"] for i, o in enumerate(D["orbits"])})
    T = HeckeAlgebra(D["full"], reps)
    a, b = T.kernel_of_rep("new"), T.kernel_of_rep("old")
    hits = 0
    for m in maximal_ideals(T, p):
        if not local_length(T.whole(), a + b, m):
            continue
        for i in range(len(D["orbits"])):
            chi = Character.from_rep(T, f"f{i}")
            try:
                chi.place(m)
            except ValueError:
                continue
            r = defect(T, chi, m)
            assert r["ord"]["c"] == 1 and r["thm_E_identity"] and r["gorenstein"]["S_m"]["gorenstein"]
            hits += 1
    assert hits == 1


def test_bad_rep_rejected():
    with pytest.raises(ValueError):
        HeckeAlgebra({"T": [[0, 0], [0, 0]]}, {"bad": {"T": [[1]]}})   # T = 0 on V but 1 on V_bad


def test_results_file():
    """``code/results/s06/C1.json`` (written by ``python -m langlandscape.defect.congruence``) has provenance."""
    try:
        res = results.read("s06/C1.json")
    except FileNotFoundError:
        pytest.skip("C1.json not generated")
    prov = res["provenance"]
    assert {"script", "commit", "params", "runtime_s", "date"} <= set(prov)
    cases = {row["case"] for row in res["data"]}
    assert {"l10a", "non_gorenstein", "ramified"} <= cases
    for row in res["data"]:
        if row["case"] == "l10a":
            assert row["ord"]["eta"] == row["ord"]["c"] == row["t"]
        if row["case"] == "non_gorenstein":
            assert not row["gorenstein"]["S_m"]["gorenstein"]
