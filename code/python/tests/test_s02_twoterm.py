"""S02-C5: two-term complex for H_*(Gamma_U, V_k) (prop:s02-coh (b), (d), prop:s02-free, if:s02-coh).

Tests compute in memory and read the committed ``code/results/s02/H_Vk.json``; they never write tracked files.
"""

import pytest

from langlandscape import results, tree, twoterm as tt
from langlandscape.levels import class_data

FREE = (3, 2, 5, 1, 7, 4)  # B_3, q = 2, U_1(5), p = 7, m = 4


@pytest.fixture(scope="module")
def free_lm():
    td = tt.tree_data(*FREE[:4])
    return td, tt.LocalModel(td, *FREE[4:])


def test_free_level_ranks(free_lm):
    """prop:s02-free / def:s02-indef: rk H_1(Gamma_U, V_k) = (q-1)(k-1)|X_B(U)| for k > 2; E - 2X + 1 for k = 2."""
    td, lm = free_lm
    q, X, E = td.q, td.T.X, td.T.E
    assert td.free and (X, E) == (2, 6) and td.T.components() == 1
    r = tt.case(*FREE, range(2, 9))
    for k in range(2, 9):
        row = r["k"][str(k)]
        assert row["rank_d_certified"] is not None
        if k == 2:
            assert row["rank_H1"] == E - 2 * X + 1 == 3
            assert row["H0"] == [FREE[5]]  # H_0 = Z/p^m (one component)
        else:
            assert row["rank_H1"] == (q - 1) * (k - 1) * X
            assert row["rank_H0"] == 0 and row["H0"] == []  # H_0 = 0 (no 7-torsion here)
            assert row["rank_Hco0_Zp_upper"] == 0  # H^0 = 0
        assert row["rank_d_Fell"] == row["rank_d_Qp_lower"]  # global model (exact splitting mod ell) agrees


def test_k2_matches_C1_graph():
    """k = 2: rank H_1 = E - 2X + 1 equals C2's rk H_1 of BG(U_1(5), 2) (validation.json)."""
    val = results.read("s02/validation.json")["data"]["cases"]
    c2 = next(c for c in val if (c["D"], c["q"], c["level"]["N1"], c["level"]["N0"]) == (3, 2, 5, 1))
    r = tt.case(*FREE, [2])
    assert r["k"]["2"]["rank_H1"] == c2["rk_H1"] == 3


def test_twist_is_needed(free_lm):
    """Dropping the coefficient twists (u_j = 1) gives H_0 of rank k-1 at the free level: the twist is detectable."""
    td, lm = free_lm
    one = ((1, 0), (0, 1))
    lm2 = tt.LocalModel.__new__(tt.LocalModel)
    lm2.td, lm2.p, lm2.m, lm2.mod = td, lm.p, lm.m, lm.mod
    lm2.Hv, lm2.He, lm2.u0, lm2.u1 = lm.Hv, lm.He, [one] * td.T.E, [one] * td.T.E
    h = lm2.homology(5)
    assert h["rank_H0_Zp_upper"] == 4 and lm.homology(5)["rank_H0_Zp_upper"] == 0


def test_signs_trivial_coefficients():
    """if:s02-coh: d = (-s_{0*}, s_{1*}) satisfies deg o d = 0 (Serre's d e = t(e) - o(e)); (+s_{0*}, s_{1*}) does not.
    delta(f0, f1) = s_1^* f1 - s_0^* f0 is exactly the transpose of d (prop:s02-duality (a)); and the local model at
    k = 2 reproduces both matrices mod p^m."""
    for c in (FREE, (2, 3, 1, 1, 5, 4), (3, 2, 1, 7, 5, 4)):
        td = tt.tree_data(*c[:4])
        A = tt.boundary_Z(td)
        assert all(sum(col) == 0 for col in zip(*A))
        Af = tt.boundary_Z(td, signs=(1, 1))
        assert all(sum(col) == 2 for col in zip(*Af))
        assert tt.coboundary_Z(td) == [list(r) for r in zip(*A)]
        lm = tt.LocalModel(td, *c[4:])
        Al, r0, r1 = lm.boundary(0)
        assert Al == [[x % lm.mod for x in row] for row in A]
        Cl, _, _ = lm.coboundary(0)
        assert Cl == [[x % lm.mod for x in row] for row in tt.coboundary_Z(td)]


def test_sign_flip_V_k_is_isomorphic(free_lm):
    """Flipping the sign of a whole vertex type is an automorphism of the target, so the homology is unchanged:
    the sign convention is only detectable through the augmentation (test above), not through H_*."""
    td, lm = free_lm
    for n in (1, 3):
        A, _, _ = lm.boundary(n)
        B_, _, _ = lm.boundary(n, signs=(1, 1))
        assert tt.elementary_divisors(A, lm.p, lm.m) == tt.elementary_divisors(B_, lm.p, lm.m)


@pytest.mark.parametrize("D,q,p", [(2, 3, 5), (2, 5, 7), (2, 7, 5), (3, 2, 5), (3, 5, 7), (3, 7, 5)])
def test_maximal_level_brandt(D, q, p):
    """U = O^x (non-free): rk M(O^x; V_k) agrees with S01 (symn.json dim_brandt), rk M(U_0(q); V_k) with JL, and
    rk H_1 = rk M(U_0 q) - 2 rk M(O^x) (prop:s02-coh (d)) = dim S_k(Gamma_0(Dq))^new; odd k: everything 0."""
    grid = results.read("s01/symn.json")["data"]["grid"]
    r = tt.case(D, q, 1, 1, p, 4, range(2, 11))
    assert not r["free"] and r["minus_one_in_U"]
    for k in range(2, 11):
        row = r["k"][str(k)]
        assert row["rank_d_certified"] is not None
        if k % 2:
            assert row["rank_C1"] == row["rank_C0"] == 0
            continue
        assert row["rank_M_U"] == grid[f"{D},{k}"]["dim_brandt"] == row["pred_rank_M_U"]
        assert row["rank_M_Uprime"] == row["pred_rank_M_Uprime"]
        assert row["rank_H1"] == row["pred_rank_H1_JL"]
        if k > 2:
            assert row["rank_H1"] == row["pred_coh_d_rank_H1"] and row["rank_H0"] == 0
            assert row["rank_Hco0_Zp_upper"] == 0


def test_norm_trace_and_epsilon():
    """prop:s02-Mhomprops (d) nu_U s_{j*} = tr_j nu_{U'} and (e) nu_{U'} s_j^! = s_j^* nu_U, with N_x summed over
    Gamma_x/(Gamma_x cap +-1); epsilon = |{+-1} cap U''| common (asserted inside).  The multiplicity-free fibre sum
    s_j^sharp violates (e) exactly when some index [Gamma_x : Gamma_e] > 1 (discriminating at O^x, not at free levels)."""
    for c in ((2, 3, 1, 1, 5, 4), (3, 7, 1, 1, 5, 4), (3, 2, 1, 7, 5, 4), FREE):
        lm = tt.LocalModel(tt.tree_data(*c[:4]), *c[4:])
        td = lm.td
        nontriv = sum(td.T.vertices0[a].stab != td.T.edges[e].stab for e, a in enumerate(td.T.s0)) + \
            sum(td.T.vertices1[b].stab != td.T.edges[e].stab for e, b in enumerate(td.T.s1))
        for n in (0, 2, 4):
            r = lm.norm_trace_check(n)
            assert r["pushforward_identity_d"] and r["transfer_identity_e"]
            if n == 0:
                assert r["naive_transfer_violations"] == nontriv
        assert (nontriv > 0) == (c != FREE)


def test_delta_is_transpose_V_k(free_lm):
    """prop:s02-duality (a) for V_k (free level, standard bases): delta with coefficients V^* is exactly d^T for V,
    no index factor."""
    td, lm = free_lm
    for n in (1, 3, 6):
        A, _, _ = lm.boundary(n)
        C, _, _ = lm.coboundary(n, dual=True)
        assert C == [list(r) for r in zip(*A)]
        C2, _, _ = lm.coboundary(n)
        assert C2 != C  # with V itself (u^{-1} instead of u^T) it is not the transpose


def test_free_level_newforms():
    """Free level vs modular forms (JL with nebentypus): rk H_1(Gamma_{U_1(5)}, V_k) for B_3, q = 2 equals
    sum_{chi mod 5, chi(-1) = (-1)^k} of q-new forms of level 6M (M | 5); rk M(U_1(5); V_k) likewise at level 3M."""
    r = tt.case(*FREE, range(2, 9))
    for k in range(2, 9):
        row = r["k"][str(k)]
        assert row["rank_H1"] == row["pred_rank_H1_JL"]
        assert row["rank_M_U"] == row["pred_rank_M_U"]


def test_psi_right_linear_at_p():
    """psi_c(w r) = psi_c(w) phi_c(r) at p (the normalisation x_{c,p} of the module docstring)."""
    D, p, m = 3, 7, 3
    td = tt.tree_data(3, 2, 5, 1)
    loc, cd = td._b.loc, class_data(D)
    mod = p**m
    for c in range(cd.h):
        for u in cd.units(c)[:6]:
            ph = cd.phi(c, u, mod)
            eps = loc._elt(c, u)
            for row in ((1, 0), (0, 1), (2, 5)):
                w = loc.preimage(c, row, mod)
                lhs = loc.psi_mod(c, cd.B.mul(w, eps), mod)
                rhs = ((row[0] * ph[0] + row[1] * ph[2]) % mod, (row[0] * ph[1] + row[1] * ph[3]) % mod)
                assert tuple(lhs) == rhs


def test_against_tree_api():
    """If tree.py exposes ``coeff_matrix`` (C1 audit fix), its u_j agree with ours up to H_v."""
    T = tree.build(*FREE[:2], tree.Level(*FREE[2:4]))
    if not hasattr(T, "coeff_matrix"):
        pytest.skip("tree.py has no coeff_matrix yet")
    for c in (FREE, (2, 7, 1, 1, 5, 4), (3, 2, 1, 7, 5, 4)):
        D, q, N1, N0, p, m = c
        td = tt.tree_data(D, q, N1, N0)
        lm = tt.LocalModel(td, p, m)
        T = tree.build(D, q, tree.Level(N1, N0))
        for e in range(T.E):
            for j, u, v in ((0, lm.u0[e], td.tw[e].v0), (1, lm.u1[e], td.tw[e].v1)):
                a, b, cc, d = T.coeff_matrix(e, j, p, m)
                h = tt._mm(u, tt.mat_inv2(((a, b), (cc, d)), lm.mod), lm.mod)
                assert h in set(lm.Hv[v])


def test_results_file():
    d = results.read("s02/H_Vk.json")
    assert d["provenance"]["script"].endswith("twoterm.py")
    data = d["data"]
    assert data["all_ok"]
    acc = [a for a in data["acceptance"] if (a["D"], a["q"], a["level"]) == (3, 2, "U1(5)") and a["k"] <= 8]
    assert [a["rank_H1"] for a in acc] == [3, 4, 6, 8, 10, 12, 14]
    assert all(a["ok"] for a in acc)
