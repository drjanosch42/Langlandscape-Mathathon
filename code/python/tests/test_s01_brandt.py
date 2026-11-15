"""S01-C3: weight-2 Brandt matrices: relations, seed C4(ii) vs PARI mf, isogeny graphs, D-new checks.

Nothing is written into code/results here (``python -m langlandscape.brandt`` does that).
"""

import pytest

from langlandscape import brandt as b


@pytest.mark.parametrize("q", b.SEED_QS)
def test_relations_and_seed_c4ii(q):
    m = b.module(q)
    rep = b.relations_report(m)
    assert rep == {"row_sums": True, "weighted_symmetry": True, "commutative": True}
    for l in b.ells_for(q):
        cp = b.charpoly_coeffs(m.T(l))
        assert cp == b.seed_rhs(q, l), (q, l)


@pytest.mark.parametrize("q", b.SEED_QS)
def test_isogeny_graph_matches(q):
    m = b.module(q)
    Ts = {l: m.T(l) for l in b.ells_for(q)}
    g = b.isogeny_graph(q)
    assert len(g["j"]) == m.h
    for l, A in g["A"].items():
        assert all(sum(r) == l + 1 for r in A)
    assert b.match_permutation(Ts, m.gammas, g) is not None


@pytest.mark.parametrize("D,M", [(11, 1), (37, 1), (5, 7)])
def test_hecke_multiplicativity(D, M):
    """T_l T_l' = T_{l l'} (l != l'), the right side computed independently by enumerating norm-l l' ideals."""
    m = b.module(D, M)
    l1, l2 = b.ells_for(D, M)[:2]
    assert b.matmul(m.T(l1), m.T(l2)) == m.T_direct(l1 * l2)
    assert b.matmul(m.T(l1), m.T(l2)) == b.matmul(m.T(l2), m.T(l1))


@pytest.mark.parametrize("D,M", b.DNEW_CASES)
def test_dnew(D, M):
    m = b.module(D, M)
    assert m.h == b.dnew_dim(D, M)
    assert b.relations_report(m) == {"row_sums": True, "weighted_symmetry": True, "commutative": True}
    for l in b.ells_for(D, M):
        assert b.charpoly_coeffs(m.T(l)) == b.dnew_rhs(D, M, l), (D, M, l)


def test_t1_numbers():
    t = b.t1_numbers()
    assert sorted(t["gammas"]) == [4, 6]
    assert str(t["mass"]) == "5/12"
    assert t["T2_eigenvalues"] == [3, -2]
    assert t["X0_11"]["genus"] == 1 and t["X0_11"]["a2_mf"] == -2 == t["X0_11"]["a2_11a1_ellap"]
