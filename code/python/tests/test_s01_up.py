"""S01-C5: N_{U_p} and U'_p on S_s = X_B(U_1(5^s)), B = B_3, p = 5 (lem:s01-Up).

Matrices are homological (columns = images, see ``langlandscape.up``).  ``tr`` below is the trace
``tr_{s+1,s}: Z^{S_{s+1}} -> Z^{S_s}``, ``tr f(x) = sum_{u in U_(s)/U_(s+1)} f(xu)``, on *functions*;
its transpose on homology is ``pi^!: Z[S_s] -> Z[S_{s+1}]``.  lem:s01-Up(c) says
``tr o U'_p = U'_p o tr`` on functions, i.e. ``U'_p o pi^! = pi^! o U'_p`` on homology.
"""

from fractions import Fraction

import numpy as np
import pytest

from langlandscape import padic, results, up

HALF = Fraction(1, 2)


@pytest.fixture(scope="module")
def C():
    return up.context(3)


@pytest.fixture(scope="module")
def ops(C):
    return {s: (C.Up(s), C.Up_prime(s)) for s in (1, 2, 3)}


# --- the algebra, the order, the splitting -----------------------------------------------------

def test_order_maximal():
    assert padic.is_order(up.A, up.B, up.BASIS)
    assert padic.discriminant(up.A, up.B, up.BASIS) == 9  # reduced discriminant 3 = disc(B_3)
    assert len(up.elements_of_norm(1)) == 12
    assert len(up.elements_of_norm(2)) == 12 * 3  # 3 = 2 + 1 right ideals of norm 2 (h = 1)
    assert len(up.elements_of_norm(5)) == 12 * 6
    assert len(up.classes_mod_units(5)) == 6


@pytest.mark.parametrize("p", [5, 7, 11, 13, 17])
@pytest.mark.parametrize("n", [1, 4])
def test_splitting(p, n):
    S = padic.split(up.A, up.B, up.BASIS, p, n)  # checks multiplicativity and bijectivity mod p
    # Hurwitz order of (-1, -1) (D = 2) as a second algebra
    hur = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (HALF, HALF, HALF, HALF)]
    padic.split(-1, -1, hur, p, n)
    assert S.image([1, 0, 0, 0]) == [[1, 0], [0, 1]]


def test_splitting_det_is_nrd():
    S = padic.split(up.A, up.B, up.BASIS, 5, 6)
    for g in up.elements_of_norm(5) + up.elements_of_norm(2):
        nrd = padic.quat_nrd(up.A, up.B, padic.to_B(up.BASIS, g))
        assert padic.mat_det(S.image(g), S.mod) == nrd % S.mod


# --- class sets ---------------------------------------------------------------------------------

def test_class_set_sizes(C):
    assert len(C.levels[1]) == 2
    assert len(C.levels[2]) == 50
    assert len(C.levels[3]) == 1250  # 2 * 25^(s-1), thm:s01-mass(d)


def test_free_action(C):
    for s in (1, 2, 3):
        assert set(C.levels[s].orbit_sizes) == {12}  # Gamma_x = 1 for all x (lem:s01-stab(b))


# --- operators ----------------------------------------------------------------------------------

@pytest.mark.parametrize("s", [1, 2, 3])
def test_degrees(ops, s):
    U, V = ops[s]
    for M in (U, V):
        assert (M.sum(axis=0) == 5).all() and (M.sum(axis=1) == 5).all()


@pytest.mark.parametrize("s", [1, 2])
@pytest.mark.parametrize("shift", [1, 3])
def test_independent_of_k(C, ops, s, shift):
    U, V = ops[s]
    assert (C.Up(s, shift) == U).all()
    assert (C.Up_prime(s, shift) == V).all()


@pytest.mark.parametrize("s", [1, 2])
def test_Up_closed_form(C, ops, s):
    """Independent derivation: U_p[v] = sum [v iota(gamma)] over the 5 norm-5 classes gamma O^x
    whose image mod 5 is not the line ker(v) (image of k varpi_j mod 5 = span k (j, 1)^T)."""
    lv = C.levels[s]
    q = lv.q
    M = np.zeros_like(ops[s][0])
    for c, v in enumerate(lv.points):
        for G in C.gammas5:
            w = lv._vm(v, G)
            if w[0] % 5 == 0 and w[1] % 5 == 0:
                continue  # image(iota(gamma)) = ker(v)
            M[lv.idx(w), c] += 1
    assert (M == ops[s][0]).all()


@pytest.mark.parametrize("s", [1, 2])
def test_pi_push_commutes_with_Up(C, ops, s):
    """lem:s01-Up(b): pi_* o U_p = U_p o pi_*."""
    pp = C.pi_push(s)
    assert (pp @ ops[s + 1][0] == ops[s][0] @ pp).all()


@pytest.mark.parametrize("s", [1, 2])
def test_pi_push_not_commutes_with_Upr(C, ops, s):
    pp = C.pi_push(s)
    assert not (pp @ ops[s + 1][1] == ops[s][1] @ pp).all()


@pytest.mark.parametrize("s", [1, 2])
def test_trace_commutes_with_Upr(C, ops, s):
    """lem:s01-Up(c): tr o U'_p = U'_p o tr on functions (= U'_p pi^! = pi^! U'_p on homology)."""
    ps = C.pi_shriek(s)
    assert (ps == C.pi_push(s).T).all()  # all Gamma_x = 1: pi^! is the fibre sum
    V_lo, V_hi = ops[s][1], ops[s + 1][1]
    assert (V_hi @ ps == ps @ V_lo).all()
    # function-side form
    tr = ps.T
    assert (tr @ V_hi.T == V_lo.T @ tr).all()


@pytest.mark.parametrize("s", [1, 2, 3])
def test_Up_adjoint(ops, s):
    """lem:s01-Up(d) with M = 1, w_x = 1: U_p^* = U'_p, i.e. M(U_p)^T = M(U'_p)."""
    U, V = ops[s]
    assert (U.T == V).all()


@pytest.mark.parametrize("s", [1, 2])
def test_commute_diamond_T2(C, ops, s):
    U, V = ops[s]
    T = C.T2(s)
    assert (T.sum(axis=0) == 3).all()
    for d in range(1, 5**s):
        if d % 5 == 0:
            continue
        D = C.diamond(s, d)
        for X in (U, V, T):
            assert (X @ D == D @ X).all()
    for X in (U, V):
        assert (X @ T == T @ X).all()
    assert (C.diamond(s, 5**s - 1) == np.eye(len(C.levels[s]), dtype=np.int64)).all()  # <-1> = 1
    assert (T.T == C.diamond(s, 2) @ T).all()  # T_2^* = S_2^{-1} T_2, S_2 = <2>^{-1}


def test_charpolys(C, ops):
    f1 = up.factored_charpoly(ops[1][0])["factors"]
    assert sorted(f1) == sorted([["x - 5", 1], ["x - 1", 1]])
    f2 = dict((a, b) for a, b in up.factored_charpoly(ops[2][0])["factors"])
    assert f2["x"] == 8 and f2["x - 5"] == 1 and f2["x - 1"] == 1
    from langlandscape.pari import get_pari

    pari = get_pari()
    assert sum(b * int(pari.poldegree(pari(a))) for a, b in f2.items()) == 50
    # character decomposition at s = 2: dims and U_p-charpolys on the Galois orbits
    chars = up.character_data(C.diamond(2, 2), {"Up": ops[2][0]}, 20)
    dims = {e["m"]: e["dim_Q"] for e in chars}
    assert dims == {1: 6, 2: 4, 4: 0, 5: 24, 10: 16, 20: 0}  # only even characters occur


def test_result_file():
    data = results.read("s01/up.json")["data"]
    assert data["levels"]["S_1"]["size"] == 2 and data["levels"]["S_2"]["size"] == 50
    assert all(v for k, v in data["checks"].items() if "expected False" not in k and "(info)" not in k)
    assert not any(v for k, v in data["checks"].items() if "expected False" in k)
