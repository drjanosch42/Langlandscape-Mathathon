"""S02-C1: tree-quotient builder ``BG(U, q)`` (def:s02-BG, prop:s02-quot); does not write results."""

from fractions import Fraction

import pytest

from langlandscape import brandt, tree
from langlandscape.classset import euler_phi_ram
from langlandscape.levels import XB, _act, canon_line, class_data

MAX_CASES = [(D, q) for D in (2, 3, 5, 7, 11, 13, 17, 19, 23, 37) for q in (2, 3, 5, 7) if D % q]
LEVEL_CASES = [
    (3, 2, tree.Level.U1(5)), (3, 2, tree.Level.U1(25)), (3, 2, tree.Level.U1(7)), (3, 2, tree.Level.U1(13)),
    (2, 3, tree.Level.U1(7)), (2, 5, tree.Level.U1(7)), (5, 2, tree.Level.U1(9)), (2, 3, tree.Level.U0(5)),
    (3, 5, tree.Level.U0(7)), (11, 3, tree.Level.U0(2)), (2, 3, tree.Level(5, 7)), (7, 2, tree.Level.U1(3)),
    (3, 2, tree.Level(7, 5)),  # <q^2> = <4> nontrivial mod 7, with N0 > 1
]


def _check_basic(T):
    q = T.q
    assert len(T.s0) == len(T.s1) == T.E and T.vertices0 == T.vertices1
    XU = XB(T.D, T.level.N1, T.level.N0)
    XE = XB(T.D, T.level.N1, T.level.N0 * q)
    assert T.X == len(XU) and T.E == len(XE)
    # edge count = sum over vertices of fibres (both endpoint maps), counted as edge classes and with weights
    for s in (T.s0, T.s1):
        fib = [0] * T.X
        fibw = [Fraction(0)] * T.X
        for e, x in enumerate(s):
            fib[x] += 1
            fibw[x] += Fraction(T.vertices0[x].stab, T.edges[e].stab)
        assert sum(fib) == T.E
        assert all(f == q + 1 for f in fibw)  # sum_{e in s_j^{-1}(x)} |Gamma_x|/|Gamma_e| = q + 1
    # stabiliser conventions: w = |Gamma/+-1|, Gamma_e subset Gamma_{s0 e}
    for cell in T.vertices0 + T.edges:
        assert cell.w * (2 if T.minus_one_in_U else 1) == cell.stab
    for e in range(T.E):
        assert T.vertices0[T.s0[e]].stab % T.edges[e].stab == 0
        assert T.vertices1[T.s1[e]].stab % T.edges[e].stab == 0
        assert set(T.edges[e].stab_units) <= set(T.vertices0[T.s0[e]].stab_units)  # same class, Gamma_e < Gamma_x
    for cell in T.vertices0 + T.edges:
        assert len(cell.stab_units) == cell.stab
    # incidence / adjacency consistency
    S0, S1 = T.incidence(0), T.incidence(1)
    A = T.adjacency()
    assert all(sum(S0[x][e] for x in range(T.X)) == 1 == sum(S1[x][e] for x in range(T.X)) for e in range(T.E))
    assert A == [[sum(S0[x][e] * S1[y][e] for e in range(T.E)) for y in range(T.X)] for x in range(T.X)]
    # mass identity sum_e 1/|Gamma_e| = (q+1) sum_x 1/|Gamma_x|
    assert sum(Fraction(1, g) for g in T.stab_e) == (q + 1) * sum(Fraction(1, g) for g in T.stab_v)


@pytest.mark.parametrize("D,q", MAX_CASES)
def test_max_level_equals_brandt_Tq(D, q):
    T = tree.build(D, q)
    _check_basic(T)
    m = T.brandt_module()  # same algebra instance as class_data(D) (brandt.module(D) may use another O basis)
    perm = T.brandt_perm()  # S01 levels class c -> brandt class
    assert sorted(perm) == list(range(m.h)) and T.X == m.h
    Bq = m.T(q)
    H = T.hecke_matrix()
    for c in range(T.X):
        for c2 in range(T.X):
            assert H[c][c2] == Bq[perm[c]][perm[c2]]
    assert T.components() == 1
    assert sum(Fraction(1, w) for w in T.w_v) == Fraction(euler_phi_ram(D), 12)  # Eichler mass with w = |Gamma/+-1|


def _scale_perm(T, s):
    """Vertex permutation ``[z] -> [z c]``, ``c`` central with ``c_N = s^{-1}`` (row ``v -> s v``)."""
    N1, N0 = T.level.N1, T.level.N0
    X = XB(T.D, N1, N0)
    out = []
    for v in T.vertices0:
        vv, l = v.pt
        vv2 = tuple((s * a) % N1 for a in vv) if N1 > 1 else ()
        l2 = canon_line(tuple((s * a) % N0 for a in l), N0) if N0 > 1 else ()
        out.append(T.vertex_of(v.c, X.orbits[v.c][X.orbit_of[v.c][(vv2, l2)]]["rep"]))
    return out


@pytest.mark.parametrize("D,q,U", LEVEL_CASES)
def test_levels_basic_and_reverse_hecke(D, q, U):
    """``s_1`` is well defined (checked in ``build``) and the type-1 correspondence is ``<q>``-twisted ``T_q``.

    ``{y : [y alpha] = [z]} = {z alpha^{-1} u}`` and ``alpha^{-1} = q_q^{-1} w alpha w`` (``w`` the Weyl element), so
    the reverse weighted adjacency ``R[x'][x] = sum_{s1 e = x', s0 e = x} |Gamma_x'|/|Gamma_e|`` equals ``H[pi(x')]``
    with ``pi`` = right multiplication by ``q_q^{-1}``, i.e. row ``v -> q^{-1} v``.  This detects a lost scalar ``q``
    in ``s_1`` (then the identity holds with ``v -> q v`` instead).
    """
    T = tree.build(D, q, U)
    _check_basic(T)
    assert T.components() == 1
    H = T.hecke_matrix()
    R = [[0] * T.X for _ in range(T.X)]
    for e, (a, b) in enumerate(zip(T.s0, T.s1)):
        R[b][a] += T.vertices0[b].stab // T.edges[e].stab
    N = U.N1 * U.N0
    p = _scale_perm(T, pow(q, -1, N))
    assert all(R[x] == H[p[x]] for x in range(T.X))
    if _scale_perm(T, q * q % N) != list(range(T.X)):  # <q^2> nontrivial on X: the test has detection power
        p2 = _scale_perm(T, q % N)
        assert not all(R[x] == H[p2[x]] for x in range(T.X))


@pytest.mark.parametrize("D,q,X,E,rk", [(2, 7, 1, 2, 1), (2, 13, 1, 3, 2), (11, 2, 2, 3, 0)])
def test_C3_T2_numbers(D, q, X, E, rk):
    T = tree.build(D, q)
    assert (T.X, T.E, T.E - 2 * T.X + T.components()) == (X, E, rk)


@pytest.mark.parametrize("s,S", [(1, 2), (2, 50), (3, 1250)])
def test_C3_T3_numbers(s, S):
    T = tree.build(3, 2, tree.Level.U1(5**s))
    assert T.X == S and T.E == 3 * S and T.components() == 1
    assert T.E - 2 * T.X + 1 == S + 1
    assert set(T.stab_v) == {1} and set(T.stab_e) == {1}


# ---------------------------------------------------------------- transport elements (coefficients, for C5)
TRANSPORT_CASES = [
    (2, 3, tree.Level(), 5), (11, 2, tree.Level(), 5), (37, 3, tree.Level(), 5), (3, 2, tree.Level.U1(5), 7),
    (3, 2, tree.Level.U1(7), 5), (2, 3, tree.Level(5, 7), 11), (3, 2, tree.Level(7, 5), 11), (5, 2, tree.Level.U1(9), 7),
]


def _conj_inv(B, g):
    n = B.nrd(g)
    return tuple(x / n for x in B.conj(g))


@pytest.mark.parametrize("D,q,U,p", TRANSPORT_CASES)
def test_transport_elements(D, q, U, p):
    """``move_j`` satisfy their defining relations; ``u_j`` intertwine stabilisers and are orbit-consistent.

    Orbit consistency (scalar-sensitive): if ``y' `` is another point of the edge orbit with ``gamma y in y' U``
    (``gamma in Gamma_c``) then ``delta = beta gamma^{-1} beta'^{-1} in Gamma_{s_j e}`` and
    ``u_j(y) = phi_{c'}(delta) u_j(y') phi_c(gamma)`` (``[y] (x) v = [y'] (x) phi_c(gamma) v``).
    """
    m = 2
    mod = p**m
    T = tree.build(D, q, U)
    ctx, B, cd = T._ctx, T._ctx.cd.B, T._ctx.cd
    N1, N0 = U.N1, U.N0
    XE = XB(D, N1, N0 * q)
    loc = ctx.loc
    for e, cell in enumerate(T.edges):
        c = cell.c
        g0, beta = T.move0[e], T.move1[e]
        v0, v1 = T.vertices0[T.s0[e]], T.vertices1[T.s1[e]]
        # s0: gamma_0 in Gamma_c moves the projected point to the vertex representative
        assert B.nrd(g0) == 1 and all(x.denominator == 1 for x in loc.coords(c, g0))
        _, P = ctx.s0_point(c, cell.pt)
        gi = B.conj(g0)
        assert _act(P, loc.phi_elt(c, gi, N1) if N1 > 1 else None, loc.phi_elt(c, gi, N0) if N0 > 1 else None,
                    N1, N0) == v0.pt
        # s1: L_{y alpha} beta^{-1} = I_{c'}
        L = T.s1_lattice(e)
        Lb = tree.Lattice([B.mul(b, _conj_inv(B, beta)) for b in L.basis])
        assert Lb.key == cd.reps[v1.c][0].key
        assert ctx.s1_point(c, cell.pt)[0] == v1.c
        # u_j intertwine Gamma_e -> Gamma_{s_j e}
        for j, (bj, vj) in enumerate(((g0, v0), (beta, v1))):
            u = T.coeff_matrix(e, j, p, m)
            ui = tree._inv2(u, mod)
            target = {tuple(t) for t in T.stab_elements(vj)}
            for g in T.stab_elements(cell):
                h = B.mul(B.mul(bj, g), _conj_inv(B, bj))
                assert h in target
                lhs = tree._mul2(tree._mul2(u, T.local_matrix(c, g, p, m), mod), ui, mod)
                assert lhs == T.local_matrix(vj.c, h, p, m)
        assert (lambda a: (a[0] * a[3] - a[1] * a[2]) % mod)(T.coeff_matrix(e, 0, p, m)) == 1
        # orbit consistency
        k = XE.orbit_of[c][cell.pt]
        members = [pt for pt, kk in XE.orbit_of[c].items() if kk == k]
        u0, u1 = T.coeff_matrix(e, 0, p, m), T.coeff_matrix(e, 1, p, m)
        for pt in members[:6]:
            gam = ctx._mover(c, cell.pt, pt, N0 * q)  # point(gamma y) = pt
            ph = T.local_matrix(c, gam, p, m)
            a0, g0p = ctx.s0_full(c, pt)
            a1, betap = ctx.s1_full(c, pt)
            assert (a0, a1) == (T.s0[e], T.s1[e])
            for bj, bjp, vj, uj, ujp in ((g0, g0p, v0, u0, loc.phi_elt(c, g0p, mod)),
                                         (beta, betap, v1, u1, ctx.u_beta(c, v1.c, betap, p, m))):
                delta = B.mul(B.mul(bj, _conj_inv(B, gam)), _conj_inv(B, bjp))
                assert delta in {tuple(t) for t in T.stab_elements(vj)}
                rhs = tree._mul2(tree._mul2(T.local_matrix(vj.c, delta, p, m), ujp, mod), ph, mod)
                assert uj == rhs


def test_vertex_of_point_and_errors():
    T = tree.build(3, 2, tree.Level.U1(7))
    X = XB(3, 7, 1)
    for pt in list(X.orbit_of[0])[:10]:
        v, gam = T.vertex_of_point(0, pt)
        gi = T._ctx.cd.B.conj(gam)
        assert _act(pt, T._ctx.loc.phi_elt(0, gi, 7), None, 7, 1) == T.vertices0[v].pt
    with pytest.raises(ValueError):
        tree.build(3, 3)
    with pytest.raises(ValueError):
        tree.build(3, 2, tree.Level.U1(4))
    with pytest.raises(ValueError):
        T.coeff_matrix(0, 0, 2, 1)
