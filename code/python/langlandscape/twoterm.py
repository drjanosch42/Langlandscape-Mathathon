"""S02-C5: ``H_*(Gamma_U, V_k)`` and ``H^*(Gamma_U, V_k)`` via the two-term complex (H02.5).

Tex labels (``plan/staged/stage-02-tree-quotients.tex``; written maths ``mathematics/chapters/s02/3-cohomology.tex``):
``prop:s02-coh`` (b), (d), ``def:s02-Mhom``, ``prop:s02-Mhomprops``, ``lem:s02-cellmod``, ``prop:s02-free``,
``def:s02-indef``, ``if:s02-coh``.  Graph: :mod:`langlandscape.tree` (S02-C1, not modified); coefficients
``V_k = Sym^{k-2}`` with the left action ``(g.P)(X, Y) = P((X, Y) g)`` of ``eq:s01-Vk`` (:func:`symn.sym_matrix`).

Complexes (signs exactly as ``if:s02-coh``; orientation type 0 -> type 1, ``o = s_0``, ``t = s_1``)::

    homological:   0 -> M(U'; V)_*  --d = (-s_{0*}, s_{1*})-->  M(U; V)_* (+) M(U; V)_*  -> 0     (degrees 1, 0)
    cohomological: 0 -> M(U; V)^2   --delta(f0, f1) = s_1^* f1 - s_0^* f0-->  M(U'; V)    -> 0     (degrees 0, 1)

with ``U' = U_0(q) U``, ``M(U''; V)_* = (+)_[x] V_{H_x}`` and ``M(U''; V) = (+)_[x] V^{H_x}``,
``H_x = x_p^{-1} Gamma_x x_p`` (``prop:s02-Mhomprops`` (a): any representatives may be used; the complex is
defined without choices on ``Z[B^x \\ B^^x] (x)_{Z[U'']} V``).  Here ``Gamma_x`` is the full stabiliser (including
``-1`` when ``-1 in U``).

Representatives and the coefficient twist (this is the data tree.py does not expose; recomputed here).
For a cell of S01 class ``c`` (left ``O``-ideal ``I_c``) with level point ``pt`` the representative idele ``x`` has
``L_x = I_c``, level datum ``pt`` and ``p``-component ``x_{c,p}`` normalised by ``psi_c(r x_{c,p}^{-1}) = r`` (rows
``r in Z_p^2``; ``psi_c`` = the right-``O_c``-linear coordinate map of tree.py, now at ``p``).  Then
``phi_c(rho) = x_{c,p}^{-1} rho x_{c,p}`` for ``rho in O_c`` (``phi_c`` = the S01 splitting at ``p``), so ``H_x`` is
``phi_c`` of the units of ``O_c`` fixing ``pt``.  For an edge ``e = [y]`` (class ``c``, point ``pt``):

* ``s_0``: ``[y]`` at level ``U`` has class ``c`` and point ``pt0`` (= ``s0_point``).  If ``eps in O_c^x`` satisfies
  ``pt(eps y) = pt0 phi_c(eps)^{-1} = rep`` (the orbit representative), then ``[y] (x) v = [x_rep] (x) phi_c(eps) v``.
* ``s_1``: ``q L_{y alpha} = I_{c'} g`` (``g in B^x`` from tree.py's ``_find_gamma``), so ``y alpha = (q g^{-1})
  x' u`` with ``u_p = T := x_{c',p}^{-1} (g/q) x_{c,p}``.  In ``psi``-coordinates ``r T^{-1} = psi_{c'}(q
  psi_c^{-1}(r) g^{-1})``: this is tree.py's transport matrix ``G``, computed mod ``p^m`` instead of mod ``N``.  With
  ``eps' in O_{c'}^x`` normalising the transported point as for ``s_0``: ``[y alpha] (x) v = [x_rep'] (x)
  phi_{c'}(eps') T v``.

So ``s_{j*}`` is ``v (mod I_{H_e}) -> u_j v (mod I_{H_v})`` and ``s_j^* f (e) = u_j^{-1} f(v)``; the code asserts
``u_j H_e u_j^{-1} subset H_v`` (well-definedness).  Over ``Z/p^m`` (``p >= 5``, ``p`` prime to ``D N q``) every
``|H_x|`` is a unit, ``V_H ~ e_H V = V^H`` (``e_H`` the averaging idempotent), and all modules are free.

Second model (``global_model``): the same complex in Gross's global form (:mod:`symn`), ``B^x`` acting on
``V_k (x) K`` through the exact splitting ``s : B -> M_2(Q(sqrt a))``, twists ``s(eps)`` and ``s(eps') s(g)/q``, reduced
modulo a prime ``ell`` of ``K`` of degree one.  It *reuses* :func:`tree_data` (``eps0``, ``eps1``, ``g`` and the
stabiliser lists), so it is independent only of the ``p``-adic normalisation ``x_{c,p}`` (the ``psi``-at-``p`` matrix
``T``).  Independent checks are the newform-dimension comparisons (``pred_rank_*_JL``, PARI ``mfdim``) and the
cross-check against tree.py's ``coeff_matrix`` (C1, separate code).  Its ranks are lower bounds for the ``K``-
(= ``Q_p``-) ranks of ``d``; with the trivial upper bound ``rk d <= min(r1, r0)`` (minus the number of components at
``k = 2``) they pin down ``rk H_1`` (``rank_d_certified``).

Output keys ``H1``, ``H0``, ``Hco0``, ``Hco1``: the ``Z/p^m``-module structures (exponent ``e`` = a summand
``Z/p^e``) of the homology of the complex tensored with ``Z/p^m``, one ``p`` per case -- only the ``p``-part.  Over
``Z_p``, ``H_1`` and ``H^0`` are torsion-free; their ``Z/p^m``-versions can carry ``Z/p^e`` (``e < m``) summands coming
from ``p``-torsion of ``H_0`` resp. ``H^1``.

Run ``python3 -m langlandscape.twoterm`` to write ``code/results/s02/H_Vk.json``.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from fractions import Fraction
from functools import lru_cache
from math import gcd

from . import results, tree
from .levels import PREC, XB, _act
from .quat import Lattice

# ---------------------------------------------------------------- linear algebra over Z/p^m
def _val(x: int, p: int, m: int) -> int:
    x %= p**m
    if x == 0:
        return m
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def mat_mul(A, B, mod):
    Bt = list(zip(*B)) if B else []
    return [[sum(a * b for a, b in zip(row, col)) % mod for col in Bt] for row in A]


def mat_inv2(g, mod):
    (a, b), (c, d) = g
    di = pow((a * d - b * c) % mod, -1, mod)
    return ((d * di % mod, -b * di % mod), (-c * di % mod, a * di % mod))


def sym(g, n: int, mod: int):
    """``Sym^n`` of the 2x2 matrix ``g`` mod ``mod`` (columns = images of ``X^{n-t} Y^t``), as :func:`symn.sym_matrix`."""
    (a, b), (c, d) = g

    def pmul(p_, q_):
        out = [0] * (len(p_) + len(q_) - 1)
        for i, x in enumerate(p_):
            for j, y in enumerate(q_):
                out[i + j] = (out[i + j] + x * y) % mod
        return out

    pw1, pw2 = [[1]], [[1]]
    for _ in range(n):
        pw1.append(pmul(pw1[-1], [a, c]))
        pw2.append(pmul(pw2[-1], [b, d]))
    cols = [pmul(pw1[n - t], pw2[t]) for t in range(n + 1)]
    return [[cols[t][s] for t in range(n + 1)] for s in range(n + 1)]


def elementary_divisors(A, p: int, m: int) -> list[int]:
    """Valuations ``a_i < m`` of the non-zero elementary divisors of ``A`` over ``Z/p^m`` (Smith form, min-valuation pivots)."""
    mod = p**m
    M = [[x % mod for x in row] for row in A]
    nr = len(M)
    nc = len(M[0]) if nr else 0
    out = []
    r0 = 0
    for _ in range(min(nr, nc)):
        best = None
        for i in range(r0, nr):
            for j in range(r0, nc):
                if M[i][j]:
                    v = _val(M[i][j], p, m)
                    if best is None or v < best[0]:
                        best = (v, i, j)
                        if v == 0:
                            break
            if best and best[0] == 0:
                break
        if best is None:
            break
        v, i, j = best
        M[r0], M[i] = M[i], M[r0]
        for row in M:
            row[r0], row[j] = row[j], row[r0]
        piv = M[r0][r0]
        unit = pow(piv // p**v, -1, mod)
        M[r0] = [x * unit % mod for x in M[r0]]  # pivot = p^v
        pv = p**v
        for i2 in range(nr):
            if i2 != r0 and M[i2][r0]:
                f = M[i2][r0] // pv  # divisible: v minimal
                M[i2] = [(x - f * y) % mod for x, y in zip(M[i2], M[r0])]
        for j2 in range(r0 + 1, nc):
            if M[r0][j2]:
                f = M[r0][j2] // pv
                for i2 in range(nr):
                    M[i2][j2] = (M[i2][j2] - f * M[i2][r0]) % mod
        out.append(v)
        r0 += 1
    return sorted(out)


def rank_mod_p(A, p: int) -> int:
    return sum(1 for v in elementary_divisors(A, p, 1) if v == 0)


def image_basis(P, p: int, mod: int):
    """Columns of the idempotent ``P`` independent mod ``p``; they form a basis of the free module ``P V``."""
    n = len(P)
    chosen, red = [], []  # red: echelon rows mod p of chosen columns
    piv_of = []
    for j in range(n):
        v = [P[i][j] % p for i in range(n)]
        for (pc, r) in zip(piv_of, red):
            if v[pc]:
                f = v[pc]
                v = [(x - f * y) % p for x, y in zip(v, r)]
        nz = next((i for i in range(n) if v[i]), None)
        if nz is None:
            continue
        inv = pow(v[nz], -1, p)
        v = [x * inv % p for x in v]
        red.append(v)
        piv_of.append(nz)
        chosen.append([P[i][j] % mod for i in range(n)])
    return chosen  # list of column vectors


class _Coords:
    """Coordinates w.r.t. a basis (columns independent mod ``p``) of a free direct summand of ``(Z/p^m)^n``."""

    def __init__(self, basis, p: int, mod: int):
        self.basis, self.p, self.mod = basis, p, mod
        r = len(basis)
        n = len(basis[0]) if r else 0
        self.r = r
        # pick r rows with an invertible minor mod p
        rows = []
        cur = []
        for i in range(n):
            cand = cur + [[basis[j][i] for j in range(r)]]
            if rank_mod_p(cand, p) == len(cand):
                cur, rows = cand, rows + [i]
            if len(rows) == r:
                break
        assert len(rows) == r
        self.rows = rows
        self.Ainv = _inv_mod([[basis[j][i] for j in range(r)] for i in rows], p, mod) if r else []

    def __call__(self, w):
        if self.r == 0:
            assert all(x % self.mod == 0 for x in w), "vector not in the (zero) summand"
            return []
        c = [sum(self.Ainv[a][b] * w[self.rows[b]] for b in range(self.r)) % self.mod for a in range(self.r)]
        recon = [sum(c[j] * self.basis[j][i] for j in range(self.r)) % self.mod for i in range(len(w))]
        assert recon == [x % self.mod for x in w], "vector not in the summand"
        return c


def _inv_mod(A, p: int, mod: int):
    n = len(A)
    M = [[x % mod for x in A[i]] + [int(i == j) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] % p)
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], -1, mod)
        M[col] = [x * inv % mod for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [(x - f * y) % mod for x, y in zip(M[r], M[col])]
    return [row[n:] for row in M]


def projector(H, n: int, p: int, mod: int):
    """``e_H = |H|^{-1} sum_{h in H} Sym^n(h)`` (``H`` a list of 2x2 matrices mod ``mod``, ``p`` not dividing ``|H|``)."""
    d = n + 1
    S = [[0] * d for _ in range(d)]
    for h in H:
        R = sym(h, n, mod)
        for i in range(d):
            for j in range(d):
                S[i][j] += R[i][j]
    inv = pow(len(H), -1, mod)
    return [[x * inv % mod for x in row] for row in S]


# ---------------------------------------------------------------- tree data with transport elements
@dataclass
class CellData:
    c: int
    pt: tuple
    H_units: list  # O_c-coordinates of the units of O_c fixing pt (= Gamma_x, including -1 if -1 in U'')


@dataclass
class EdgeTwist:
    """Transport data of one edge (see module docstring): ``u_0 = phi_c(eps0)``, ``u_1 = phi_{c'}(eps1) T``."""

    v0: int
    v1: int
    eps0: list  # O_c coordinates (the true eps, pt(eps y) = rep)
    eps1: list  # O_{c'} coordinates
    g: tuple    # q L_{y alpha} = I_{c'} g  (algebra element)
    c: int
    c1: int


@dataclass
class TwoTermData:
    D: int
    q: int
    level: tree.Level
    T: tree.TreeQuotient
    verts: list[CellData]
    edges: list[CellData]
    tw: list[EdgeTwist]
    _b: object = field(repr=False, default=None)

    @property
    def free(self) -> bool:
        return all(len(c.H_units) == 1 for c in self.verts + self.edges)


class _TwistBuilder(tree._Builder):
    """tree.py's builder plus the elements ``g``, ``eps0``, ``eps1`` (recomputed; tree.py is not modified)."""

    def transport_gamma(self, c: int, lam: tuple):
        key = ("g", c, lam)
        if key in self._trans:
            return self._trans[key]
        B, loc, q = self.cd.B, self.loc, self.q
        I, N = self.cd.reps[c]
        wq = loc.preimage(c, lam, q)
        v = B.mul(loc.e0(q), wq)
        qL = Lattice([tuple(q * x for x in b) for b in I.basis] + [B.mul(o, v) for o in B.O.basis])
        for c2, (J, NJ) in enumerate(self.cd.reps):
            g = tree._find_gamma(B, J, NJ, qL, N * q)
            if g is not None:
                self._trans[key] = (c2, g)
                return c2, g
        raise AssertionError("q-neighbour lies in no known class")

    def conj_coords(self, c: int, u):
        cd = self.cd
        R = cd.orders[c]
        x = tuple(sum(Fraction(u[i]) * R.basis[i][k] for i in range(4)) for k in range(4))
        return cd.struct(c)[1](cd.B.conj(x))

    def normaliser(self, c: int, pt: tuple, X: XB):
        """``(rep index, eps)`` with ``pt . phi_c(eps)^{-1} = rep`` (``eps`` true element, O_c coordinates)."""
        cd, N1, N0 = self.cd, X.N1, X.N0
        k = X.orbit_of[c][pt]
        rep = X.orbits[c][k]["rep"]
        for u in cd.units(c):
            if _act(pt, cd.phi(c, u, N1), cd.phi(c, u, N0), N1, N0) == rep:
                # pt . phi(u) = rep, so eps = u^{-1} = conj(u)
                return k, self.conj_coords(c, u)
        raise AssertionError("no normalising unit")

    def stab_units(self, c: int, pt: tuple, X: XB):
        cd, N1, N0 = self.cd, X.N1, X.N0
        return [u for u in cd.units(c) if _act(pt, cd.phi(c, u, N1), cd.phi(c, u, N0), N1, N0) == pt]


@lru_cache(maxsize=None)
def tree_data(D: int, q: int, N1: int = 1, N0: int = 1) -> TwoTermData:
    level = tree.Level(N1, N0)
    b = _TwistBuilder(D, q, level, check=False)
    T = b.build()
    XU, XE = b.XU, b.XE
    verts = [CellData(v.c, v.pt, b.stab_units(v.c, v.pt, XU)) for v in T.vertices0]
    edges = [CellData(e.c, e.pt, b.stab_units(e.c, e.pt, XE)) for e in T.edges]
    for cell, tc in zip(verts + edges, T.vertices0 + T.edges):
        assert len(cell.H_units) == tc.stab
    vidx = {(v.c, v.pt): i for i, v in enumerate(T.vertices0)}
    tw = []
    for k, e in enumerate(T.edges):
        c0, p0 = b.s0_point(e.c, e.pt)
        k0, eps0 = b.normaliser(c0, p0, XU)
        c1, p1 = b.s1_point(e.c, e.pt)
        k1, eps1 = b.normaliser(c1, p1, XU)
        v0 = vidx[(c0, XU.orbits[c0][k0]["rep"])]
        v1 = vidx[(c1, XU.orbits[c1][k1]["rep"])]
        assert (v0, v1) == (T.s0[k], T.s1[k]), "endpoints disagree with tree.py"
        lq = b._split_line(e.pt[1])[1]
        c1b, g = b.transport_gamma(e.c, lq)
        assert c1b == c1
        tw.append(EdgeTwist(v0, v1, eps0, eps1, g, e.c, c1))
    return TwoTermData(D, q, level, T, verts, edges, tw, b)


# ---------------------------------------------------------------- local model at p
class LocalModel:
    """The two-term complex over ``Z/p^m`` with ``V = Sym^n((Z/p^m)^2)``, ``n = k - 2`` (``m <= 8``)."""

    def __init__(self, td: TwoTermData, p: int, m: int):
        assert p >= 5 and td.D % p and (td.level.N1 * td.level.N0 * td.q) % p and m <= PREC
        self.td, self.p, self.m, self.mod = td, p, m, p**m
        b, cd, mod = td._b, td._b.cd, p**m
        loc = b.loc
        ph = lambda c, u: (lambda t: ((t[0], t[1]), (t[2], t[3])))(cd.phi(c, u, mod))
        self.Hv = [[ph(v.c, u) for u in v.H_units] for v in td.verts]
        self.He = [[ph(e.c, u) for u in e.H_units] for e in td.edges]
        self.u0, self.u1, self.Tmat = [], [], []
        q, B = td.q, cd.B
        for tw in td.tw:
            g = tw.g
            ng = B.nrd(g)
            ginv = tuple(x / ng for x in B.conj(g))
            rows = []
            for r in ((1, 0), (0, 1)):
                w = loc.preimage(tw.c, r, mod)
                w2 = B.mul(tuple(q * x for x in w), ginv)
                rows.append(loc.psi_mod(tw.c1, w2, mod))
            Ginv = (tuple(rows[0]), tuple(rows[1]))  # r -> r G, G = T^{-1}
            Tm = mat_inv2(Ginv, mod)
            self.Tmat.append(Tm)
            self.u0.append(ph(tw.c, tw.eps0))
            self.u1.append(_mm(ph(tw.c1, tw.eps1), Tm, mod))
        self._check_conjugation()

    def _check_conjugation(self):
        mod = self.mod
        for k, tw in enumerate(self.td.tw):
            for u, v in ((self.u0[k], tw.v0), (self.u1[k], tw.v1)):
                Hv = set(self.Hv[v])
                ui = mat_inv2(u, mod)
                for h in self.He[k]:
                    assert _mm(_mm(u, h, mod), ui, mod) in Hv, "u H_e u^{-1} not in H_v"

    # -- norm maps (prop:s02-Mhomprops (b), (d)): N_x = sum over H_x / (H_x cap +-1)
    def _mod_pm(self, H):
        mod = self.mod
        neg = ((mod - 1, 0), (0, mod - 1))
        seen, out = set(), []
        for h in H:
            if h in seen:
                continue
            out.append(h)
            seen.add(h)
            seen.add(_mm(neg, h, mod))
        return out

    def norm_trace_check(self, n: int) -> dict:
        """Index-factor identities of ``prop:s02-Mhomprops`` on every edge and both ``j`` (matrices on ``V``):

        * (d) ``nu_U s_{j*} = tr_j nu_{U'}`` (no index factor), ``tr_j`` in representatives
          ``(tr_j f)(x) = sum_{e: s_j e = x} sum_{h in H_x / u H_e u^{-1}} h u f(e)``;
        * (e) ``nu_{U'} s_j^! = s_j^* nu_U`` with the transfer in representatives
          ``s_j^!([x] (x) v) = sum_{e: s_j e = x} sum_{h in H_x / u H_e u^{-1}} [e] (x) u^{-1} h^{-1} v``
          (``[Gamma_x : Gamma_e]`` terms per edge) and ``(s_j^* F)(e) = u^{-1} F(x)``;
        * ``naive_transfer_violations``: how often the multiplicity-free fibre sum ``s_j^sharp`` (only ``h = 1``)
          violates (e); it is ``0`` iff all indices ``[Gamma_x : Gamma_e]`` are ``1`` (e.g. free levels).

        ``N_x = sum_{H_x / (H_x cap +-1)}`` (the ``Gamma_x/+-1`` convention); ``epsilon = |{+-1} cap U''|`` is asserted
        common to vertices and edges.  Requires ``n`` even or ``-1 notin H`` (otherwise the halved sum is not defined)."""
        mod = self.mod
        neg = ((mod - 1, 0), (0, mod - 1))
        Nmat = lambda H: [[sum(col) % mod for col in zip(*rows)] for rows in zip(*[sym(h, n, mod) for h in H])]
        add = lambda A, B: [[(a + b) % mod for a, b in zip(r1, r2)] for r1, r2 in zip(A, B)]
        ok_d = ok_e = True
        naive_bad = 0
        for k, tw in enumerate(self.td.tw):
            He = self.He[k]
            for u, v in ((self.u0[k], tw.v0), (self.u1[k], tw.v1)):
                Hv = self.Hv[v]
                assert (neg in set(Hv)) == (neg in set(He)), "epsilon = |{+-1} cap U''| not common"
                assert n % 2 == 0 or neg not in set(Hv), "N_x over H/+-1 needs -1 to act trivially"
                ui = mat_inv2(u, mod)
                conj = {_mm(_mm(u, h, mod), ui, mod) for h in He}
                reps, cov = [], set()
                for h in Hv:
                    if h not in cov:
                        reps.append(h)
                        cov |= {_mm(h, c, mod) for c in conj}
                assert len(reps) * len(He) == len(Hv)
                Nv, Ne = Nmat(self._mod_pm(Hv)), Nmat(self._mod_pm(He))
                Su, Sui = sym(u, n, mod), sym(ui, n, mod)
                zero = [[0] * (n + 1) for _ in range(n + 1)]
                # (d)
                rhs = zero
                for h in reps:
                    rhs = add(rhs, mat_mul(mat_mul(sym(h, n, mod), Su, mod), Ne, mod))
                ok_d = ok_d and mat_mul(Nv, Su, mod) == rhs
                # (e)
                lhs = zero
                for h in reps:
                    lhs = add(lhs, mat_mul(mat_mul(Ne, Sui, mod), sym(mat_inv2(h, mod), n, mod), mod))
                target = mat_mul(Sui, Nv, mod)
                ok_e = ok_e and lhs == target
                if mat_mul(Ne, Sui, mod) != target:
                    naive_bad += 1
        return {"pushforward_identity_d": ok_d, "transfer_identity_e": ok_e, "naive_transfer_violations": naive_bad}

    # -- modules
    def summands(self, n: int):
        p, mod = self.p, self.mod
        bv = [image_basis(projector(H, n, p, mod), p, mod) for H in self.Hv]
        be = [image_basis(projector(H, n, p, mod), p, mod) for H in self.He]
        return bv, be

    def boundary(self, n: int, signs=(-1, 1)):
        """Matrix of ``d = (sgn0 s_{0*}, sgn1 s_{1*})`` in the bases ``e_H V``; rows: type-0 then type-1 vertices."""
        mod, p = self.mod, self.p
        td = self.td
        bv, be = self.summands(n)
        Pv = [projector(H, n, p, mod) for H in self.Hv]
        cv = [_Coords(B_, p, mod) for B_ in bv]
        X = len(bv)
        off = [0]
        for B_ in bv + bv:
            off.append(off[-1] + len(B_))
        coff = [0]
        for B_ in be:
            coff.append(coff[-1] + len(B_))
        A = [[0] * coff[-1] for _ in range(off[-1])]
        for k, tw in enumerate(td.tw):
            for j, (u, v) in enumerate(((self.u0[k], tw.v0), (self.u1[k], tw.v1))):
                S = sym(u, n, mod)
                for a, col in enumerate(be[k]):
                    w = [sum(S[i][t] * col[t] for t in range(n + 1)) % mod for i in range(n + 1)]
                    w = [sum(Pv[v][i][t] * w[t] for t in range(n + 1)) % mod for i in range(n + 1)]
                    co = cv[v](w)
                    r0 = off[j * X + v]
                    for i, x in enumerate(co):
                        A[r0 + i][coff[k] + a] = (A[r0 + i][coff[k] + a] + signs[j] * x) % mod
        return A, off[-1], coff[-1]

    def coboundary(self, n: int, dual: bool = False):
        """Matrix of ``delta(f0, f1) = s_1^* f1 - s_0^* f0`` on invariants ``V^H = e_H V``; columns: f0 then f1.

        ``dual=True``: coefficients ``V^* = Hom(V, Z/p^m)`` (contragredient, dual basis), where ``u^{-1}`` acts by the
        transpose of ``Sym^n(u)``; only implemented for trivial stabilisers (free levels)."""
        mod, p = self.mod, self.p
        td = self.td
        bv, be = self.summands(n)
        ce = [_Coords(B_, p, mod) for B_ in be]
        X = len(bv)
        off = [0]
        for B_ in bv + bv:
            off.append(off[-1] + len(B_))
        roff = [0]
        for B_ in be:
            roff.append(roff[-1] + len(B_))
        A = [[0] * off[-1] for _ in range(roff[-1])]
        for k, tw in enumerate(td.tw):
            for j, (u, v, sg) in enumerate(((self.u0[k], tw.v0, -1), (self.u1[k], tw.v1, 1))):
                if dual:
                    assert all(len(H) == 1 for H in self.Hv + self.He), "dual coboundary only at free levels"
                    S = [list(r) for r in zip(*sym(u, n, mod))]
                else:
                    S = sym(mat_inv2(u, mod), n, mod)
                for a, col in enumerate(bv[v]):
                    w = [sum(S[i][t] * col[t] for t in range(n + 1)) % mod for i in range(n + 1)]
                    co = ce[k](w)  # u^{-1} f lies in V^{H_e}
                    c0 = off[j * X + v]
                    for i, x in enumerate(co):
                        A[roff[k] + i][c0 + a] = (A[roff[k] + i][c0 + a] + sg * x) % mod
        return A, roff[-1], off[-1]

    def homology(self, k: int) -> dict:
        n = k - 2
        m = self.m
        A, r0, r1 = self.boundary(n)
        ed = elementary_divisors(A, self.p, m) if r0 and r1 else []
        s = len(ed)
        tors = [v for v in ed if v > 0]
        C, c1, c0 = self.coboundary(n)
        edc = elementary_divisors(C, self.p, m) if c1 and c0 else []
        sc = len(edc)
        return {
            "rank_C1": r1, "rank_C0": r0,  # rk M(U'; V_k), 2 rk M(U; V_k)
            "rank_M_U": r0 // 2, "rank_M_Uprime": r1,
            "elem_div_vals_d": ed,
            # Z/p^m-module structure: list of exponents e meaning Z/p^e
            "H1": [m] * (r1 - s) + tors, "H0": [m] * (r0 - s) + tors,
            "Hco0": [m] * (c0 - sc) + [v for v in edc if v > 0], "Hco1": [m] * (c1 - sc) + [v for v in edc if v > 0],
            "rank_d_Qp_lower": s,  # elementary divisors of valuation < m: a lower bound for rk_{Q_p} d
            "rank_H1_Zp_upper": r1 - s, "rank_H0_Zp_upper": r0 - s,
            "rank_Hco0_Zp_upper": c0 - sc,
        }


def _mm(x, y, m):
    return tuple(tuple(sum(x[i][k] * y[k][j] for k in range(2)) % m for j in range(2)) for i in range(2))


# ---------------------------------------------------------------- global model (Gross form) mod a split prime of K
class BasisMismatch(Exception):
    """PARI's ``alginit`` is randomised; :mod:`symn` and :mod:`levels` may hold different bases (then no global model)."""


class GlobalModel:
    """The same complex with ``B^x`` acting through the exact splitting ``s`` of :mod:`symn`, reduced mod ``ell``."""

    def __init__(self, td: TwoTermData, ell: int | None = None):
        from . import symn

        SA = symn.split_algebra(td.D)
        cd = td._b.cd
        if SA.B.C != cd.B.C:
            raise BasisMismatch("symn and levels use different alginit bases")
        a = SA.a
        if ell is None:
            ell = next(l for l in range(1_000_003, 2_000_000, 2)
                       if all(l % d for d in range(3, int(l**0.5) + 1, 2)) and pow(a % l, (l - 1) // 2, l) == 1)
        self.ell = ell
        self.sqa = next(s for s in range(ell) if (s * s - a) % ell == 0) if ell < 10**5 else _sqrt_mod(a % ell, ell)
        self.SA, self.td = SA, td
        red = lambda x: (x.r.numerator * pow(x.r.denominator, -1, ell) + self.sqa * x.s.numerator *
                         pow(x.s.denominator, -1, ell)) % ell
        self._red = red

        def s_of(c, u):
            R = cd.orders[c]
            x = tuple(sum(Fraction(u[i]) * R.basis[i][k] for i in range(4)) for k in range(4))
            return self.s_elt(x)

        self.Hv = [[s_of(v.c, u) for u in v.H_units] for v in td.verts]
        self.He = [[s_of(e.c, u) for u in e.H_units] for e in td.edges]
        qi = pow(td.q, -1, ell)
        self.u0 = [s_of(tw.c, tw.eps0) for tw in td.tw]
        self.u1 = []
        for tw in td.tw:
            sg = self.s_elt(tw.g)
            sg = tuple(tuple(x * qi % ell for x in row) for row in sg)
            self.u1.append(_mm(s_of(tw.c1, tw.eps1), sg, ell))

    def s_elt(self, x):
        M = self.SA.split(x)
        return tuple(tuple(self._red(e) for e in row) for row in M)

    def rank_d(self, k: int) -> tuple[int, int, int]:
        """``(rk_{F_ell} d, rk C_1, rk C_0)`` -- uses :class:`LocalModel`'s assembly with ``p = ell``, ``m = 1``."""
        lm = LocalModel.__new__(LocalModel)
        lm.td, lm.p, lm.m, lm.mod = self.td, self.ell, 1, self.ell
        lm.Hv, lm.He, lm.u0, lm.u1 = self.Hv, self.He, self.u0, self.u1
        lm._check_conjugation()
        A, r0, r1 = lm.boundary(k - 2)
        return (rank_mod_p(A, self.ell) if r0 and r1 else 0), r1, r0


def _sqrt_mod(a: int, p: int) -> int:
    """Tonelli--Shanks."""
    if a == 0:
        return 0
    qq, s = p - 1, 0
    while qq % 2 == 0:
        qq //= 2
        s += 1
    z = next(z for z in range(2, p) if pow(z, (p - 1) // 2, p) == p - 1)
    M, c, t, R = s, pow(z, qq, p), pow(a, qq, p), pow(a, (qq + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (M - i - 1), p)
        M, c, t, R = i, b * b % p, t * b * b % p, R * b % p
    return R


# ---------------------------------------------------------------- trivial coefficients: exact over Z
def boundary_Z(td: TwoTermData, signs=(-1, 1)):
    """``d`` for ``V = Z`` (all ``H_x`` act trivially): ``[e] -> (sgn0 [s_0 e], sgn1 [s_1 e])``; ``(2X) x E``."""
    X, E = td.T.X, td.T.E
    A = [[0] * E for _ in range(2 * X)]
    for k, (a, b) in enumerate(zip(td.T.s0, td.T.s1)):
        A[a][k] += signs[0]
        A[X + b][k] += signs[1]
    return A


def coboundary_Z(td: TwoTermData):
    """``delta(f0, f1)(e) = f1(s_1 e) - f0(s_0 e)``; ``E x (2X)``."""
    X, E = td.T.X, td.T.E
    A = [[0] * (2 * X) for _ in range(E)]
    for k, (a, b) in enumerate(zip(td.T.s0, td.T.s1)):
        A[k][a] -= 1
        A[k][X + b] += 1
    return A


# ---------------------------------------------------------------- predictions
def _is_prime(n: int) -> bool:
    return n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))


def mf_new_dim(N: int, k: int) -> int:
    from .pari import get_pari
    pari = get_pari()
    return int(pari.mfdim([N, k], 0))


def _gamma1_dim(Dq: int, l: int, k: int) -> int:
    """``sum_{chi mod l, chi(-1) = (-1)^k} sum_{M | l, cond chi | M} sigma_0(l/M) dim S_k(Dq M, chi)^new`` (``l`` prime)."""
    from .pari import get_pari
    pari = get_pari()
    G = pari(f"znstar({l}, 1)")
    tot = 0
    for a in range(1, l):
        if gcd(a, l) != 1:
            continue
        if int(pari.zncharisodd(G, a)) != k % 2:
            continue
        for M in (1, l):
            if a != 1 and M == 1:
                continue
            chi = pari(f"Mod({a}, {l})") if a != 1 else None
            d = int(pari.mfdim([Dq * M, k, chi], 0)) if chi is not None else int(pari.mfdim([Dq * M, k], 0))
            tot += (2 if M == 1 else 1) * d
    return tot


def case(D: int, q: int, N1: int, N0: int, p: int, m: int, ks, with_global: bool = True) -> dict:
    td = tree_data(D, q, N1, N0)
    lm = LocalModel(td, p, m)
    gm = None
    if with_global:
        try:
            gm = GlobalModel(td)
        except BasisMismatch:
            gm = None
    X, E = td.T.X, td.T.E
    out = {"D": D, "q": q, "level": str(td.level), "N1": N1, "N0": N0, "p": p, "m": m, "X": X, "E": E,
           "free": td.free, "minus_one_in_U": td.T.minus_one_in_U, "components": td.T.components(),
           "stab_v": td.T.stab_v, "stab_e": td.T.stab_e, "k": {}}
    out["global_model"] = bool(gm)
    if gm:
        out["ell"] = gm.ell
    for k in ks:
        h = lm.homology(k)
        r1, r0 = h["rank_C1"], h["rank_C0"]
        row = dict(h)
        if gm:
            rg, g1, g0 = gm.rank_d(k)
            assert (g1, g0) == (r1, r0), "global and local module ranks differ"
            row["rank_d_Fell"] = rg
        # certified Q_p-ranks: lower bound L = max(local, global) for rk d; upper bound r0 (k > 2) or r0 - comps (k = 2)
        lower = max(h["rank_d_Qp_lower"], row.get("rank_d_Fell", 0))
        upper = min(r1, r0 - (out["components"] if (k == 2 and r0) else 0))
        if lower > upper:
            raise AssertionError(f"rank bounds inconsistent: lower {lower} > upper {upper} ({D},{q},{N1},{N0},k={k})")
        row["rank_d_certified"] = lower if lower == upper else None
        if lower == upper:
            row["rank_H1"], row["rank_H0"] = r1 - lower, r0 - lower
        # R6: only the p-part is computed; H_0 over Z_p is determined by the exponents iff no divisor reached p^m
        row["H0_p_part_exact"] = all(v < m - 1 for v in h["elem_div_vals_d"])
        row["p_le_k_minus_2"] = p <= k - 2
        if k > 2:
            row["pred_free_rank_H1"] = (q - 1) * (k - 1) * X if td.free else None
            row["pred_coh_d_rank_H1"] = r1 - r0  # prop:s02-coh (d): rk M(U') - 2 rk M(U)
        else:
            row["pred_free_rank_H1"] = E - 2 * X + out["components"]
        if N0 == 1 and N1 > 2 and _is_prime(N1):
            # U = U_1(l), l prime: sum over Dirichlet chi mod l with chi(-1) = (-1)^k of the forms of level
            # D q M (M | l, cond chi | M), new at D q, with multiplicity sigma_0(l/M) (JL with nebentypus)
            row["pred_rank_H1_JL"] = _gamma1_dim(D * q, N1, k)
            row["pred_rank_M_U"] = _gamma1_dim(D, N1, k) + (k == 2)
        if N1 == 1 and N0 > 1 and _is_prime(N0) and k % 2 == 0:
            # U = U_0(N0), N0 prime: q-new forms of level D q N0 that are new at D q: new(DqN0) + 2 new(Dq)
            row["pred_rank_H1_JL"] = mf_new_dim(D * q * N0, k) + 2 * mf_new_dim(D * q, k)
        if N1 == 1 and N0 == 1 and k % 2 == 0:
            # Brandt-module ranks via JL (S01): rk M(O^x; V_k) = dim S_k(D)^new + [k=2]; edge level U_0(q):
            # rk M(U_0(q); V_k) = dim S_k(Dq)^new + 2 dim S_k(D)^new + [k=2]; q-new part = dim S_k(Dq)^new.
            sD, sDq = mf_new_dim(D, k), mf_new_dim(D * q, k)
            row["pred_rank_M_U"] = sD + (k == 2)
            row["pred_rank_M_Uprime"] = sDq + 2 * sD + (k == 2)
            row["pred_rank_H1_JL"] = sDq
        out["k"][str(k)] = row
    return out


CASES = [
    # (D, q, N1, N0, p, m)  free levels
    (3, 2, 5, 1, 7, 4), (3, 2, 7, 1, 5, 4), (2, 3, 7, 1, 5, 4), (3, 2, 13, 1, 5, 3),
    # non-free: U = O^x
    (2, 3, 1, 1, 5, 4), (2, 5, 1, 1, 7, 4), (2, 7, 1, 1, 5, 4), (3, 2, 1, 1, 5, 4), (3, 5, 1, 1, 7, 4),
    (3, 7, 1, 1, 5, 4), (5, 2, 1, 1, 7, 4), (7, 2, 1, 1, 5, 4), (13, 2, 1, 1, 5, 4),
    # non-free with level: U_0(N)
    (2, 3, 1, 5, 7, 4), (3, 2, 1, 7, 5, 4),
]
KS_ALL = tuple(range(2, 11))


def compute_all() -> dict:
    cases = []
    for c in CASES:
        r = case(*c, KS_ALL)
        lm = LocalModel(tree_data(*c[:4]), c[4], c[5])
        r["norm_trace"] = {str(n + 2): lm.norm_trace_check(n) for n in (0, 2, 4)}
        cases.append(r)
    acc = []
    for r in cases:
        for k, row in r["k"].items():
            k = int(k)
            pred = row.get("pred_free_rank_H1") if r["free"] else row.get("pred_rank_H1_JL")
            if pred is None and k > 2:
                pred = row.get("pred_coh_d_rank_H1")
            acc.append({"D": r["D"], "q": r["q"], "level": r["level"], "k": k, "rank_H1": row.get("rank_H1"),
                        "pred": pred, "pred_JL": row.get("pred_rank_H1_JL"),
                        "ok": (row.get("rank_H1") == pred if pred is not None else None) if
                        row.get("pred_rank_H1_JL") is None else
                        (row.get("rank_H1") == row["pred_rank_H1_JL"] and (pred is None or row.get("rank_H1") == pred)),
                        "H0_rank0": (row.get("rank_H0") == 0) if k > 2 else None,
                        "Hco0_rank0": (row["rank_Hco0_Zp_upper"] == 0) if k > 2 else None})
    return {"cases": cases, "acceptance": acc,
            "all_ok": all(a["ok"] is not False and a["H0_rank0"] is not False and a["Hco0_rank0"] is not False
                          for a in acc)}


def main() -> None:
    with results.Timer() as t:
        data = compute_all()
    path = results.write("s02/H_Vk.json", data, script="code/python/langlandscape/twoterm.py",
                         params={"cases": CASES, "ks": KS_ALL}, runtime_s=round(t.seconds, 2),
                         notes="S02-C5: H_*(Gamma_U, V_k) via d = (-s_{0*}, s_{1*}) (prop:s02-coh (b)); "
                               "module structures over Z/p^m as exponent lists; ranks certified by local SNF + "
                               "global model mod ell + trivial bound min(r1, r0) (minus components at k = 2); "
                               "only the p-part (one p per case) is computed; base sha " + results.git_commit())
    print(path)


if __name__ == "__main__":
    main()
