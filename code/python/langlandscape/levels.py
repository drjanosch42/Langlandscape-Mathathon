"""S01-C2: class sets at U_0(M), U_1(N), U_0(q)U via fibres Gamma_x \\ (U / U'); mass level change; the p-tower S_s.

Tex labels (plan/staged/stage-01-quaternion-foundations.tex): def:s01-B, def:s01-levels, lem:s01-nrd, prop:s01-eichler,
def:s01-classset, prop:s01-finite, lem:s01-stab, thm:s01-mass, ex:s01-masschecks.

Setting.  ``U = \\hat O^x`` and ``U' = U_1(N1) cap U_0(N0)`` with ``gcd(N1, N0) = 1`` and ``gcd(N1 N0, D) = 1``
(``U_0(M)``: ``N1 = 1, N0 = M``; ``U_1(N)``: ``N1 = N, N0 = 1``; ``U_0(q)U_1(N)``: ``N1 = N, N0 = q``).
``X_B(U') = disjoint union over x in X_B(U) of Gamma_x \\ (U/U')``, ``Gamma_x = O_x^x`` (def:s01-classset, prop:s01-finite).

Conventions (derived from def:s01-levels: lower row of ``U_1(N)`` is ``(0,1)``, ``U_0(N)``: ``c = 0``).
* ``x`` runs over the left ideal classes of ``O`` (C1), ``O_x := O_r(I_x)`` the right order; ``Gamma_x = O_x^x`` (nrd 1).
  (The class sets of left ideals of ``O`` and of right ideals correspond by ``I -> conj(I)``; this swaps left/right
  orders only and preserves class numbers, unit groups and all counts below.)
* ``phi_x : O_x -> M_2(Z/N)`` is the reduction of an iso ``O_x (x) Z_N ~ M_2(Z_N)`` obtained from a Hensel-lifted idempotent
  ``e`` (``e^2 = e``, rank one mod each prime): ``O_x e`` is free of rank 2 over ``Z/l^K`` and ``phi_x(r)`` is the matrix of
  *left* multiplication by ``r`` on it, so ``phi_x(rs) = phi_x(r) phi_x(s)`` and ``det phi_x = nrd`` (both asserted).
  Another splitting differs by conjugation by ``g in GL_2(Z/N)``; ``h U' -> g h U'`` is a bijection of the orbit sets.
* ``Gamma_x`` acts on ``U/U' = GL_2(Z/N)/U'_N`` from the left, ``gamma . hU' = phi(gamma) h U'``, compatible with the right
  action ``x -> xu``.  Since ``U_1`` is the stabiliser of the row vector ``(0,1)`` under ``v -> v u``, the coset ``hU_1``
  corresponds to the primitive row vector ``v = (0,1) h^{-1}`` and ``gamma`` acts by ``v -> v phi(gamma)^{-1}``;
  likewise for ``U_0`` with ``P^1(Z/N)`` (lines ``(0,1)h^{-1}`` up to units).  Orbits are the orbits of the group
  ``phi(Gamma_x)`` acting on the right on row vectors (resp. lines).
* ``|Gamma_{x'}|`` of the orbit of ``hU'`` is the stabiliser of the coset in ``Gamma_x``; ``w_{x'} = |Gamma_{x'}/(Gamma_{x'} cap +-1)|``.
* Tower: ``S_s = X_B(U_1(M p^s))``, one splitting mod ``p^K`` (``K = 8``) reduced to ``p^s``, so the projection
  ``S_s -> S_{s-1}`` is ``v -> v mod M p^{s-1}``.  The diamond ``Delta_s``, ``[x] -> [x iota_p^{-1} diag(1,d)]`` sends ``hU -> h diag(1,d) U``,
  i.e. ``v -> d^{-1} v`` (``d`` mod ``p^s``, identity mod ``M``).

Run ``python -m langlandscape.levels`` to write ``code/results/s01/levels.json``.
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from functools import lru_cache
from math import gcd

from flint import fmpq, fmpq_mat

from . import results
from .quat import DefiniteAlgebra, Lattice, prime_factors

PREC = 8  # l-adic precision of the splittings


def _factor(n: int) -> dict[int, int]:
    out = {}
    for p in prime_factors(n):
        k = 0
        while n % p == 0:
            n //= p
            k += 1
        out[p] = k
    return out


def phi_fn(n: int) -> int:
    r = 1
    for p, k in _factor(n).items():
        r *= (p - 1) * p ** (k - 1)
    return r


def psi_fn(n: int) -> int:
    r = n
    for p in prime_factors(n):
        r = r // p * (p + 1)
    return r


def _crt(residues: list[tuple[int, int]]) -> int:
    x, m = 0, 1
    for r, q in residues:
        t = ((r - x) * pow(m, -1, q)) % q if q > 1 else 0
        x, m = x + m * t, m * q
    return x % m


# ---------------------------------------------------------------- algebra data per class

class ClassData:
    """Class set of ``O`` (C1 algorithm) with, per class, the order ``O_x``, its units and the splittings."""

    def __init__(self, D: int):
        self.B = B = DefiniteAlgebra(D)
        self.D = D
        reps = [(B.O, 1)]
        queue = [0]
        while queue:
            I, N = reps[queue.pop(0)]
            for J, NJ in B.neighbours(I, N):
                if not any(B.equivalent(R, NR, J, NJ) for R, NR in reps):
                    reps.append((J, NJ))
                    queue.append(len(reps) - 1)
        self.reps = reps
        self.orders = [B.right_order(I, N) for I, N in reps]
        self.h = len(reps)
        self._struct, self._units, self._split = {}, {}, {}

    # structure constants of O_x in its HNF basis
    def struct(self, c: int):
        if c not in self._struct:
            B, R = self.B, self.orders[c]
            q = lambda t: fmpq(t.numerator, t.denominator)
            M = fmpq_mat(4, 4, [q(R.basis[j][i]) for i in range(4) for j in range(4)])
            Minv = M.inv()

            def to_coords(y):
                s = Minv * fmpq_mat(4, 1, [q(Fraction(t)) for t in y])
                assert all(s[i, 0].q == 1 for i in range(4)), "element not in lattice"
                return [int(s[i, 0].p) for i in range(4)]

            cst = [[to_coords(B.mul(R.basis[i], R.basis[j])) for j in range(4)] for i in range(4)]
            self._struct[c] = (cst, to_coords)
        return self._struct[c]

    def mul(self, c: int, x, y, m: int | None = None):
        cst, _ = self.struct(c)
        out = [0] * 4
        for i in range(4):
            if x[i] == 0:
                continue
            for j in range(4):
                f = x[i] * y[j]
                if f:
                    for k in range(4):
                        out[k] += f * cst[i][j][k]
        return [t % m for t in out] if m else out

    def one(self, c: int):
        return self.struct(c)[1](self.B.one)

    def units(self, c: int) -> list[list[int]]:
        """All elements of ``O_x`` of reduced norm 1, as integer coordinate vectors (with ``-u``)."""
        if c not in self._units:
            from .pari import get_pari
            pari = get_pari()
            R = self.orders[c]
            G = self.B.gram(R)
            res = pari.qfminim(G, 2, 10**6, 0)
            cnt = int(res[0])
            vecs = res[2]
            half = [[int(vecs[i, j]) for i in range(4)] for j in range(int(pari.matsize(vecs)[1]))]
            allv = half + [[-t for t in v] for v in half]
            assert len(allv) == cnt == self.B.unit_count(*self.reps[c]), "unit enumeration mismatch"
            self._units[c] = allv
        return self._units[c]

    def minus_one(self, c: int) -> list[int]:
        return [-t for t in self.one(c)]

    # ---- splitting
    def splitting(self, c: int, l: int):
        """Basis images ``phi(r_i)`` (2x2 matrices mod ``l^PREC``) of ``O_x`` for a prime ``l`` not dividing ``D``."""
        key = (c, l)
        if key in self._split:
            return self._split[key]
        assert self.D % l, "splitting requires l not dividing D"
        K, m = PREC, l**PREC
        R = self.orders[c]
        B = self.B
        mulm = lambda x, y: self.mul(c, x, y, m)
        one = self.one(c)

        def alg(v):
            return tuple(sum(v[i] * R.basis[i][k] for i in range(4)) for k in range(4))

        e = None
        # idempotent mod l
        for v in itertools.product(range(l), repeat=4):
            a = alg(v)
            t, n = int(B.trd(a)), int(B.nrd(a))
            if l > 2:
                disc = (t * t - 4 * n) % l
                if disc == 0:
                    continue
                s = next((s for s in range(l) if (s * s - disc) % l == 0), None)
                if s is None:
                    continue
                r1, r2 = ((t + s) * pow(2, -1, l)) % l, ((t - s) * pow(2, -1, l)) % l
                inv = pow(r1 - r2, -1, l)
                cand = [((v[i] - r2 * one[i]) * inv) % l for i in range(4)]
            else:
                cand = list(v)
            sq = mulm(cand, cand)
            if [x % l for x in sq] == [x % l for x in cand] and any(x % l for x in cand) and \
               [x % l for x in cand] != [x % l for x in one]:
                e = cand
                break
        assert e is not None, "no idempotent found"
        for _ in range(5):  # Hensel: e -> 3e^2 - 2e^3
            e2 = mulm(e, e)
            e3 = mulm(e2, e)
            e = [(3 * a - 2 * b) % m for a, b in zip(e2, e3)]
        assert mulm(e, e) == [x % m for x in e]
        basis_unit = [[int(i == j) for j in range(4)] for i in range(4)]
        f = [mulm(basis_unit[i], e) for i in range(4)]  # r_i e, generate O e
        pick = None
        for i, j in itertools.combinations(range(4), 2):
            for a, b in itertools.combinations(range(4), 2):
                det = (f[i][a] * f[j][b] - f[i][b] * f[j][a]) % l
                if det:
                    pick = (i, j, a, b)
                    break
            if pick:
                break
        assert pick, "O e is not free of rank 2"
        i, j, a, b = pick
        b1, b2 = f[i], f[j]
        det = (b1[a] * b2[b] - b1[b] * b2[a]) % m
        di = pow(det, -1, m)
        # inverse of [[b1[a], b2[a]], [b1[b], b2[b]]]
        inv = [[b2[b] * di % m, -b2[a] * di % m], [-b1[b] * di % m, b1[a] * di % m]]

        def coords(y):  # y in O e, coordinates wrt (b1, b2)
            return (inv[0][0] * y[a] + inv[0][1] * y[b]) % m, (inv[1][0] * y[a] + inv[1][1] * y[b]) % m

        mats = []
        for r in basis_unit:
            cols = [coords(mulm(r, bj)) for bj in (b1, b2)]
            mats.append(((cols[0][0], cols[1][0]), (cols[0][1], cols[1][1])))
        self._split[key] = (mats, m)
        # consistency checks: ring hom on basis products, det = nrd
        cst, _ = self.struct(c)
        for p_ in range(4):
            for q_ in range(4):
                lhs = _mm(mats[p_], mats[q_], m)
                rhs = [[0, 0], [0, 0]]
                for k in range(4):
                    for u in range(2):
                        for w in range(2):
                            rhs[u][w] = (rhs[u][w] + cst[p_][q_][k] * mats[k][u][w]) % m
                assert [list(r) for r in lhs] == rhs, "splitting is not a ring homomorphism"
        for p_ in range(4):
            a_ = alg([int(i == p_) for i in range(4)])
            mm = mats[p_]
            assert (mm[0][0] * mm[1][1] - mm[0][1] * mm[1][0] - int(B.nrd(a_))) % m == 0, "det != nrd"
        return self._split[key]

    def phi(self, c: int, u, Q: int):
        """``phi_x(u)`` in ``M_2(Z/Q)`` for ``u`` in ``O_x`` (coordinates), ``gcd(Q, D) = 1``; tuple ``(a, b, c, d)``."""
        if Q == 1:
            return (0, 0, 0, 0)
        parts = []
        for l, k in _factor(Q).items():
            mats, m = self.splitting(c, l)
            q = l**k
            ent = [sum(u[i] * mats[i][r][s] for i in range(4)) % q for r in range(2) for s in range(2)]
            parts.append((ent, q))
        return tuple(_crt([(e[t], q) for e, q in parts]) for t in range(4))


def _mm(x, y, m):
    return tuple(tuple(sum(x[i][k] * y[k][j] for k in range(2)) % m for j in range(2)) for i in range(2))


@lru_cache(maxsize=None)
def class_data(D: int) -> ClassData:
    return ClassData(D)


# ---------------------------------------------------------------- point sets

def _units_mod(n: int) -> list[int]:
    return [u for u in range(1, max(n, 2)) if gcd(u, n) == 1] if n > 1 else [0]


@lru_cache(maxsize=None)
def prim_vectors(N: int) -> list[tuple[int, int]]:
    """Primitive row vectors of ``(Z/N)^2`` (= ``GL_2/U_1(N)``), N >= 2."""
    return [(a, b) for a in range(N) for b in range(N) if gcd(gcd(a, b), N) == 1]


def canon_line(v, N: int):
    return min(((u * v[0]) % N, (u * v[1]) % N) for u in _units_mod(N))


@lru_cache(maxsize=None)
def lines(N: int) -> list[tuple[int, int]]:
    return sorted({canon_line(v, N) for v in prim_vectors(N)})


def level_points(N1: int, N0: int) -> list[tuple]:
    """Points of ``GL_2(Z/N1 N0)/U'`` as pairs (primitive vector mod N1 or (), line mod N0 or ())."""
    V = prim_vectors(N1) if N1 > 1 else [()]
    L = lines(N0) if N0 > 1 else [()]
    return [(v, l) for v in V for l in L]


def _act(pt, g1, g0, N1: int, N0: int):
    v, l = pt
    if N1 > 1:
        a, b, c, d = g1
        v = ((v[0] * a + v[1] * c) % N1, (v[0] * b + v[1] * d) % N1)
    if N0 > 1:
        a, b, c, d = g0
        l = canon_line(((l[0] * a + l[1] * c) % N0, (l[0] * b + l[1] * d) % N0), N0)
    return (v, l)


def minus_one_in_U(N1: int, N0: int = 1) -> bool:
    """``-1 in U_1(N1) cap U_0(N0)`` iff ``N1 | 2``."""
    return N1 in (1, 2)


class XB:
    """``X_B(U')`` for ``U' = U_1(N1) cap U_0(N0)``: orbits of ``Gamma_x`` on ``GL_2(Z/N)/U'`` for every class ``x``."""

    def __init__(self, D: int, N1: int = 1, N0: int = 1):
        assert gcd(N1, N0) == 1 and gcd(N1 * N0, D) == 1
        self.D, self.N1, self.N0 = D, N1, N0
        self.cd = cd = class_data(D)
        pts = level_points(N1, N0)
        self.index = len(pts)  # [hat O^x : U']
        self.orbit_of: list[dict] = []   # per class: point -> orbit number
        self.orbits: list[list[dict]] = []  # per class: list of {rep, size, stab, w}
        self.mass = Fraction(0)    # sum 1/|Gamma_x'|
        self.massW = Fraction(0)   # sum 1/w_x'
        for c in range(cd.h):
            gam = cd.units(c)
            mats = [(cd.phi(c, u, N1), cd.phi(c, u, N0)) for u in gam]
            mats = sorted(set(mats))
            m1 = (cd.phi(c, cd.minus_one(c), N1), cd.phi(c, cd.minus_one(c), N0))
            order = len(gam)
            of, orbs = {}, []
            for p in pts:
                if p in of:
                    continue
                orb = {_act(p, g1, g0, N1, N0) for g1, g0 in mats}
                k = len(orbs)
                for q in orb:
                    of[q] = k
                stab = order // len(orb)
                assert order % len(orb) == 0
                minus_in = _act(p, m1[0], m1[1], N1, N0) == p
                w = stab // 2 if minus_in else stab
                orbs.append({"rep": p, "size": len(orb), "stab": stab, "w": w})
                self.mass += Fraction(1, stab)
                self.massW += Fraction(1, w)
            self.orbit_of.append(of)
            self.orbits.append(orbs)

    def __len__(self):
        return sum(len(o) for o in self.orbits)

    @property
    def gamma_multiset(self):
        return sorted(o["stab"] for orbs in self.orbits for o in orbs)

    def elements(self):
        return [(c, i) for c, orbs in enumerate(self.orbits) for i in range(len(orbs))]


def mass_check(D: int, big: tuple[int, int], small: tuple[int, int]) -> dict:
    """Level change ``U' = U_1(n1') cap U_0(n0')`` inside ``U = U_1(n1) cap U_0(n0)`` (both conventions)."""
    X, Y = XB(D, *big), XB(D, *small)
    assert Y.index % X.index == 0
    idx = Y.index // X.index
    mU, mUp = minus_one_in_U(*big), minus_one_in_U(*small)
    factor_two = mU and not mUp
    ok_full = Y.mass == idx * X.mass
    ok_w = (2 if factor_two else 1) * Y.massW == idx * X.massW
    return {"D": D, "U": list(big), "Uprime": list(small), "index": idx, "factor_two": factor_two,
            "mass_U": X.mass, "mass_Up": Y.mass, "massW_U": X.massW, "massW_Up": Y.massW,
            "ok_full": ok_full, "ok_w": ok_w}


# ---------------------------------------------------------------- p-tower

class Tower:
    """``S_s = X_B(U_1(M p^s))``, ``s = 1..smax``, with projections and diamond operators (``p`` not dividing ``D M``)."""

    def __init__(self, D: int, p: int, smax: int, M: int = 1):
        assert gcd(p, D * M) == 1 and gcd(M, D) == 1
        self.D, self.p, self.M, self.smax = D, p, M, smax
        self.S = {s: XB(D, M * p**s, 1) for s in range(1, smax + 1)}

    def size(self, s: int) -> int:
        return len(self.S[s])

    def _index_map(self, s):
        X = self.S[s]
        return {e: k for k, e in enumerate(X.elements())}

    def projection(self, s: int) -> list[int]:
        """``S_s -> S_{s-1}`` (``s >= 2``) as a list of target indices."""
        assert 2 <= s <= self.smax
        X, Y = self.S[s], self.S[s - 1]
        Nn = self.M * self.p ** (s - 1)
        idy = self._index_map(s - 1)
        out = []
        for c, i in X.elements():
            (v0, v1), _ = X.orbits[c][i]["rep"]
            q = ((v0 % Nn, v1 % Nn), ())
            out.append(idy[(c, Y.orbit_of[c][q])])
        return out

    def diamond(self, s: int, d: int) -> list[int]:
        """``Delta_s`` acting by ``d in (Z/p^s)^x``: ``v -> d^{-1} v`` modulo ``p^s`` and trivially modulo ``M``."""
        X = self.S[s]
        N = self.M * self.p**s
        ps = self.p**s
        dinv = pow(d, -1, ps)
        u = _crt([(dinv, ps), (1, self.M)]) if self.M > 1 else dinv
        idx = self._index_map(s)
        out = []
        for c, i in X.elements():
            (v0, v1), _ = X.orbits[c][i]["rep"]
            q = (((u * v0) % N, (u * v1) % N), ())
            out.append(idx[(c, X.orbit_of[c][q])])
        return out

    def delta_free(self, s: int) -> bool:
        """``Delta_s = (1 + pZ)/(1 + p^s Z)`` acts freely: no non-identity element has a fixed point."""
        ps = self.p**s
        for k in range(1, ps // self.p):
            perm = self.diamond(s, 1 + self.p * k)
            if any(perm[j] == j for j in range(len(perm))):
                return False
        return True


# ---------------------------------------------------------------- output

def expected_Sizes(D: int, p: int, s: int, M: int = 1) -> Fraction:
    N = M * p**s
    return Fraction(phi_fn(D), 24) * psi_fn(N) * phi_fn(N)


MASS_CASES = [  # (D, U, U')  with U = (N1, N0)
    (2, (1, 1), (1, 3)), (2, (1, 1), (5, 1)), (2, (1, 3), (5, 3)), (3, (1, 1), (1, 7)), (3, (1, 5), (5, 1)),
    (3, (7, 1), (7, 5)), (3, (7, 1), (35, 1)), (5, (1, 7), (7, 1)), (7, (1, 1), (4, 1)), (11, (1, 1), (3, 1)),
    (11, (1, 1), (1, 2)), (3, (1, 4), (5, 4)), (2, (3, 1), (3, 5)),
]


def main() -> None:
    with results.Timer() as t:
        data: dict = {"mass_level_change": [], "tower": {}, "x_u1_5_D2": None, "trivial_stab_u1p": {}}
        for D, U, Up in MASS_CASES:
            r = mass_check(D, U, Up)
            assert r["ok_full"] and r["ok_w"], r
            data["mass_level_change"].append(r)
        X = XB(2, 5, 1)
        data["x_u1_5_D2"] = len(X)
        for D in (2, 3, 5, 7, 11, 13):
            for p in (5, 7, 11):
                if D % p == 0:
                    continue
                X = XB(D, p, 1)
                data["trivial_stab_u1p"][f"D={D},p={p}"] = {"size": len(X), "all_gamma_trivial": X.gamma_multiset == [1] * len(X)}
        for D, p, smax in ((3, 5, 3), (2, 5, 3), (3, 7, 2)):
            T = Tower(D, p, smax)
            data["tower"][f"D={D},p={p}"] = {
                "sizes": {str(s): T.size(s) for s in range(1, smax + 1)},
                "expected": {str(s): str(expected_Sizes(D, p, s)) for s in range(1, smax + 1)},
                "delta_free": {str(s): T.delta_free(s) for s in range(1, smax + 1)},
            }
    results.write(
        "s01/levels.json", data, script="code/python/langlandscape/levels.py (python -m langlandscape.levels)",
        params={"mass_cases": MASS_CASES, "PREC": PREC}, runtime_s=t.seconds,
        notes="X_B(U') = sqcup_x Gamma_x\\(U/U'); mass in conventions |Gamma| and w=|Gamma/+-1|; "
              "U=(N1,N0) means U_1(N1) cap U_0(N0)",
    )


if __name__ == "__main__":
    main()
