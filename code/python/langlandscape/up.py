"""S01-C5: ``N_{U_p}`` and ``U'_p`` on ``S_s = X_B(U_1(5^s))`` for ``B = B_3``, ``p = 5``, ``M = 1``.

Conventions (binding: ``plan/staged/stage-01-quaternion-foundations.tex``)
--------------------------------------------------------------------------
* ``B = (-1, -3)_Q``, ramified exactly at ``{3, infinity}``; ``O = Z<1, i, (1+j)/2, (i+ij)/2>``
  (checked: an order with ``det(trd(b_k b_l)) = 9 = 3^2``, hence maximal of reduced discriminant 3).
  ``|O^x| = 12`` and the mass is ``1/12`` (thm:s01-mass(a)), so ``h = 1``: ``B^-hat^x = B^x O^-hat^x``.
* ``iota = iota_5: O -> M_2(Z/5^n)`` from :mod:`langlandscape.padic`.
* ``U = U_1(5^s)`` (def:s01-levels): lower row ``(c, d) = (0, 1) mod 5^s``.
* Points.  Since ``h = 1`` and ``B^x cap O^-hat^x = O^x``,
  ``S_s = O^x \\ GL_2(Z_5) / U_1(5^s)_5``.  For ``k`` in ``GL_2(Z_5)`` put ``v(k) := e_2 k^{-1}``
  (the lower row of ``k^{-1}``) mod ``5^s``.  For ``u`` in ``U_1``: ``(ku)^{-1} = u^{-1} k^{-1}`` and
  the lower row of ``u^{-1}`` is ``(0, 1)``, so ``v(ku) = v(k)``; conversely ``v(k) = v(k')`` iff
  ``e_2 k^{-1} k' = e_2`` iff ``k^{-1}k'`` has lower row ``(0, 1)``, i.e. lies in ``U_1``.  Thus
  ``kU_1 -> v(k)`` is a bijection onto primitive row vectors mod ``5^s``, and
  ``v(gamma k) = v(k) iota(gamma)^{-1}``: a point of ``S_s`` is an orbit of primitive row vectors
  under right multiplication by ``iota(O^x)``.  ``Gamma_x = 1`` iff the orbit has 12 elements.
* Homological operators on ``Z[S_s]`` (transposes of the function operators, def:s01-brandt):
  ``T_g [x] = sum_i [x g_i]`` with ``U g U = coprod g_i U``.  For ``x = k`` (at 5) and ``g`` at 5 with
  ``det g`` in ``5 Z_5^x`` we write ``x g = gamma y`` with ``gamma`` in ``O``, ``Nrd gamma = 5``,
  ``y`` in ``O^-hat^x`` (``iota(gamma)^{-1} k g`` integral; ``gamma`` is unique up to ``gamma O^x``).
  The away-from-5 components ``gamma^{-1}`` of ``y`` lie in ``U^{(5)}`` and are dropped, so
  ``[x g] = v(iota(gamma)^{-1} k g)``.  Computed with precision ``5^(s+2)`` (``iota(gamma)^{-1}`` has
  denominator 5).
* Matrices: ``M[t, s] = `` coefficient of ``[x_t]`` in ``T[x_s]`` (columns = images).  The matrix of
  the same-named operator on functions ``Z^{S_s}`` (evaluation duality, all ``Gamma_x = 1``) is ``M^T``.
* ``U_p = N_{U_p}``: ``varpi_j = iota^{-1}[[5, j], [0, 1]]``, ``j = 0..4`` (def:s01-NUp);
  ``U'_p``: representatives ``iota^{-1}[[1, 0], [5^s j, 5]]`` at level ``s`` (lem:s01-Up(c)).
* Diamonds (def:s01-hecke): ``<d>[x] = [x delta_d]``, ``delta_d = iota^{-1} diag(1, d)``, i.e.
  ``v -> d^{-1} v``.  This is the *adelic* ``<d>`` (tex: adelic ``<d>`` = classical ``<d>^{-1}``).
  Character parts are ``{x in C[S_s] : <d> x = chi(d) x}`` for this homological adelic ``<d>``.
* ``T_2 = [U varpi_2 U]``: ``T_2[v] = sum_{gamma} [v iota(gamma)]``, ``gamma`` over the 3 classes
  ``gamma O^x`` of elements of norm 2 (``x varpi_{2,i} = gamma y`` with ``y_5 = iota(gamma)^{-1} k``).
* ``pi = pi_{s+1,s}``: ``v mod 5^(s+1) -> v mod 5^s``.  ``pi_*[x] = [pi x]``;
  ``pi^![x] = sum_{u in U_(s)/U_(s+1)} [x u]`` (``u = [[1, 0], [5^s c, 1 + 5^s d]]``), the transpose of
  the trace ``tr f(x) = sum_u f(xu)`` on functions; the transpose of ``pi_*`` is the pullback
  ``pi^* f = f o pi``.
"""

from __future__ import annotations

import functools
import math
import itertools
from fractions import Fraction

import numpy as np

from . import padic
from .padic import mat_adj, mat_det, mat_mul

A, B = -1, -3
P = 5
BASIS = [
    (1, 0, 0, 0),
    (0, 1, 0, 0),
    (Fraction(1, 2), 0, Fraction(1, 2), 0),
    (0, Fraction(1, 2), 0, Fraction(1, 2)),
]
E2 = (0, 1)


# ---------------------------------------------------------------------------
# the order
# ---------------------------------------------------------------------------

def gram_nrd():
    """Integer Gram matrix ``G`` with ``x^T G x = 2 Nrd(x)`` in the order basis."""
    G = [[0] * 4 for _ in range(4)]
    for k in range(4):
        for l in range(4):
            G[k][l] = int(padic.quat_trd(padic.quat_mul(A, B, BASIS[k], padic.quat_conj(BASIS[l]))))
    return G


@functools.lru_cache(maxsize=None)
def elements_of_norm(n: int) -> tuple:
    """All elements of ``O`` (order coordinates) of reduced norm ``n`` (PARI ``qfminim``)."""
    from .pari import get_pari

    pari = get_pari()
    G = gram_nrd()
    Gp = pari.matrix(4, 4, [G[r][c] for r in range(4) for c in range(4)])
    res = pari.qfminim(Gp, 2 * n)
    vecs = res[2]
    out = []
    for t in range(int(pari.matsize(vecs)[1])):
        v = tuple(int(vecs[r, t]) for r in range(4))
        if padic.quat_nrd(A, B, padic.to_B(BASIS, v)) == n:
            out.append(v)
            out.append(tuple(-c for c in v))
    return tuple(sorted(set(out)))


def _mul_O(x, y):
    """Product in order coordinates."""
    z = padic.quat_mul(A, B, padic.to_B(BASIS, x), padic.to_B(BASIS, y))
    c = padic._solve4(BASIS, z)
    assert all(t.denominator == 1 for t in c)
    return tuple(int(t) for t in c)


@functools.lru_cache(maxsize=None)
def classes_mod_units(n: int) -> tuple:
    """Representatives of ``{gamma : Nrd gamma = n} / O^x`` (right multiplication)."""
    units = elements_of_norm(1)
    seen, reps = set(), []
    for g in elements_of_norm(n):
        if g in seen:
            continue
        orb = {_mul_O(g, e) for e in units}
        assert len(orb) == len(units)
        seen |= orb
        reps.append(g)
    return tuple(reps)


# ---------------------------------------------------------------------------
# levels
# ---------------------------------------------------------------------------

class Level:
    """``S_s``: orbits of primitive row vectors mod ``5^s`` under right mult. by ``iota(O^x)``."""

    def __init__(self, s: int, iota: padic.Splitting):
        self.s = s
        self.q = P**s
        self.iota = iota
        q = self.q
        self.unit_mats = [[[c % q for c in row] for row in iota.image(e)] for e in elements_of_norm(1)]
        self.index: dict = {}
        self.points: list = []
        self.orbit_sizes: list = []
        for v in itertools.product(range(q), repeat=2):
            if v[0] % P == 0 and v[1] % P == 0 or v in self.index:
                continue
            orb = {self._vm(v, E) for E in self.unit_mats}
            rep = min(orb)
            idx = len(self.points)
            self.points.append(rep)
            self.orbit_sizes.append(len(orb))
            for w in orb:
                self.index[w] = idx
        # sort points canonically
        order = sorted(range(len(self.points)), key=lambda t: self.points[t])
        relabel = {old: new for new, old in enumerate(order)}
        self.points = [self.points[t] for t in order]
        self.orbit_sizes = [self.orbit_sizes[t] for t in order]
        self.index = {w: relabel[t] for w, t in self.index.items()}

    def _vm(self, v, E):
        q = self.q
        return ((v[0] * E[0][0] + v[1] * E[1][0]) % q, (v[0] * E[0][1] + v[1] * E[1][1]) % q)

    def __len__(self):
        return len(self.points)

    def idx(self, v) -> int:
        return self.index[(v[0] % self.q, v[1] % self.q)]


def k_from_v(v, mod: int, shift: int = 0):
    """A matrix ``k`` mod ``mod`` with ``e_2 k^{-1} = v``; ``shift`` varies the choice (tests)."""
    v1, v2 = v[0] % mod, v[1] % mod
    if v2 % P:
        r = [padic._inv(v2, mod), 0]
    else:
        r = [0, (-padic._inv(v1, mod)) % mod]
    r = [(r[0] + shift * v1) % mod, (r[1] + shift * v2) % mod]
    kinv = [r, [v1, v2]]
    assert mat_det(kinv, mod) == 1
    return mat_adj(kinv, mod)  # det 1


def v_of(y, q: int):
    """``e_2 y^{-1}`` mod ``q`` for ``y`` in ``GL_2(Z_5)`` (given mod a multiple of ``q``)."""
    d = mat_det(y, q)
    assert d % P, "not invertible"
    di = padic._inv(d, q)
    return ((-y[1][0]) * di % q, y[0][0] * di % q)


class Context:
    """Splitting + norm-5 data at a fixed precision."""

    def __init__(self, smax: int):
        self.smax = smax
        self.N = smax + 3  # precision of iota
        self.iota = padic.split(A, B, BASIS, P, self.N)
        self.mod = P**self.N
        self.gammas5 = [self.iota.image(g) for g in classes_mod_units(P)]
        self.gammas2 = [self.iota.image(g) for g in classes_mod_units(2)]
        self.levels = {s: Level(s, self.iota) for s in range(1, smax + 1)}

    # -- [x g] for g at 5 with det g in Z_5^x or 5 Z_5^x --------------------------------------
    def translate(self, level: Level, v, g, shift: int = 0):
        """Index of ``[x g]`` in ``level`` where ``v(x) = v``; ``g`` integer 2x2 (mod ``5^N``)."""
        s = level.s
        mod = P ** (s + 2)
        k = k_from_v(v, mod, shift)
        kg = mat_mul(k, [[c % mod for c in row] for row in g], mod)
        dg = mat_det(g, mod)
        if dg % P:
            return level.idx(v_of(kg, level.q))
        assert dg % (P * P) and dg % P == 0
        hits = []
        for G in self.gammas5:
            Gm = [[c % mod for c in row] for row in G]
            z = mat_mul(mat_adj(Gm, mod), kg, mod)  # = 5 * iota(gamma)^{-1} k g
            if all(c % P == 0 for row in z for c in row):
                y = [[(c // P) % (mod // P) for c in row] for row in z]
                hits.append(y)
        assert len(hits) == 1, f"expected exactly one gamma, got {len(hits)}"
        return level.idx(v_of(hits[0], level.q))

    def operator(self, level: Level, mats, shift: int = 0) -> np.ndarray:
        n = len(level)
        M = np.zeros((n, n), dtype=np.int64)
        for c, v in enumerate(level.points):
            for g in mats:
                M[self.translate(level, v, g, shift), c] += 1
        return M

    def Up(self, s: int, shift: int = 0) -> np.ndarray:
        return self.operator(self.levels[s], [[[P, j], [0, 1]] for j in range(P)], shift)

    def Up_prime(self, s: int, shift: int = 0) -> np.ndarray:
        return self.operator(self.levels[s], [[[1, 0], [P**s * j, P]] for j in range(P)], shift)

    def diamond(self, s: int, d: int) -> np.ndarray:
        return self.operator(self.levels[s], [[[1, 0], [0, d]]])

    def T2(self, s: int) -> np.ndarray:
        level = self.levels[s]
        n, q = len(level), level.q
        M = np.zeros((n, n), dtype=np.int64)
        for c, v in enumerate(level.points):
            for G in self.gammas2:
                M[level.idx(level._vm(v, G)), c] += 1
        return M

    def pi_push(self, s: int) -> np.ndarray:
        """``pi_*: Z[S_{s+1}] -> Z[S_s]``."""
        hi, lo = self.levels[s + 1], self.levels[s]
        M = np.zeros((len(lo), len(hi)), dtype=np.int64)
        for c, v in enumerate(hi.points):
            M[lo.idx(v), c] += 1
        return M

    def pi_shriek(self, s: int) -> np.ndarray:
        """``pi^!: Z[S_s] -> Z[S_{s+1}]``, ``[x] -> sum_{u in U_(s)/U_(s+1)} [xu]``."""
        hi, lo = self.levels[s + 1], self.levels[s]
        M = np.zeros((len(hi), len(lo)), dtype=np.int64)
        mod = P ** (s + 3)
        us = [[[1, 0], [P**s * c, 1 + P**s * d]] for c in range(P) for d in range(P)]
        for col, v in enumerate(lo.points):
            k = k_from_v(v, mod)
            for u in us:
                M[hi.idx(v_of(mat_mul(k, u, mod), hi.q)), col] += 1
        return M


# ---------------------------------------------------------------------------
# exact algebra (PARI)
# ---------------------------------------------------------------------------

def _pmat(M):
    from .pari import get_pari

    pari = get_pari()
    M = np.asarray(M)
    return pari.matrix(M.shape[0], M.shape[1], [int(t) for t in M.flatten()])


def factored_charpoly(M) -> dict:
    from .pari import get_pari

    pari = get_pari()
    cp = pari.charpoly(_pmat(M))
    fa = pari.factor(cp)
    facs = [[str(fa[t, 0]), int(fa[t, 1])] for t in range(int(pari.matsize(fa)[0]))]
    return {"charpoly": str(cp), "factors": facs}


def character_data(D: np.ndarray, ops: dict, phi: int) -> list:
    """Decompose ``Q[S]`` under ``<2>`` (``D``), ``2`` a generator of ``(Z/5^s)^x`` of order ``phi``.

    For each ``m | phi``: ``W_m = ker Phi_m(D)`` = sum of the ``chi``-parts over the Galois orbit
    of characters with ``chi(2)`` a primitive ``m``-th root of unity.  Reports ``dim W_m``, the
    charpolys over ``Q`` (factored) of each operator on ``W_m``, and, for the representative
    ``chi(2) = y`` (``y`` a root of ``polcyclo(m, y)``), the charpoly of each operator on the
    ``chi``-part factored over ``Q(y)``.
    """
    from .pari import get_pari

    pari = get_pari()
    Dp = _pmat(D)
    n = D.shape[0]
    out = []
    for m in sorted(d for d in range(1, phi + 1) if phi % d == 0):
        cyc = pari.polcyclo(m)
        PhiD = pari.subst(cyc, "x", Dp)
        if m == 1:
            PhiD = Dp - pari.matid(n)
        K = pari.matker(PhiD)
        dim = int(pari.matsize(K)[1])
        entry = {"m": m, "dim_Q": dim, "chi_rep": f"chi(2) = y, polcyclo({m}, y) = 0",
                 "conrey_exponents": [k for k in range(phi) if (phi // math.gcd(k, phi)) == m],
                 "parity": "even" if (phi // 2) % m == 0 else "odd"}
        if dim:
            nf = pari.nfinit(pari.polcyclo(m, "y"))
            z = pari("Mod(y, polcyclo(%d, y))" % m)
            Kz = pari.matker(Dp - z * pari.matid(n))
            dz = int(pari.matsize(Kz)[1])
            entry["dim_chi"] = dz
            for name, Op in ops.items():
                Opp = _pmat(Op)
                R = pari.matinverseimage(K, Opp * K)
                assert int(pari.matsize(R)[0]) == dim
                cpQ = pari.charpoly(R)
                fa = pari.factor(cpQ)
                entry[name + "_Q"] = {
                    "charpoly": str(cpQ),
                    "factors": [[str(fa[t, 0]), int(fa[t, 1])] for t in range(int(pari.matsize(fa)[0]))],
                }
                Rz = pari.matinverseimage(Kz, Opp * Kz)
                cpz = pari.lift(pari.charpoly(Rz))
                faz = pari.nffactor(nf, cpz)
                entry[name + "_chi"] = {
                    "charpoly": str(cpz),
                    "factors_over_Q(y)": [[str(pari.lift(faz[t, 0])), int(faz[t, 1])]
                                          for t in range(int(pari.matsize(faz)[0]))],
                }
        out.append(entry)
    return out


def conrey_label(k: int, s: int) -> int:
    """Conrey label of the character mod ``5^s`` with ``chi(2) = exp(2 pi i k / phi(5^s))``.

    (2 is the least primitive root mod ``5^s``; Conrey: ``chi_n(2) = e(nu(n)/phi)``, ``nu`` = log_2.)
    """
    return pow(2, k, P**s)


@functools.lru_cache(maxsize=None)
def context(smax: int = 3) -> Context:
    return Context(smax)


# ---------------------------------------------------------------------------
# checks and result file
# ---------------------------------------------------------------------------

def checks(C: Context) -> dict:
    """All asserted identities as booleans (``pi``-checks for ``s = 1 .. smax-1``)."""
    out = {}
    U = {s: C.Up(s) for s in C.levels}
    V = {s: C.Up_prime(s) for s in C.levels}
    for s in C.levels:
        out[f"s{s}_Gamma_trivial"] = set(C.levels[s].orbit_sizes) == {len(elements_of_norm(1))}
        out[f"s{s}_Up_degree5"] = bool((U[s].sum(axis=0) == P).all() and (U[s].sum(axis=1) == P).all())
        out[f"s{s}_Upr_degree5"] = bool((V[s].sum(axis=0) == P).all() and (V[s].sum(axis=1) == P).all())
        out[f"s{s}_Up_transpose_eq_Upr (lem:s01-Up(d), M=1, w=1)"] = bool((U[s].T == V[s]).all())
    for s in C.levels:
        if s + 1 not in C.levels:
            continue
        pp, ps = C.pi_push(s), C.pi_shriek(s)
        out[f"s{s}_pi_push_Up_commute (lem:s01-Up(b))"] = bool((pp @ U[s + 1] == U[s] @ pp).all())
        out[f"s{s}_pi_push_Upr_commute (expected False)"] = bool((pp @ V[s + 1] == V[s] @ pp).all())
        out[f"s{s}_pi_shriek_eq_pi_push_transpose"] = bool((ps == pp.T).all())
        out[f"s{s}_trace_Upr_commute (lem:s01-Up(c))"] = bool((V[s + 1] @ ps == ps @ V[s]).all())
        out[f"s{s}_pi_shriek_Up_commute (info)"] = bool((U[s + 1] @ ps == ps @ U[s]).all())
    for s in [t for t in C.levels if t <= 2]:
        D, T = C.diamond(s, 2), C.T2(s)
        for nm, X in (("Up", U[s]), ("Upr", V[s])):
            out[f"s{s}_{nm}_commutes_diamond2"] = bool((X @ D == D @ X).all())
            out[f"s{s}_{nm}_commutes_T2"] = bool((X @ T == T @ X).all())
        out[f"s{s}_T2_degree3"] = bool((T.sum(axis=0) == 3).all())
        out[f"s{s}_T2_transpose_eq_diamond2_T2 (prop:s01-adjoint(b))"] = bool((T.T == D @ T).all())
    return out


def run(smax: int = 3) -> dict:
    from . import results

    with results.Timer() as tm:
        C = context(smax)
        data = {
            "algebra": {"a": A, "b": B, "D": 3, "order_basis_in_1_i_j_ij": [[str(c) for c in v] for v in BASIS],
                        "disc_squared": str(padic.discriminant(A, B, BASIS)), "units": len(elements_of_norm(1)),
                        "iota_5": {"method": C.iota.method, "precision": f"5^{C.N}", "I": C.iota.I,
                                   "J": C.iota.J}},
            "conventions": {
                "points": "x = k in GL_2(Z_5) at 5 <-> O^x-orbit of v = e_2 k^{-1} mod 5^s (lower row of k^{-1}); "
                          "left action gamma: v -> v iota(gamma)^{-1}",
                "matrices": "homological, columns = images: M[t][c] = coeff of [x_t] in T[x_c]; "
                            "function-side operator has matrix M^T",
                "Up": "N_{U_p}: U_p[x] = sum_j [x varpi_j], varpi_j = iota^-1 [[5, j], [0, 1]]",
                "Upr": "U'_p[x] = sum_j [x iota^-1 [[1, 0], [5^s j, 5]]]",
                "diamond": "adelic <d>[x] = [x iota^-1 diag(1, d)] (v -> d^-1 v); tex: adelic <d> = classical <d>^-1; "
                           "matrix stored for d = 2 (generator of (Z/5^s)^x)",
                "characters": "chi-part = {x in C[S_s]: <d>x = chi(d)x} for the homological adelic <d>; "
                              "chi(2) = exp(2 pi i k/phi(5^s)) has Conrey label 2^k mod 5^s; "
                              "the rows group chi by m = order of chi(2)",
                "pi": "pi_* = pushforward Z[S_{s+1}] -> Z[S_s]; pi^! = transpose of the trace on functions",
            },
            "levels": {},
            "checks": checks(C),
        }
        for s in [t for t in C.levels if t <= 2]:
            lv = C.levels[s]
            U, V, D, T = C.Up(s), C.Up_prime(s), C.diamond(s, 2), C.T2(s)
            phi = 4 * P ** (s - 1)
            chars = character_data(D, {"Up": U, "Upr": V}, phi)
            for e in chars:
                e["conrey_labels"] = [conrey_label(k, s) for k in e["conrey_exponents"]]
            data["levels"][f"S_{s}"] = {
                "size": len(lv),
                "points_v": [list(v) for v in lv.points],
                "Up": U.tolist(), "Upr": V.tolist(), "diamond_2": D.tolist(), "T2": T.tolist(),
                "charpoly_Up": factored_charpoly(U), "charpoly_Upr": factored_charpoly(V),
                "characters": chars,
            }
        data["levels"]["S_3"] = {"size": len(C.levels[3])} if 3 in C.levels else None
        data["pi_push_S2_to_S1"] = C.pi_push(1).tolist()
    results.write("s01/up.json", data, script="code/python/langlandscape/up.py (python -m langlandscape.up)",
                  params={"D": 3, "p": P, "M": 1, "smax": smax}, runtime_s=round(tm.seconds, 3),
                  notes="S01-C5: N_{U_p} and U'_p on S_1, S_2 (S_3 for the pi-checks)")
    return data


if __name__ == "__main__":
    d = run()
    for k, v in d["checks"].items():
        print(k, v)
