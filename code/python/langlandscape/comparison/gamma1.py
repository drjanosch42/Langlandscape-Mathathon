# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S05-C2 / T05-2: validation of prop:s05-sign(c),(d) at level ``U_1(N)`` for ``B_q`` (weight 2).

Definite side (homological, right translation, tex Setting of ss:s05-sign; def:s01-hecke).
* ``B = B_q``, ``O`` maximal (``levels.class_data(q)``), left ideal classes ``I_c`` of ``O`` (stage-1 C1 BFS over
  ``ell0``-neighbours, ``ell0 = 2`` here, so ``nrd(I_c)`` is a power of ``ell0``, prime to ``N``).  ``J_c := conj(I_c)``
  is a right ideal, ``J_c = x_c O^`` with ``x_c`` in ``B^_f^x`` chosen ``= 1`` at the primes ``l | N`` (possible since
  ``J_{c,l} = O_l``), and ``X_B(U_1(N)) = sqcup_c Gamma_c \\ GL_2(Z/N)/U_1(N)``, ``Gamma_c = O_l(J_c)^x = O_r(I_c)^x``.
* One splitting ``iota: O (x) Z_N -> M_2(Z_N)`` (that of ``levels`` for ``O`` itself), used for *all* classes (this is the
  cross-class compatibility that stage-1 ``XB`` does not need).  Point ``[x_c k]`` <-> ``(c, v)``, ``v = e_2 k^{-1}`` mod N
  (primitive row vector); ``gamma in Gamma_c`` acts by ``v -> v iota(gamma)^{-1}``.
* ``T_g`` for ``g`` supported at ``l`` prime to ``N`` (``T_ell``: ``g = varpi_ell``; ``Pi_q``: a uniformiser at ``q``):
  ``x_c g_i O^ = J'`` and ``J' = gamma J_{c'}`` with ``gamma in B^x``  ==>  ``[x_c k g_i] = (c', v iota(gamma))``.
  In left-ideal language ``conj(J') = I_{c'} conj(gamma)``; ``conj(J')`` runs over the ``ell+1`` neighbours
  ``I_c K`` (``T_ell``) resp. equals ``P I_c`` with ``P`` the two-sided prime of ``O`` above ``q`` (``Pi_q``).
* ``<d>[x] = [x delta_d]``, ``delta_d = diag(1, d)`` at ``N``: ``v -> d^{-1} v`` (adelic diamond, as levels.Tower.diamond).
* Matrices: column ``c`` = image of ``[x_c]``.  ``Z[X]^0`` basis ``[x_i] - [x_0]`` (``i >= 1``).

Classical side (PARI ``mf``).  q-new part of ``S_2(Gamma_1(N) cap Gamma_0(q))`` for ``N`` prime: newforms of level ``Nq``
with character ``chi`` mod ``N`` (one PARI space per Galois orbit; all complex embeddings) and newforms of level ``q``
(trivial character) with multiplicity 2.  ``chi`` is read off the coefficients, convention-free:
``chi(l) = (a_l^2 - a_{l^2})/l`` (``T_l^2 = T_{l^2} + l<l>``, classical ``<l>``), so no Conrey-label convention enters.

Dictionaries ``theta``: ``T_ell -> T_ell``, ``<d>_cl -> <d>_ad^{-delta}``, ``U_q -> +Pi_q^e`` for ``(delta, e) in {+-1}^2``,
plus the genuine Rosati dictionary ``theta^Ros`` (prop:s05-AL, lem:s05-consistency(b)): ``T_ell -> <ell>_ad T_ell``,
``<d> -> <d>_ad``, ``U_q -> Pi_q^{-1}``.  A dictionary *matches* iff the multiset of images of the joint eigensystems of
``(T_ell, <d>_ad, Pi_q)`` on ``Z[X]^0 (x) C`` equals the multiset of classical ``(a_ell, chi(d), a_q)``.

Run ``python3 -m langlandscape.comparison.gamma1`` (from ``code/python``) to write ``code/results/s05/T05-2.json``.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import gcd

import numpy as np

from .. import brandt, levels, results
from ..pari import get_pari
from ..quat import Lattice, prime_factors

PAIRS = ((13, 5), (11, 7), (23, 5), (23, 7))  # (q, N); (23, 7) added: N = 5 is never informative, see informative()
NELLS = 4
TOL = 1e-6


def mult_order(a: int, n: int) -> int:
    k, x = 1, a % n
    while x != 1:
        x, k = x * a % n, k + 1
    return k


def primitive_root(n: int) -> int:
    return next(g for g in range(2, n) if mult_order(g, n) == n - 1)


def informative(q: int, N: int) -> dict:
    """Plan criterion ``ord(q mod N) not in {1,2}`` and the sharp one: some *even* chi has ``chi(q)^2 != 1``.

    Only even characters occur (``-1`` is central in ``B^x``, so ``<-1>_ad = 1``; weight 2), and an even ``chi`` with
    ``chi(q)^2 != 1`` exists iff ``q^2`` is nontrivial in ``(Z/N)^x/{+-1}``, i.e. ``q^2 != +-1 mod N``.
    """
    o = mult_order(q, N)
    return {"ord_q_mod_N": o, "plan_criterion": o not in (1, 2), "even_chi_with_chi_q_sq_ne_1": (q * q) % N not in (1, N - 1)}


# ---------------------------------------------------------------- definite side

class Gamma1Module:
    """``Z[X_B(U_1(N))]`` for ``B = B_q`` with ``T_ell``, adelic ``<d>`` and ``Pi_q`` (homological)."""

    def __init__(self, q: int, N: int):
        assert len(prime_factors(N)) == 1 and prime_factors(N)[0] == N and gcd(q, N) == 1, "N prime, prime to q"
        self.q, self.N = q, N
        self.cd = cd = levels.class_data(q)
        self.B = B = cd.B
        assert [list(b) for b in cd.orders[0].basis] == [list(b) for b in B.O.basis] == [[int(i == j) for j in range(4)] for i in range(4)]
        self.reps = cd.reps  # (I_c, nrd I_c)
        assert all(gcd(n, N) == 1 for _, n in self.reps)
        self.h = cd.h
        pv = levels.prim_vectors(N)
        self.orbit_of, self.points = [], []
        for c in range(self.h):
            R = cd.orders[c]
            mats = {self.iota(tuple(sum(u[i] * R.basis[i][k] for i in range(4)) for k in range(4))) for u in cd.units(c)}
            of = {}
            for v in pv:
                if v in of:
                    continue
                k = len(self.points)
                self.points.append((c, v))
                for g in mats:
                    of[self.vact(v, g)] = k
            self.orbit_of.append(of)
        self.n = len(self.points)

    def iota(self, gamma) -> tuple:
        """``iota(gamma)`` mod ``N`` for ``gamma in B`` integral at ``N`` (algebra coordinates = coordinates in ``O``)."""
        m = 1
        for t in gamma:
            m = m * Fraction(t).denominator // gcd(m, Fraction(t).denominator)
        assert gcd(m, self.N) == 1
        a = self.cd.phi(0, [int(Fraction(t) * m) for t in gamma], self.N)
        mi = pow(m, -1, self.N)
        return tuple(x * mi % self.N for x in a)

    def vact(self, v, g):
        a, b, c, d = g
        N = self.N
        return ((v[0] * a + v[1] * c) % N, (v[0] * b + v[1] * d) % N)

    def _class_and_gamma(self, Ip: Lattice, nIp: int):
        """``c'`` and ``gamma`` with ``Ip = I_{c'} conj(gamma)``."""
        B, pari = self.B, get_pari()
        for c2, (I2, n2) in enumerate(self.reps):
            L = B.lmul(B.lconj(I2), Ip)
            res = pari.qfminim(B.gram(L), 2 * n2 * nIp, None, 2)
            vecs = res[2]
            for t in range(int(pari.matsize(vecs)[1])):
                co = [int(vecs[r, t]) for r in range(4)]
                alpha = tuple(sum(co[i] * L.basis[i][k] for i in range(4)) for k in range(4))
                if B.nrd(alpha) == n2 * nIp:
                    gbar = tuple(x / n2 for x in alpha)
                    return c2, B.conj(gbar)
        raise RuntimeError("ideal not in any class")

    def _operator(self, targets) -> np.ndarray:
        """``targets[c]`` = list of ``(c', gamma)``; returns the homological matrix, checking well-definedness."""
        M = np.zeros((self.n, self.n), dtype=np.int64)
        imgs = []
        for c in range(self.h):
            imgs.append([(c2, self.iota(g)) for c2, g in targets[c]])
        for col, (c, v) in enumerate(self.points):
            for c2, g in imgs[c]:
                M[self.orbit_of[c2][self.vact(v, g)], col] += 1
        # well-definedness: every vector in the orbit of the representative gives the same image multiset
        for c in range(self.h):
            for v, k in self.orbit_of[c].items():
                img = Counter(self.orbit_of[c2][self.vact(v, g)] for c2, g in imgs[c])
                assert img == Counter({i: int(M[i, k]) for i in np.nonzero(M[:, k])[0]}), "T_g not well defined"
        return M

    @lru_cache(maxsize=None)
    def T(self, ell: int) -> np.ndarray:
        assert (self.N * self.q) % ell
        tg = [[self._class_and_gamma(Ip, nIp) for Ip, nIp in brandt.neighbours(self.B, I, n, ell)] for I, n in self.reps]
        return self._operator(tg)

    def prime_q(self) -> Lattice:
        B, q = self.B, self.q
        Ob = B.O.basis
        alpha = next(x for x in (tuple(Fraction(a) for a in v) for v in _small_vectors()) if B.nrd(x) % q == 0 and any(x))
        P = Lattice([B.mul(B.mul(r, alpha), s) for r in Ob for s in Ob] + [tuple(q * t for t in r) for r in Ob])
        idx = abs(int(get_pari().matdet(get_pari().matrix(4, 4, [int(P.basis[j][i]) for i in range(4) for j in range(4)]))))
        assert idx == q * q, "P is not the prime above q"
        return P

    @lru_cache(maxsize=None)
    def Pi(self) -> np.ndarray:
        B, P = self.B, self.prime_q()
        tg = [[self._class_and_gamma(B.lmul(P, I), n * self.q)] for I, n in self.reps]
        return self._operator(tg)

    @lru_cache(maxsize=None)
    def diamond(self, d: int) -> np.ndarray:
        N = self.N
        di = pow(d, -1, N)
        M = np.zeros((self.n, self.n), dtype=np.int64)
        for col, (c, v) in enumerate(self.points):
            M[self.orbit_of[c][(di * v[0] % N, di * v[1] % N)], col] += 1
        return M


def _small_vectors(r: int = 3):
    import itertools
    return sorted(itertools.product(range(-r, r + 1), repeat=4), key=lambda v: sum(abs(t) for t in v))


def restrict0(M: np.ndarray) -> np.ndarray:
    """Matrix on ``Z[X]^0`` in the basis ``[x_i] - [x_0]``, ``i >= 1``."""
    n = M.shape[0]
    E = np.zeros((n, n - 1), dtype=np.int64)
    for i in range(1, n):
        E[i, i - 1], E[0, i - 1] = 1, -1
    Y = M @ E
    assert (Y.sum(axis=0) == 0).all()
    return Y[1:, :]


def brandt_systems(X: Gamma1Module, ells, g: int) -> list[dict]:
    """Joint eigensystems ``(lambda_ell, psi(g), pi)`` of ``T_ell, <g>_ad, Pi_q`` on ``Z[X]^0 (x) C``."""
    ops = {f"T{l}": restrict0(X.T(l)).astype(float) for l in ells}
    ops["D"] = restrict0(X.diamond(g)).astype(float)
    ops["Pi"] = restrict0(X.Pi()).astype(float)
    rng = np.random.default_rng(1)
    A = sum(rng.normal() * M for M in ops.values())
    _, V = np.linalg.eig(A)
    out = []
    for j in range(V.shape[1]):
        v = V[:, j]
        sysd = {}
        for k, M in ops.items():
            lam = np.vdot(v, M @ v) / np.vdot(v, v)
            assert np.linalg.norm(M @ v - lam * v) < 1e-7 * max(1, np.linalg.norm(M)), "not a joint eigenvector"
            sysd[k] = complex(lam)
        out.append({"a": [sysd[f"T{l}"] for l in ells], "psi_g": sysd["D"], "pi": sysd["Pi"]})
    return out


# ---------------------------------------------------------------- classical side

def _cx(x) -> complex:
    pari = get_pari()
    return complex(float(pari.real(x)), float(pari.imag(x)))


def _embedded(f, nmax: int) -> list[list[complex]]:
    pari = get_pari()
    e = pari.mfembed(f, pari.mfcoefs(f, nmax))
    vecs = [e] if str(pari.type(e[0])) != "t_VEC" else list(e)
    return [[_cx(t) for t in v] for v in vecs]


def classical_systems(q: int, N: int, ells, g: int, pg: int) -> tuple[list[dict], dict]:
    """Eigensystems ``(a_ell, chi(g), a_q)`` of the q-new part of ``S_2(Gamma_1(N) cap Gamma_0(q))``, ``N`` prime."""
    pari = get_pari()
    nmax = max(max(ells), pg, q) ** 2
    raw, dims = [], {}
    seen = set()
    for a in range(1, N):
        if a in seen:
            continue
        o = mult_order(a, N)
        orbit = {pow(a, k, N) for k in range(1, o + 1) if gcd(k, o) == 1}
        seen |= orbit
        mf = pari(f"mfinit([{N * q},2,Mod({a},{N})],0)")
        dims[f"Mod({a},{N})"] = {"orbit": sorted(orbit), "dim_one_chi": int(pari.mfdim(mf))}
        for f in pari.mfeigenbasis(mf):
            for c in _embedded(f, nmax):
                raw.append((c, 1))
                if len(orbit) == 2:  # Q(chi) imaginary quadratic: the other embedding is complex conjugation
                    raw.append(([z.conjugate() for z in c], 1))
                assert len(orbit) <= 2, "Galois orbits of size > 2 not handled"
    mf = pari(f"mfinit([{q},2],0)")
    dims["level_q_old_mult2"] = int(pari.mfdim(mf))
    for f in pari.mfeigenbasis(mf):
        for c in _embedded(f, nmax):
            raw.append((c, 2))
    out = []
    for c, m in raw:
        chi_g = (c[pg] ** 2 - c[pg * pg]) / pg
        dl = {pow(g, k, N): k for k in range(N - 1)}
        chi = lambda d: chi_g ** dl[d % N]
        assert abs(abs(chi_g) - 1) < TOL and abs(chi(-1) - 1) < TOL
        for l in ells:  # T_l^2 = T_{l^2} + l <l>: validates chi on all ell
            assert abs(c[l] ** 2 - c[l * l] - l * chi(l)) < 1e-6 * l
        assert abs(c[q] ** 2 - chi(q)) < TOL  # Li: a_q^2 = chi(q) (q-new, weight 2)
        for _ in range(m):
            out.append({"a": [c[l] for l in ells], "chi_g": chi_g, "aq": c[q]})
    return out, dims


# ---------------------------------------------------------------- matching

def dictionaries():
    """name -> (delta, e, eps, rosati_T); ``U_q -> eps Pi_q^e``."""
    out = {f"delta={d:+d},e={e:+d}": (d, e, 1, False) for d in (1, -1) for e in (1, -1)}
    out["delta=+1,e=+1,eps=-1"] = (1, 1, -1, False)
    out["Rosati (T->,<l>T, <d>-><d>, U_q->Pi^-1)"] = (-1, -1, 1, True)
    return out


def image(sysb: dict, delta: int, e: int, eps: int, ros: bool, ells, g: int, N: int) -> tuple:
    dl = {pow(g, k, N): k for k in range(N - 1)}
    psi = lambda d: sysb["psi_g"] ** dl[d % N]
    a = [lam * (psi(l) if ros else 1) for lam, l in zip(sysb["a"], ells)]
    return (a, sysb["psi_g"] ** (-delta), eps * sysb["pi"] ** e)


def _close(x: tuple, y: dict) -> bool:
    return all(abs(s - t) < TOL for s, t in zip(x[0], y["a"])) and abs(x[1] - y["chi_g"]) < TOL and abs(x[2] - y["aq"]) < TOL


def match(imgs: list[tuple], cls: list[dict]):
    """Greedy multiset matching with tolerance; returns (ok, unmatched images)."""
    left = list(range(len(cls)))
    bad = []
    for x in imgs:
        j = next((j for j in left if _close(x, cls[j])), None)
        if j is None:
            bad.append(x)
        else:
            left.remove(j)
    return (not bad and not left and len(imgs) == len(cls)), bad


def _c(z: complex) -> list:
    return [round(z.real, 8), round(z.imag, 8)]


def run_pair(q: int, N: int) -> dict:
    ells = [l for l in (2, 3, 5, 7, 11, 13, 17, 19) if (N * q) % l][:NELLS]
    g = primitive_root(N)
    pg = next(p for p in range(g, 10**4, N) if len(prime_factors(p)) == 1 and prime_factors(p)[0] == p and p != q)
    X = Gamma1Module(q, N)
    I = np.eye(X.n, dtype=np.int64)
    Ts = {l: X.T(l) for l in ells}
    ops = list(Ts.values()) + [X.Pi(), X.diamond(g)]
    checks = {
        "n_equals_stage1_XB": X.n == len(levels.XB(q, N, 1)),
        "T_degree_ell_plus_1": all((Ts[l].sum(axis=0) == l + 1).all() for l in ells),
        "all_commute": all((A @ B_ == B_ @ A).all() for A in ops for B_ in ops),
        "Pi_sq_eq_<q>^-1": bool((X.Pi() @ X.Pi() == X.diamond(pow(q, -1, N))).all()),
        "Pi_sq_ne_<q>": bool((X.Pi() @ X.Pi() != X.diamond(q % N)).any()),
        "Pi_sq_trivial": bool((X.Pi() @ X.Pi() == I).all()),
        "<-1>_trivial": bool((X.diamond(N - 1) == I).all()),
    }
    bs = brandt_systems(X, ells, g)
    cs, dims = classical_systems(q, N, ells, g, pg)
    dl = {pow(g, k, N): k for k in range(N - 1)}
    chis = Counter(tuple(_c(s["chi_g"])) for s in cs)
    chi_q = {str(k): _c(complex(*k) ** dl[q % N]) for k in chis}
    psis = Counter(tuple(_c(s["psi_g"])) for s in bs)
    occ_bad = any(abs((complex(*k) ** dl[q % N]) ** 2 - 1) > TOL for k in chis)
    verdicts, witnesses = {}, {}
    for name, (d, e, eps, ros) in dictionaries().items():
        ok, bad = match([image(s, d, e, eps, ros, ells, g, N) for s in bs], cs)
        verdicts[name] = ok
        if not ok:
            x = bad[0] if bad else None
            witnesses[name] = {"n_unmatched": len(bad), "first_unmatched_image": None if x is None else
                               {"a_ell": [_c(z) for z in x[0]], "chi_g": _c(x[1]), "a_q": _c(x[2]),
                                "chi_q": _c(x[1] ** dl[q % N])}}
    return {
        "q": q, "N": N, "ells": ells, "generator_g": g, "prime_for_chi_g": pg, "informative": informative(q, N),
        "h_Bq": X.h, "size_X_B_U1N": X.n, "dim_Z0": X.n - 1, "dim_classical_qnew": len(cs), "dims_detail": dims,
        "checks": checks,
        "classical_characters_chi_g_with_mult": {str(k): v for k, v in chis.items()},
        "classical_chi_q": chi_q,
        "brandt_adelic_psi_g_with_mult": {str(k): v for k, v in psis.items()},
        "some_occurring_chi_q_ne_pm1": occ_bad,
        "match": verdicts, "witness_of_failure": witnesses,
    }


def verdict(pd: dict) -> str:
    m = pd["match"]
    if not all(pd["checks"][k] for k in ("n_equals_stage1_XB", "T_degree_ell_plus_1", "all_commute", "Pi_sq_eq_<q>^-1")) \
       or pd["dim_Z0"] != pd["dim_classical_qnew"]:
        return "INCONCLUSIVE"
    if not m["delta=+1,e=+1"]:
        return "CONTRADICTION"
    if pd["some_occurring_chi_q_ne_pm1"] and (m["delta=+1,e=-1"] or m["delta=-1,e=+1"]):
        return "CONTRADICTION"
    return "CONFIRMED" if pd["some_occurring_chi_q_ne_pm1"] else "CONFIRMED (uninformative for e: all chi(q) = +-1)"


EXPLANATION = (
    "theta (delta=+1,e=+1: <d>_cl -> <d>_ad^-1, U_q -> +Pi_q) matches at every pair, eps=-1 never does. At N=7 the even cubic "
    "characters have chi(q) = zeta_3^{+-1} != +-1 and both mixed dictionaries fail (witnessed failure of Pi_q^-1 with delta=+1), "
    "as prop:s05-sign(c) predicts. The genuine Rosati dictionary theta^Ros (T_l -> <l>_ad T_l, <d> -> <d>_ad, U_q -> Pi_q^-1) "
    "also matches at every pair: it is the eigensystem-level shadow of prop:s05-AL (theta vs theta^Ros indistinguishable at "
    "one level; separated only by naturality in p-power levels, prop:s05-sign(d)), so this is no contradiction. The naive "
    "(delta,e)=(-1,-1) with T_l -> T_l fails by the T_l-relation (lem:s05-consistency(a)). At N=5 only the trivial and the "
    "quadratic even character occur (the order-4 characters are odd), so chi(q)=+-1, delta is invisible and (c) imposes "
    "nothing; (+1,-1) still fails there, because Pi_q^-1 = -Pi_q on the chi(q)=-1 part (a sign, not the exponent relation). "
    "The plan's criterion ord(q mod N) not in {1,2} is not sufficient: informative needs q^2 != +-1 mod N (even chi only).")


def main() -> None:
    with results.Timer() as t:
        pairs = []
        for q, N in PAIRS:
            pd = run_pair(q, N)
            pd["verdict"] = verdict(pd)
            pairs.append(pd)
            print(q, N, pd["size_X_B_U1N"], pd["dim_Z0"], pd["dim_classical_qnew"], pd["match"], pd["verdict"], flush=True)
    summary = {f"({p['q']},{p['N']})": p["verdict"] for p in pairs}
    overall = "CONTRADICTION" if any(v == "CONTRADICTION" for v in summary.values()) else \
        ("CONFIRMED" if any(v == "CONFIRMED" for v in summary.values()) else "INCONCLUSIVE")
    results.write(
        "s05/T05-2.json", {"pairs": pairs, "verdict_per_pair": summary, "verdict": overall, "explanation": EXPLANATION},
        script="code/python/langlandscape/comparison/gamma1.py (cd code/python && python3 -m langlandscape.comparison.gamma1)",
        params={"pairs": PAIRS, "n_ells": NELLS, "tol": TOL, "weight": 2},
        runtime_s=round(t.seconds, 2),
        notes="T05-2 (S05-C2): Z[X_B(U_1(N))]^0 homological; <d>_ad[x]=[x diag(1,d)]; Pi_q[x]=[x Pi_q]; "
              "dictionary T->T, <d>_cl-><d>_ad^{-delta}, U_q->+Pi_q^e; chi from a_l^2-a_{l^2}=l chi(l). "
              "Characters are recorded by their value chi(g) at the primitive root g mod N, as [re, im].",
    )


if __name__ == "__main__":
    main()
