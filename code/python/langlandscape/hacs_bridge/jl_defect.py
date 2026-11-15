# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-8: the integral JL defect comparison ``eta_f(q) = c_q(f) * eta^B`` with the GL_2 side from HACS.

Plan: ``plan/hacs/HACS-JL-PLAN.md`` section 4, HJ-8; stage tex ``plan/staged/stage-06-integral-defect.tex`` H2 (T5), H3.
Oracle and definitions: :mod:`langlandscape.defect.t5_gl2` (S06-C4), :mod:`langlandscape.defect.gram` (S06-C5),
:mod:`langlandscape.defect.t5_compare` (S06-C6), ``code/cas/s06-xcheck`` (S06-C7 / H3).

GL_2 side (HACS, binary of record; nothing of it is computed by PARI):

* ``descent(N, n, P).module_Z()`` (allowed, Fabian Q4) for ``N = q`` and ``N = 1``: the exact integer matrices ``F_l`` of
  ``T_l`` (``l`` not dividing ``N``) on ``L_N = H^1(Gamma_0(N); Sym^n Z^2)/tors`` in HACS's basis (HACS's own words: rule
  ``iso_dixon/v3``, saturation ``det_pm1``).  The prime set is split into batches (the verb takes at most 6 primes <= 97 with sum
  <= 100); the basis fingerprint ``basis_fnv`` is asserted equal across the batches, so the matrices are in one basis.
* ``level_n(q, n, ell, [q])``: the characteristic polynomial of ``U_q`` mod ``ell`` on ``H^1(Gamma_0(q); Sym^n F_ell)``
  (``ell`` not a torsion prime of ``L_q``), which gives the number of ``q``-new forms with ``a_q = +-q^{n/2}``; the signs
  are distributed over the Galois orbits by subset sum (as HJ-A1, :func:`gl2_dnew.u_d_split`).  Where several sign
  assignments fit, every one is computed and the cell is ``computed`` only if all give the same numbers.
* ``hecke_structure(q, n, "full")``: the HeckeZ record (with ``U_q``, HeckeZUp).  Its words (``C1``, components,
  ``G2.ell=p.*``, ``G3.C_T*``) are copied into every cell as ``record_words``; where it certifies the maximal ideals at
  ``p``, their ranks and Gorenstein words are compared with ours.  The record does not export ``U_q`` as a matrix and,
  at the T5 levels, stops at ``C1 = open(cap)``, so the defect numbers themselves come from the exact algebra below.

The Hecke algebra.  ``S = Z[T_l (l <= Sturm + 1, l != q), U_q]`` acting on ``S_kk(Gamma_0(q))``.  ``S`` is a subring of
``prod_s K_s`` over the Hecke eigensystems ``s`` (it acts faithfully and semisimply), so it is determined by the
eigenvalues of its generators, as elements of the fields ``K_s``:

* a ``q``-new Galois orbit ``s`` (multiplicity 2 in ``L_q``): ``K_s = Q[x]/phi_s``, ``phi_s`` an irreducible factor of the
  characteristic polynomial of a generic ``A = sum c_l T_l`` on ``L_q``, ``T_l = p_{l,s}(x)`` read off a Krylov basis of
  ``ker phi_s(A)`` (checked on the whole kernel), ``U_q = eps_s q^{n/2}``;
* a level-one Galois orbit ``g`` (multiplicity 4 in ``L_q``, 2 in ``L_1``): ``K = K_g[y]/(y^2 - a_q(g) y + q^{kk-1})`` with
  ``T_l = p_{l,g}(x)`` and ``a_q(g) = p_{q,g}(x)`` from ``L_1`` (checked equal to the level-``q`` polynomials),
  ``U_q = y``.

Every orbit that can meet ``m`` is kept (``phi_s(a) = 0 mod p`` for the residue ``a`` of ``A``, as S06-C4); each gets a
``Z``-lattice ``Lambda_s = Z[generators] * 1`` in ``K_s`` (HNF closure), and :class:`defect.hecke_alg.HeckeAlgebra` is
built on ``(+)_s Lambda_s`` with the representations ``new``, ``old``, ``o<i>``.  From there on the S06-C4 code path is
reused verbatim: maximal ideals with the residues of ``g``, :class:`defect.congruence.Character`, ``defect()``.

Definite side (HJ-8a): ``eta^B`` from :mod:`langlandscape.defect.gram` (S06-C5), read from ``code/results/s06/T5_def.json``
(T5) or recomputed by ``gram.triple`` (H3, census).  HJ-8b replaces it by the native ``quat/BrandtSym`` Gram.

Status words: ``computed`` (an exact computation), ``bound`` (an inequality only), ``open`` (not determined; the reason
is given), and the record's own words where quoted (marked as record words).  Our own text uses no stronger word.

CLI: ``python -m langlandscape.hacs_bridge.jl_defect t5 [--hacs BIN] [--out FILE] [--no-shifted]``.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import pathlib
import random
import sys
import time
from typing import Sequence

import flint

from . import runner

TRIPLES = ((13, 18, 19), (5, 18, 23), (5, 16, 31), (13, 12, 31), (3, 18, 53), (3, 18, 61), (13, 16, 101))
H3_CASES = ((13, 7, 4), (13, 7, 6), (19, 5, 4), (29, 5, 4))       # (q, p, k), p | q + 1 (S06-C7 ordering)
HACS_DEFAULT = "/home/janosch/data/hacs-build/laneB/final/hacs"
HACS_MAX_PRIME = 97          # descent: primes <= 97
HACS_MAX_BATCH = 6           # descent: at most 6 primes ...
HACS_MAX_SUM = 100           # ... with sum <= 100
HACS_MAX_N = 60              # descent / hecke_structure: n <= 60
CONFIRM_YES = 'set confirm = "yes";\n'
CALL_TIMEOUT = 1200          # 20 min per HACS call (box rule)
ORACLE_CROSSCHECK_MAX_NEW = 60   # PARI oracle cross-check of unambiguous U_q signs up to this new dimension
RECORD_TIMEOUT_SHIFTED = 600   # the HeckeZ record at k + p - 1 is optional (words only)
STATUS_WORDS = ("computed", "bound", "open")


class Refused(Exception):
    """A cell that HACS (or this driver) cannot compute; the message is the recorded reason."""


# ---------------------------------------------------------------------------------------------- small arithmetic

def primes_upto(n: int) -> list[int]:
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def sturm_bound(N: int, k: int) -> int:
    """``floor(k [SL_2(Z) : Gamma_0(N)] / 12)`` (as :func:`defect.hecke_alg.sturm_bound`)."""
    idx = N
    for ell in primes_upto(N):
        if N % ell == 0:
            idx = idx * (ell + 1) // ell
    return k * idx // 12


def vp(x: int, p: int) -> int | str:
    x = int(x)
    if x == 0:
        return "inf"
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def generators(q: int, kk: int, p: int) -> tuple[list[int], list[int]]:
    """(primes l != q used as T_l, primes dropped by the HACS cap).  S06-C4 uses primes <= Sturm + 1 plus p and q."""
    ns = sorted(set(primes_upto(sturm_bound(q, kk) + 1)) | {p})
    ns = [l for l in ns if l != q]
    return [l for l in ns if l <= HACS_MAX_PRIME], [l for l in ns if l > HACS_MAX_PRIME]


def batches(primes: Sequence[int], max_len: int = HACS_MAX_BATCH, max_sum: int = HACS_MAX_SUM) -> list[list[int]]:
    """Split ``primes`` into lists of at most ``max_len`` primes with sum ``<= max_sum`` (first fit, ascending)."""
    out: list[list[int]] = []
    for l in sorted(primes):
        if l > max_sum:
            raise ValueError(f"prime {l} exceeds the batch sum bound")
        for b in out:
            if len(b) < max_len and sum(b) + l <= max_sum:
                b.append(l)
                break
        else:
            out.append([l])
    return out


# ---------------------------------------------------------------------------------------------- HACS calls

def modz_script(N: int, n: int, prime_batches: Sequence[Sequence[int]]) -> str:
    src = [CONFIRM_YES, 'set coefficient_ring = "Z";\n']
    for i, P in enumerate(prime_batches):
        src.append(f"D{i} = descent({N}, {n}, {json.dumps(list(P))});\nZ{i} = D{i}.module_Z();\n")
        src.append(f'print("@@MZ " + json([{i}, Z{i}.status, Z{i}.free_block, Z{i}.free_rank, Z{i}.basis.rule, '
                   f'Z{i}.basis.basis_fnv, Z{i}.basis.saturation, Z{i}.torsion_primes, Z{i}.refusal, Z{i}.free_refusal]));\n')
        src.append(f'for o in Z{i}.ops {{ print("@@F " + json([o.p, o.F_proof, o.F])); }}\n')
    return "".join(src)


def hacs_modz(N: int, n: int, primes: Sequence[int], hacs=None, threads: int = 8) -> dict:
    """Exact ``T_l`` on ``L_N`` from ``module_Z()``, one basis (asserted).  Returns flint matrices and provenance words."""
    if n > HACS_MAX_N:
        raise Refused(f"descent(N, n, P): n = {n} > {HACS_MAX_N} (the verb's bound)")
    bs = batches(primes)
    heads, Fs, wall = [], [], 0.0
    for i, b in enumerate(bs):          # one HACS process per batch: every call stays inside the 20-min box cap
        try:
            r = runner.run_script(modz_script(N, n, [b]), hacs=hacs, threads=threads, timeout=CALL_TIMEOUT)
        except runner.HacsError as err:
            raise Refused(f"descent({N}, {n}, {b}).module_Z() failed: {str(err)[:300]}") from None
        heads += [[i] + h[1:] for h in r.tags.get("MZ", [])]
        Fs += r.tags.get("F", [])
        wall += r.wall_s
    if len(heads) != len(bs):
        raise Refused(f"module_Z: {len(heads)} of {len(bs)} batches answered")
    for h in heads:
        if h[1] != "ok" or h[2] != "exact" or h[6] != "det_pm1":
            raise Refused(f"module_Z refused or not exact: {h}")
    fnvs = {h[5] for h in heads}
    ranks = {h[3] for h in heads}
    assert len(fnvs) == 1 and len(ranks) == 1, f"module_Z batches in different bases: {heads}"
    T = {}
    proofs = {}
    for p, proof, F in Fs:
        T[int(p)] = flint.fmpz_mat([[int(x) for x in row] for row in F])
        proofs[int(p)] = proof
    assert set(T) == set(primes), (sorted(T), sorted(primes))
    return {"T": T, "rank": heads[0][3], "basis_rule": heads[0][4], "basis_fnv": heads[0][5],
            "saturation": heads[0][6], "torsion_primes": [int(x) for x in heads[0][7]], "F_proof": proofs,
            "batches": bs, "wall_s": round(wall, 2)}


def modz_union(N: int, n: int, primes: Sequence[int], cache: dict, hacs=None, threads: int = 8) -> dict:
    """``hacs_modz`` with a per-prime cache: only the primes not yet read for (N, n) are fetched; the HACS basis
    fingerprint is asserted equal across all reads, so the matrices are in one basis."""
    key = ("modzp", N, n)
    have = cache.get(key)
    missing = [l for l in primes if have is None or l not in have["T"]]
    if missing:
        L = hacs_modz(N, n, missing, hacs, threads)
        if have is None:
            have = dict(L)
            have["T"] = dict(L["T"])
            have["batches"] = list(L["batches"])
        else:
            assert have["basis_fnv"] == L["basis_fnv"] and have["rank"] == L["rank"], "module_Z basis changed"
            have["T"].update(L["T"])
            have["F_proof"].update(L["F_proof"])
            have["batches"] = have["batches"] + L["batches"]
            have["wall_s"] = round(have["wall_s"] + L["wall_s"], 2)
        cache[key] = have
    view = dict(have)
    view["T"] = {l: have["T"][l] for l in primes}
    return view


def hacs_uq_charpolys(q: int, n: int, ells: Sequence[int], hacs=None, threads: int = 4) -> dict:
    """``{ell: charpoly of U_q on H^1(Gamma_0(q); Sym^n F_ell)}`` (constant term first) from ``level_n``."""
    src = CONFIRM_YES + "".join(
        f'A{i} = level_n({q}, {n}, {ell}, [{q}]);\n'
        f'print("@@LN " + json([{ell}, A{i}.h1, A{i}.ops[0].label, A{i}.ops[0].bad, A{i}.ops[0].charpoly]));\n'
        for i, ell in enumerate(ells))
    r = runner.run_script(src, hacs=hacs, threads=threads, timeout=CALL_TIMEOUT)
    out = {}
    for ell, h1, label, bad, cp in r.tags.get("LN", []):
        assert bad and label.startswith("U_"), (label, bad)
        out[int(ell)] = {"h1": h1, "charpoly": [int(c) for c in cp]}
    return {"charpolys": out, "wall_s": round(r.wall_s, 2)}


RECORD_KEEP = ("G0.operators", "G0.status", "G1.C1.status", "G1.reduced_Q", "G1.theta", "G1.theta_ops",
               "G1.components", "G1.C2_status", "G3.partition", "G3.C_T.status", "G3.C_T.lower", "G3.fibre_product")


def hacs_record(q: int, n: int, p: int, hacs=None, threads: int = 8, timeout: float = CALL_TIMEOUT) -> dict:
    """The words of ``hecke_structure(q, n, "full")`` that concern this cell (see ``RECORD_KEEP`` and ``G2.ell=p``)."""
    if n > HACS_MAX_N:
        return {"status": "open", "reason": f"hecke_structure: n = {n} > {HACS_MAX_N} (the verb's bound)"}
    src = (CONFIRM_YES + 'set coefficient_ring = "Z";\n'
           f'R = hecke_structure({q}, {n}, "full");\n'
           'print("@@RS " + json([R.status, R.record_fnv1a64, R.settings_fingerprint]));\n'
           'for l in R.body { print("@@RB " + json(l)); }\n')
    try:
        r = runner.run_script(src, hacs=hacs, threads=threads, timeout=timeout)
    except runner.HacsError as err:
        return {"status": "open", "reason": f"hecke_structure not read (timeout {timeout} s or error): {str(err)[:300]}"}
    st, fnv, fp = r.tags["RS"][0]
    words = {}
    s_cand = set()
    for line in r.tags.get("RB", []):
        if line.startswith("G1.S_cand.ell="):     # G1.S_cand.ell=<l>.<field>=<value>
            s_cand.add(int(line.split("=")[1].split(".")[0]))
            continue
        if line.startswith("G2.ell=") or line.startswith("G4.ell="):   # G2.ell=<l>.<field>=<value>
            head, _, rest = line.partition(".ell=")
            ell, _, fv = rest.partition(".")
            if ell == str(p):
                f, _, v = fv.partition("=")
                words[f"{head}.ell={p}.{f}"] = v
            continue
        key, _, val = line.partition("=")
        if key in RECORD_KEEP or key.startswith("G3.C_T[") or key.startswith("G1.components["):
            words[key] = val
    ell_seen = any(k.startswith(f"G2.ell={p}.") for k in words)
    return {"status": st, "record_fnv1a64": fnv, "settings_fingerprint": fp, "words": words,
            "S_cand": sorted(s_cand), "p_in_S_cand": p in s_cand, "p_in_record_G2": ell_seen,
            "wall_s": round(r.wall_s, 2)}


# ---------------------------------------------------------------------------------------------- exact algebra

def lin(Ts: dict[int, flint.fmpz_mat], co: dict[int, int]) -> flint.fmpz_mat:
    A = None
    for l, c in co.items():
        A = Ts[l] * c if A is None else A + Ts[l] * c
    return A


def poly_at(f: flint.fmpz_poly, A: flint.fmpz_mat) -> flint.fmpz_mat:
    n = A.nrows()
    one = flint.fmpz_mat(n, n, [int(i == j) for i in range(n) for j in range(n)])
    R = flint.fmpz_mat(n, n)
    for c in reversed(f.coeffs()):
        R = R * A + one * int(c)
    return R


def kernel_cols(M: flint.fmpz_mat) -> flint.fmpz_mat:
    X, nul = M.nullspace()
    return flint.fmpz_mat([[X[i, j] for j in range(nul)] for i in range(X.nrows())])


def col(M, j):
    return [M[i, j] for i in range(M.nrows())]


def krylov_polys(A: flint.fmpz_mat, Ts: dict[int, flint.fmpz_mat], phi: flint.fmpz_poly, mult: int) -> dict[int, list]:
    """``{l: coefficients (Fractions, constant first) of p_l}`` with ``T_l = p_l(A)`` on ``ker phi(A)`` (checked there)."""
    from fractions import Fraction
    d = phi.degree()
    K = kernel_cols(poly_at(phi, A))
    assert K.ncols() == d * mult, f"dim ker phi(A) = {K.ncols()} != deg * mult = {d * mult}"
    v = flint.fmpz_mat([[K[i, 0]] for i in range(K.nrows())])
    kry = [v]
    for _ in range(d - 1):
        kry.append(A * kry[-1])
    Kr = flint.fmpq_mat(flint.fmpz_mat([[kry[j][i, 0] for j in range(d)] for i in range(K.nrows())]))
    G = Kr.transpose() * Kr
    Ginv = G.inv()
    out = {}
    powers = [flint.fmpq_mat(K)]
    for _ in range(d - 1):
        powers.append(flint.fmpq_mat(A) * powers[-1])
    for l, T in Ts.items():
        w = flint.fmpq_mat(T * v)
        c = Ginv * (Kr.transpose() * w)
        cs = [Fraction(int(c[i, 0].p), int(c[i, 0].q)) for i in range(d)]
        # check on the whole kernel: T K == sum c_i A^i K
        lhs = flint.fmpq_mat(T * K)
        rhs = None
        for i in range(d):
            term = powers[i] * flint.fmpq(cs[i].numerator, cs[i].denominator)
            rhs = term if rhs is None else rhs + term
        if lhs != rhs:
            raise ArithmeticError(f"T_{l} is not a polynomial in A on ker phi(A): A does not separate systems")
        out[l] = cs
    return out


def companion(phi: flint.fmpz_poly):
    """Rational matrix of multiplication by x on Q[x]/phi in the basis 1, x, ..., x^{d-1} (columns = images)."""
    from fractions import Fraction
    d = phi.degree()
    lc = int(phi.coeffs()[-1])
    assert lc == 1, "characteristic polynomial factors are monic"
    C = [[Fraction(0)] * d for _ in range(d)]
    for i in range(d - 1):
        C[i + 1][i] = Fraction(1)
    cs = [int(c) for c in phi.coeffs()]
    for i in range(d):
        C[i][d - 1] = Fraction(-cs[i])
    return C


def _fq(M):
    """list-of-lists of Fractions -> flint.fmpq_mat."""
    n, m = len(M), len(M[0])
    return flint.fmpq_mat(n, m, [flint.fmpq(x.numerator, x.denominator) for r in M for x in r])


def poly_matrix(cs, C: flint.fmpq_mat) -> flint.fmpq_mat:
    d = C.nrows()
    one = flint.fmpq_mat(d, d, [int(i == j) for i in range(d) for j in range(d)])
    R = flint.fmpq_mat(d, d)
    for c in reversed(cs):
        R = R * C + one * flint.fmpq(c.numerator, c.denominator)
    return R


def blockdiag(*Ms: flint.fmpq_mat) -> flint.fmpq_mat:
    n = sum(M.nrows() for M in Ms)
    R = flint.fmpq_mat(n, n)
    o = 0
    for M in Ms:
        for i in range(M.nrows()):
            for j in range(M.ncols()):
                R[o + i, o + j] = M[i, j]
        o += M.nrows()
    return R


def _hnf_basis(vecs: list[list[flint.fmpq]], D: int) -> list[list[flint.fmpq]]:
    """A Z-basis (rows) of the Z-span of rational vectors of length D."""
    den = 1
    for v in vecs:
        for x in v:
            den = den * int(x.q) // math.gcd(den, int(x.q))
    M = flint.fmpz_mat([[int(x * den) for x in v] for v in vecs])
    H = M.hnf()
    rows = [[flint.fmpq(H[i, j], den) for j in range(D)] for i in range(H.nrows()) if any(H[i, j] for j in range(D))]
    return rows


def order_lattice(gens: dict[str, flint.fmpq_mat], D: int, max_iter: int = 200,
                  start: list | None = None) -> flint.fmpq_mat:
    """Columns: a Z-basis of ``Z[gens] * start`` in Q^D (default ``start = e_0``, the element 1 of one field)."""
    basis = [list(start) if start is not None else [flint.fmpq(int(i == 0)) for i in range(D)]]
    for _ in range(max_iter):
        vecs = list(basis)
        for g in gens.values():
            for b in basis:
                bv = flint.fmpq_mat(D, 1, b)
                w = g * bv
                vecs.append([w[i, 0] for i in range(D)])
        new = _hnf_basis(vecs, D)
        if len(new) == len(basis) and new == basis:
            break
        basis = new
    else:
        raise RuntimeError("order closure did not stabilise")
    assert len(basis) == D, f"Z[gens]*1 has rank {len(basis)} < {D}"
    return flint.fmpq_mat(D, D, [basis[j][i] for i in range(D) for j in range(D)])


def int_matrix(M: flint.fmpq_mat) -> list[list[int]]:
    out = []
    for i in range(M.nrows()):
        row = []
        for j in range(M.ncols()):
            x = M[i, j]
            assert x.q == 1, "generator does not preserve the order lattice"
            row.append(int(x.p))
        out.append(row)
    return out


def system_gens(sys_: dict, names: Sequence[int], q: int, kk: int) -> dict[str, flint.fmpq_mat]:
    """Rational matrices of the generators on ``K_s`` (``T<l>`` for l in names, ``T<q>`` = U_q)."""
    C = _fq(companion(sys_["phi"]))
    d = C.nrows()
    out = {}
    if sys_["kind"] == "new":
        for l in names:
            out[f"T{l}"] = poly_matrix(sys_["evals"][l], C)
        s = q ** ((kk - 2) // 2)
        out[f"T{q}"] = flint.fmpq_mat(d, d, [int(i == j) * sys_["eps"] * s for i in range(d) for j in range(d)])
    else:
        for l in names:
            P = poly_matrix(sys_["evals"][l], C)
            out[f"T{l}"] = blockdiag(P, P)
        r = poly_matrix(sys_["evals"][q], C)
        Q = q ** (kk - 1)
        U = flint.fmpq_mat(2 * d, 2 * d)
        for i in range(d):
            U[d + i, i] = 1               # y * (x^i) = x^i y
            U[i, d + i] = -Q              # y * (x^i y) = -Q x^i + r(x) x^i y
            for j in range(d):
                U[d + j, d + i] = r[j, i]
        out[f"T{q}"] = U
    return out


def lattice_rep(sys_: dict, names, q: int, kk: int) -> dict[str, list[list[int]]]:
    g = system_gens(sys_, names, q, kk)
    D = next(iter(g.values())).nrows()
    B = order_lattice(g, D)
    Bi = B.inv()
    return {nm: int_matrix(Bi * M * B) for nm, M in g.items()}


def _elem_basis_mats(sys_: dict, q: int, kk: int) -> list[flint.fmpq_mat]:
    """Multiplication matrices of the Q-basis elements of K_s (x^j, and x^j y for an old system)."""
    C = _fq(companion(sys_["phi"]))
    d = C.nrows()
    pw = [flint.fmpq_mat(d, d, [int(i == j) for i in range(d) for j in range(d)])]
    for _ in range(d - 1):
        pw.append(pw[-1] * C)
    if sys_["kind"] == "new":
        return pw
    Y = system_gens(sys_, [], q, kk)[f"T{q}"]
    big = [blockdiag(P, P) for P in pw]
    return big + [Pm * Y for Pm in big]


class AbstractHecke:
    """Placeholder namespace (see :func:`abstract_hecke`)."""


def abstract_hecke(kept_systems: list[dict], names, q: int, kk: int, name: str = "S"):
    """The Hecke ring ``S = Z[gens] * 1`` inside ``prod_s K_s`` as a :class:`defect.hecke_alg.ZOrder` (structure constants
    on a Z-basis of ``S`` itself, rank ``D = sum_s dim K_s``), with ``kernel_of_rep(rho)`` for ``rho`` in ``new``, ``old``,
    ``o<i>`` (the projection to those factors).  Same ring as :class:`HeckeAlgebra` on ``(+)_s Lambda_s`` (tested), but
    without the ``D^2``-dimensional closure in ``End(V)``."""
    from ..defect import hecke_alg as ha
    P = ha._P()
    gm = [system_gens(s, names, q, kk) for s in kept_systems]
    gnames = [f"T{l}" for l in names] + [f"T{q}"]
    G = {g: blockdiag(*[m[g] for m in gm]) for g in gnames}
    sizes = [next(iter(m.values())).nrows() for m in gm]
    offs = [0]
    for z in sizes:
        offs.append(offs[-1] + z)
    D = offs[-1]
    start = [flint.fmpq(0)] * D
    for o in offs[:-1]:
        start[o] = flint.fmpq(1)
    B = order_lattice(G, D, start=start)
    Bi = B.inv()
    E = [_elem_basis_mats(s, q, kk) for s in kept_systems]

    def mult_matrix(vcol):              # multiplication by the element with coordinates vcol (in Q^D) on Q^D
        blocks = []
        for b, s in enumerate(kept_systems):
            z = sizes[b]
            M = flint.fmpq_mat(z, z)
            for t in range(z):
                c = vcol[offs[b] + t]
                if c != 0:
                    M = M + E[b][t] * c
            blocks.append(M)
        return blockdiag(*blocks)

    def to_int_vec(v):
        out = []
        for i in range(v.nrows()):
            x = v[i, 0]
            assert x.q == 1, "not in the order"
            out.append(int(x.p))
        return out

    L = []
    for i in range(D):
        Mi = Bi * mult_matrix([B[t, i] for t in range(D)]) * B
        L.append(P.matrix(D, D, [int(x) for x in int_matrix(Mi) for x in x]))
    one = to_int_vec(Bi * flint.fmpq_mat(D, 1, start))
    gens = {g: to_int_vec(Bi * (G[g] * flint.fmpq_mat(D, 1, start))) for g in gnames}
    T = ha.ZOrder(L, one, gens, name)
    groups = {"new": [b for b, s in enumerate(kept_systems) if s["kind"] == "new"],
              "old": [b for b, s in enumerate(kept_systems) if s["kind"] == "old"]}
    orbit_names = {}
    for b, s in enumerate(kept_systems):
        if s["kind"] == "new":
            nm = f"o{len(orbit_names)}"
            orbit_names[nm] = b
            groups[nm] = [b]

    def rep_hom(rho):
        rows = [t for b in groups[rho] for t in range(offs[b], offs[b + 1])]
        if not rows:
            return ha.ZHom(T, 0, None)
        den = 1
        for t in rows:
            for j in range(D):
                den = den * int(B[t, j].q) // math.gcd(den, int(B[t, j].q))
        A = P.matrix(len(rows), D, [int(B[t, j] * den) for t in rows for j in range(D)])
        return ha.ZHom(T, len(rows), A)

    T.rep_hom = rep_hom
    T.kernel_of_rep = lambda rho: rep_hom(rho).kernel()
    T.orbit_names = orbit_names
    return T


def blockdiag_int(blocks: list[list[list[int]]]) -> list[list[int]]:
    n = sum(len(b) for b in blocks)
    R = [[0] * n for _ in range(n)]
    o = 0
    for b in blocks:
        for i, row in enumerate(b):
            R[o + i][o:o + len(row)] = row
        o += len(b)
    return R


# ---------------------------------------------------------------------------------------------- systems from HACS data

def _root_mod_p(f: flint.fmpz_poly, a: int, p: int) -> bool:
    return int(f(a)) % p == 0


def eisenstein_value(co: dict[int, int], kk: int) -> int:
    return sum(c * (1 + l ** (kk - 1)) for l, c in co.items())


def classify(Lq: dict, L1: dict, co: dict[int, int], kk: int) -> list[dict]:
    """All Hecke systems of ``L_q`` (``A = sum c_l T_l``): ``kind`` in {eis, old, new}, ``phi``, multiplicity."""
    Aq, A1 = lin(Lq["T"], co), lin(L1["T"], co)
    _, fq = Aq.charpoly().factor()
    _, f1 = A1.charpoly().factor()
    lvl1 = {str(f): m for f, m in f1}
    e = eisenstein_value(co, kk)
    out = []
    for f, m in fq:
        if f.degree() == 1 and int(f(e)) == 0:
            kind = "eis"
        elif str(f) in lvl1:
            kind = "old"
        else:
            kind = "new"
        out.append({"phi": f, "mult": int(m), "kind": kind, "level1_mult": lvl1.get(str(f))})
    return out


def sign_counts(cp: list[int], ell: int, q: int, kk: int, t1_cusp: flint.fmpz_poly) -> tuple[int, int]:
    """(# of q-new forms with a_q = +q^{n/2}, with a_q = -q^{n/2}) from the U_q charpoly mod ell (gl2_dnew.u_d_split)."""
    from .gl2_dnew import u_d_split
    a, b = u_d_split(cp, ell, q, kk, t1_cusp)
    assert a % 2 == 0 and b % 2 == 0, (a, b)
    return a // 2, b // 2


def sign_solutions(new_degrees: list[int], n_plus: int, cap: int = 64) -> list[tuple[int, ...]]:
    """All +-1 assignments to the new orbits with total degree n_plus on '+' (at most ``cap``; more -> RuntimeError)."""
    sols: list[tuple[int, ...]] = []

    def rec(i, rem, cur):
        if len(sols) > cap:
            return
        if i == len(new_degrees):
            if rem == 0:
                sols.append(cur)
            return
        d = new_degrees[i]
        if d <= rem:
            rec(i + 1, rem - d, cur + (1,))
        rec(i + 1, rem, cur + (-1,))

    rec(0, n_plus, ())
    if len(sols) > cap:
        raise RuntimeError(f"more than {cap} sign assignments")
    return sols


# ---------------------------------------------------------------------------------------------- one cell

def pari_newform_signs(q: int, kk: int, orbits: list[dict], ells: Sequence[int]) -> list[int] | None:
    """Independent oracle (team lead, source (b)): the sign eps of a_q(f) = eps q^{(kk-2)/2} of each HACS new orbit,
    read from PARI's q-new eigenforms of S_kk(Gamma_0(q)).  A HACS orbit (``phi``, ``evals``) is matched to a PARI
    orbit by the characteristic polynomials over Q of T_l, l in ``ells``; returns None unless the matching is a
    bijection onto distinct keys.  Never uses the definite side."""
    from ..pari import get_pari
    P = get_pari()
    mf = P.mfinit([q, kk], 0)                       # the new space
    fields = P.mffields(mf)
    forms = P.mfeigenbasis(mf)
    B = max(max(ells), q)
    s_ = q ** ((kk - 2) // 2)
    pari_keys = []
    for F, pol in zip(forms, fields):
        c = P.mfcoefs(F, B)
        pol = P.subst(pol, P.variable(pol), "y")
        key = []
        for l in ells:
            el = P.Mod(P.lift(c[l]) if str(P.type(c[l])) == "t_POLMOD" else c[l], pol) if P.poldegree(pol) > 0 else c[l]
            cp = P.charpoly(el) if P.poldegree(pol) > 0 else P("x") - c[l]
            key.append(str(cp))
        aq = c[q]
        aq = P.simplify(P.lift(aq) if str(P.type(aq)) == "t_POLMOD" else aq)
        if str(P.type(aq)) not in ("t_INT", "t_FRAC") or abs(int(aq)) != s_:
            return None
        pari_keys.append((tuple(key), 1 if int(aq) > 0 else -1))
    hk = []
    for o in orbits:
        C = _fq(companion(o["phi"]))
        key = []
        for l in ells:
            M = poly_matrix(o["evals"][l], C)
            cp = M.charpoly()                       # fmpq_poly
            key.append(str(P.Pol([P(f"{int(c.p)}/{int(c.q)}") for c in reversed(cp.coeffs())])))
        hk.append(tuple(key))
    pk = [k_ for k_, _ in pari_keys]
    if len(set(pk)) != len(pk) or len(set(hk)) != len(hk):
        return None
    lut = dict(pari_keys)
    if any(k_ not in lut for k_ in hk):
        return None
    return [lut[k_] for k_ in hk]


def pick_ells_for_signs(q: int, p: int, kk: int, torsion: Sequence[int], count: int = 2) -> list[int]:
    s = q ** ((kk - 2) // 2)
    out = []
    for ell in primes_upto(400):
        if ell < 5 or ell in (p, q) or ell in torsion or (2 * s) % ell == 0:
            continue
        out.append(ell)
        if len(out) == count:
            break
    return out


def gl2_cell(q: int, k: int, p: int, kk: int | None = None, hacs=None, residues: dict[int, int] | None = None,
             data_cache: dict | None = None, threads: int = 8, route: str = "local") -> dict:
    """GL_2 side of one cell through HACS.  ``residues``: the T_l residues of m (default: the level-one form of weight k).

    Returns the S06-C4 field set (``components`` / ``forms`` / ``ord``), plus ``hacs`` provenance words."""
    from ..defect import hecke_alg as ha
    from ..defect.congruence import Character, defect, place_info
    from ..defect.t5_gl2 import _matching_ideals

    kk = k if kk is None else kk
    n = kk - 2
    t0 = time.perf_counter()
    names, dropped = generators(q, kk, p)
    if residues is not None:       # every T_l that defines m is a generator (the definite m_id uses l <= 11)
        names = sorted(set(names) | {int(l) for l in residues if int(l) != q and int(l) <= HACS_MAX_PRIME})
    cache = {} if data_cache is None else data_cache
    lvl1_primes = sorted(set(names) | {q})

    def get(key, fn):
        if key not in cache:
            cache[key] = fn()
        return cache[key]

    if kk <= 2:
        raise Refused("weight 2 is not handled by this driver (no level-one cohomology; Eisenstein multiplicity 1)")
    Lq = modz_union(q, n, names, cache, hacs, threads)
    L1 = modz_union(1, n, lvl1_primes, cache, hacs, threads)
    # level-one form of weight k (the branch of m): its T_l residues (dim S_k(1) = 1 asserted)
    g = None
    if residues is None:
        Lk = L1 if kk == k else modz_union(1, k - 2, lvl1_primes, cache, hacs, threads)
        g = level_one_rational(Lk, k)
        residues = {l: g[l] % p for l in names if l != p}
        out_m = "the level-one eigenform g of weight k (T5)"
    else:
        residues = {int(l): int(r) % p for l, r in residues.items()}
        if kk == k and L1["rank"] == 3:
            g = level_one_rational(L1, k)
        out_m = "given residues a_l mod p (the definite block's m_id)"
    out = {"q": q, "k": k, "p": p, "weight": kk, "hecke_generators": names + [q], "dropped_by_hacs_cap": dropped,
           "algebra_route": route, "m_defined_by": out_m, "m_residues": {str(l): r for l, r in sorted(residues.items())},
           "hacs": {"L_q": _modz_words(Lq), "L_1": _modz_words(L1)}}
    if g is not None and kk == k:
        out["t_f_q"] = vp(g[q] ** 2 - q ** (k - 2) * (q + 1) ** 2, p)
        out["a_p_g_mod_p"] = g[p] % p if p in g else None
        out["level_one_g_mod_p_matches_m"] = all(g[l] % p == r for l, r in residues.items() if l in g and l != p)
    elif L1["rank"] == 1:
        out["t_f_q"] = 0
        out["t_f_q_reason"] = "S_k(SL_2(Z)) = 0: no old form, c_q(f) = (1) and t_f(q) = 0 (vacuous, S06-xcheck doubt 1)"
    # generic A over small primes avoiding p (residue known)
    rng = random.Random(1)
    a_primes = [l for l in names if l != p and l in residues][:4]
    for attempt in range(8):
        co = {l: rng.randrange(1, 30) for l in a_primes}
        systems = classify(Lq, L1, co, kk)
        try:
            kept = _kept_systems(systems, Lq, L1, co, residues, p, q, kk, names)
            break
        except ArithmeticError:
            continue
    else:
        raise Refused("no separating generic operator found")
    out["generic_A"] = {str(l): c for l, c in co.items()}
    news = [s for s in systems if s["kind"] == "new"]
    olds = [s for s in systems if s["kind"] == "old"]
    out["dims"] = {"L_q": Lq["rank"], "new": sum(s["phi"].degree() for s in news),
                   "old_level1": sum(s["phi"].degree() for s in olds),
                   "full": sum(s["phi"].degree() for s in news) + 2 * sum(s["phi"].degree() for s in olds)}
    _check_multiplicities(systems)
    # U_q signs on the new orbits
    t1 = cusp_charpoly_level1(L1, q, kk)
    ells = pick_ells_for_signs(q, p, kk, Lq["torsion_primes"])
    U = get(("uq", q, n, tuple(ells)), lambda: hacs_uq_charpolys(q, n, ells, hacs))
    counts = {ell: sign_counts(U["charpolys"][ell]["charpoly"], ell, q, kk, t1) for ell in ells}
    assert len(set(counts.values())) == 1, f"U_q sign counts differ between ells: {counts}"
    n_plus, n_minus = next(iter(counts.values()))
    assert n_plus + n_minus == out["dims"]["new"], (n_plus, n_minus, out["dims"])
    sols = sign_solutions([s["phi"].degree() for s in news], n_plus)
    kept_new_idx = [i for i, s in enumerate(news) if any(s is t["sys"] for t in kept if t["sys"]["kind"] == "new")]
    projected = sorted({tuple(sol[i] for i in kept_new_idx) for sol in sols})
    out["U_q_signs"] = {"n_plus": n_plus, "n_minus": n_minus, "ells": ells, "assignments_total": len(sols),
                        "assignments_on_kept_orbits": [list(x) for x in projected],
                        "source": "HACS level_n(q, n, ell, [q]) charpoly of U_q mod ell; subset sum over new orbits"}
    if len(projected) > 1:
        kept_new = [news[i] for i in kept_new_idx]
        small = [l for l in names if l != p][:3]
        try:
            ps = pari_newform_signs(q, kk, kept_new, small)
        except Exception as err:            # the oracle failing leaves the ambiguity in place
            ps = None
            out["U_q_signs"]["oracle_error"] = f"{type(err).__name__}: {str(err)[:200]}"
        out["U_q_signs"]["oracle"] = ("PARI mfinit([q,kk],0) q-new eigenforms, a_q(f), orbits matched by charpolys of "
                                      f"T_l, l in {small} (team-lead source (b); independent of the definite side)")
        if ps is not None and tuple(ps) in projected:
            projected = [tuple(ps)]
            out["U_q_signs"]["resolved_by_oracle"] = ps
        else:
            out["U_q_signs"]["resolved_by_oracle"] = None
            out["U_q_signs"]["oracle_result"] = ps
    elif projected and kept_new_idx and out["dims"]["new"] <= ORACLE_CROSSCHECK_MAX_NEW:
        # unambiguous HACS signs: the PARI oracle as an independent cross-check of the level_n route
        try:
            ps = pari_newform_signs(q, kk, [news[i] for i in kept_new_idx], [l for l in names if l != p][:3])
        except Exception as err:
            ps = None
            out["U_q_signs"]["oracle_error"] = f"{type(err).__name__}: {str(err)[:200]}"
        out["U_q_signs"]["oracle_crosscheck"] = None if ps is None else (tuple(ps) == tuple(projected[0]))
    variants = []
    for signs in projected:
        for i, s in zip(kept_new_idx, signs):
            news[i]["eps"] = s
        fn = _defects_local if route == "local" else _defects_on
        variants.append(fn(kept, names, q, kk, p, residues, ha, Character, defect, place_info, _matching_ideals))
    out["components"] = variants[0]["components"]
    out["orbit_degrees"] = variants[0]["orbit_degrees"]
    out["old_factor_degrees"] = variants[0]["old_factor_degrees"]
    out["sign_robust"] = all(_strip(v["components"]) == _strip(variants[0]["components"]) for v in variants)
    if len(variants) > 1:
        out["variants"] = [{"signs": list(sg), "components": v["components"]} for sg, v in zip(projected, variants)]
    out["status"] = "computed" if out["sign_robust"] else "open"
    if not out["sign_robust"]:
        out["reason"] = ("open (U_q-sign ambiguity on new orbits): the HACS sign assignment is ambiguous, changes the "
                         "numbers, and the PARI newform oracle did not settle it")
    out["runtime_s"] = round(time.perf_counter() - t0, 2)
    return out


def _strip(comps):
    return json.dumps(comps, sort_keys=True, default=str)


def _modz_words(L: dict) -> dict:
    return {k: L[k] for k in ("rank", "basis_rule", "basis_fnv", "saturation", "torsion_primes", "batches", "wall_s")}


def level_one_rational(L1: dict, k: int) -> dict[int, int]:
    """``a_l(g)`` of the unique level-one eigenform of weight k (dim S_k(1) = 1 asserted) from HACS ``L_1``."""
    rank = L1["rank"]
    assert rank == 3, f"dim S_{k}(1) != 1 (rank L_1 = {rank})"
    out = {}
    for l, T in L1["T"].items():
        _, fac = T.charpoly().factor()
        eis = 1 + l ** (k - 1)
        cusp = [f for f, m in fac if not (f.degree() == 1 and int(f(eis)) == 0)]
        assert len(cusp) == 1 and cusp[0].degree() == 1, (l, fac)
        out[l] = -int(cusp[0].coeffs()[0])
    return out


def cusp_charpoly_level1(L1: dict, q: int, kk: int) -> flint.fmpz_poly:
    """Charpoly of T_q on S_kk(SL_2(Z)) from HACS: chi(T_q | L_1) = (x - 1 - q^{kk-1}) * chi_cusp^2."""
    x = flint.fmpz_poly([0, 1])
    chi = L1["T"][q].charpoly()
    rest, r = divmod(chi, x - (1 + q ** (kk - 1)))
    assert r == 0
    _, fac = rest.factor()
    out = flint.fmpz_poly([1])
    for f, m in fac:
        assert m % 2 == 0
        out *= f ** (m // 2)
    return out


def _check_multiplicities(systems: list[dict]) -> None:
    for s in systems:
        want = {"eis": 2, "old": 4, "new": 2}[s["kind"]]
        assert s["mult"] == want, f"{s['kind']} system with multiplicity {s['mult']} (expected {want})"


def _kept_systems(systems, Lq, L1, co, residues, p, q, kk, names):
    a = sum(c * residues[l] for l, c in co.items()) % p
    kept = []
    for s in systems:
        if s["kind"] == "eis" or not _root_mod_p(s["phi"], a, p):
            continue
        Aq = lin(Lq["T"], co)
        evq = krylov_polys(Aq, {l: Lq["T"][l] for l in names}, s["phi"], s["mult"])
        if s["kind"] == "old":
            A1 = lin(L1["T"], co)
            ev1 = krylov_polys(A1, {l: L1["T"][l] for l in sorted(set(names) | {q})}, s["phi"], 2)
            assert all(ev1[l] == evq[l] for l in names), "old system: level-1 and level-q eigenvalues differ"
            s["evals"] = ev1
        else:
            s["evals"] = evq
        kept.append({"sys": s})
    return kept


LOCAL_E = 40          # p-adic working precision of the local route (every valuation read is checked < E - 1)


def _padic_int_mod(x, p: int, E: int) -> int:
    """A p-adic integer (PARI t_PADIC / rational) as an integer mod p^E (asserts integrality and precision >= E)."""
    from ..defect import hecke_alg as ha
    P = ha._P()
    if str(P.type(x)) == "t_PADIC":
        if x == 0:
            return 0
        assert int(P.valuation(x, p)) >= 0, "non-integral p-adic eigenvalue"
        assert int(P.padicprec(x, p)) >= E, "p-adic precision lost"
        return int(P.lift(P.truncate(x))) % p ** E if int(P.valuation(x, p)) < E else 0
    num, den = int(P.numerator(x)), int(P.denominator(x))
    assert den % p, "non-integral eigenvalue"
    return num * pow(den, -1, p ** E) % p ** E


def local_places(kept: list[dict], names, q: int, kk: int, p: int, E: int = LOCAL_E,
                 resid: dict | None = None) -> list[dict]:
    """Every place v of degree 1 (e = f = 1) above p of the kept systems, with lam_v(generator) mod p^E.

    A ramified p-adic factor (reduction (x - c)^d, d > 1) is refused: the local route needs O_v = Z_p."""
    from ..defect import hecke_alg as ha
    P = ha._P()
    X = 2 * E + 20                       # extra precision for the rational Krylov coefficients
    out = []
    for b, s in enumerate(kept):
        phi = P.Pol([int(c) for c in reversed(s["phi"].coeffs())])
        fa = P.factorpadic(phi, p, X)
        for i in range(int(P.matsize(fa)[0])):
            f = fa[0][i]
            d = int(P.poldegree(f))
            if d == 1:
                continue
            red = P.factormod(P.Pol([int(P.lift(P.truncate(c))) % p for c in P.Vec(f)]), p)
            if int(P.matsize(red)[0]) == 1 and int(P.poldegree(red[0][0])) == 1:
                # a place with residue field F_p but e > 1: theta = c mod the prime.  It matters only if it lies in m,
                # i.e. if every T_l residue p_l(c) mod p equals that of m (needs p-integral Krylov coefficients).
                c0 = -int(P.lift(P.polcoef(red[0][0], 0))) % p
                in_m = True
                if resid:
                    for gname, rv in resid.items():
                        l = int(gname[1:])
                        if l not in s["evals"]:
                            continue             # no eigenvalue polynomial for this generator: no information
                        cs = s["evals"][l]
                        if any(c.denominator % p == 0 for c in cs):
                            break                # residue not readable from the coefficients: treat as in m
                        val = sum(c.numerator * pow(c.denominator, -1, p) * pow(c0, j, p) for j, c in enumerate(cs)) % p
                        if val != rv:
                            in_m = False
                            break
                if in_m:
                    raise Refused(f"ramified place above p = {p} (degree {d}, residue {c0}) can lie in m: "
                                  "O_v is not Z_p")
        for th in P.polrootspadic(phi, p, X):
            lam = {}
            for l in names:
                cs = s["evals"][l]
                val = sum(P(f"{c.numerator}/{c.denominator}") * th ** j for j, c in enumerate(cs))
                lam[f"T{l}"] = _padic_int_mod(val, p, E)
            if resid and any(lam[g] % p != v for g, v in resid.items()):
                continue                         # this place is not in m
            if s["kind"] == "new":
                out.append({"sys": b, "kind": "new", "lam": {**lam, f"T{q}": s["eps"] * q ** ((kk - 2) // 2) % p ** E},
                            "degree": s["phi"].degree(), "eps": s["eps"]})
            else:
                cs = s["evals"][q]
                aq = sum(P(f"{c.numerator}/{c.denominator}") * th ** j for j, c in enumerate(cs))
                y = P.Pol([1, -aq, q ** (kk - 1)])
                ys = P.polrootspadic(y, p, X)
                if len(ys) != 2:
                    raise Refused("old system: y^2 - a_q y + q^(kk-1) does not split over Z_p at a place in play")
                for yy in ys:
                    out.append({"sys": b, "kind": "old", "lam": {**lam, f"T{q}": _padic_int_mod(yy, p, E)},
                                "degree": s["phi"].degree()})
    return out


def local_order(places: list[dict], gnames: list[str], p: int, E: int = LOCAL_E):
    """R = Z[lam_v(gens)] + p^E Z^r in Z^r (componentwise ring).  R (x) Z_p = S_m exactly when p^(E-1) Z^r is in R
    (checked; Nakayama), and R (x) Z_l = Z_l^r for l != p.  Returns a ZOrder with kernel_of_rep for new/old/o<i>."""
    from ..defect import hecke_alg as ha
    P = ha._P()
    r = len(places)
    Q = p ** E
    vec = {g: [pl["lam"][g] % Q for pl in places] for g in gnames}
    basis = [[1] * r] + [[Q * int(i == j) for j in range(r)] for i in range(r)]

    def hnf(vs):
        M = flint.fmpz_mat(vs)
        H = M.hnf()
        return [[int(H[i, j]) for j in range(r)] for i in range(H.nrows()) if any(H[i, j] for j in range(r))]

    cur = hnf(basis)
    for _ in range(10 * E * r + 10):
        prods = [[(a * b) % Q for a, b in zip(v, vec[g])] for v in cur for g in gnames]
        nxt = hnf(cur + prods + basis[1:])
        if nxt == cur:
            break
        cur = nxt
    else:
        raise RuntimeError("local order closure did not stabilise")
    assert len(cur) == r
    B = flint.fmpz_mat(cur).transpose()            # columns = Z-basis of R
    Bi = flint.fmpq_mat(B).inv()
    for i in range(r):                             # p^(E-1) e_i in R  <=>  R (x) Z_p = S_m
        e = flint.fmpq_mat(r, 1, [Q // p * int(j == i) for j in range(r)])
        c = Bi * e
        if any(c[j, 0].q != 1 for j in range(r)):
            raise Refused(f"local route: precision p^{E} below the conductor of S_m (raise LOCAL_E)")

    def coords(v):
        c = Bi * flint.fmpq_mat(r, 1, v)
        assert all(c[j, 0].q == 1 for j in range(r))
        return [int(c[j, 0].p) for j in range(r)]

    L = []
    for i in range(r):
        bi = [int(B[t, i]) for t in range(r)]
        cols = [coords([bi[t] * int(B[t, j]) for t in range(r)]) for j in range(r)]
        L.append(P.matrix(r, r, [cols[j][t] for t in range(r) for j in range(r)]))
    T = ha.ZOrder(L, coords([1] * r), {g: coords(vec[g]) for g in gnames}, "S_m(local)")
    groups = {"new": [i for i, pl in enumerate(places) if pl["kind"] == "new"],
              "old": [i for i, pl in enumerate(places) if pl["kind"] == "old"]}
    k = 0
    for i, pl in enumerate(places):
        if pl["kind"] == "new":
            groups[f"o{k}"] = [i]
            pl["rep"] = f"o{k}"
            k += 1

    def rep_hom(rho):
        rows = groups[rho]
        if not rows:
            return ha.ZHom(T, 0, None)
        return ha.ZHom(T, len(rows), P.matrix(len(rows), r, [int(B[t, j]) for t in rows for j in range(r)]))

    T.rep_hom = rep_hom
    T.kernel_of_rep = lambda rho: rep_hom(rho).kernel()
    return T


def _defects_local(kept, names, q, kk, p, residues, ha, Character, defect, place_info, _matching_ideals,
                   E: int = LOCAL_E):
    """As :func:`_defects_on`, through the local route (one ZOrder per maximal ideal, places of degree 1 only)."""
    gnames = [f"T{l}" for l in names] + [f"T{q}"]
    resid = {f"T{l}": r % p for l, r in residues.items()}
    places = local_places([t["sys"] for t in kept], names, q, kk, p, E, resid)
    places = [pl for pl in places if all(pl["lam"][g] % p == v for g, v in resid.items())]
    groups: dict = {}
    for pl in places:
        groups.setdefault(tuple(pl["lam"][g] % p for g in gnames), []).append(pl)
    comps = []
    for key, pls in groups.items():
        T = local_order(pls, gnames, p, E)
        a_, b_ = T.kernel_of_rep("new"), T.kernel_of_rep("old")
        Sn, qn = T.quotient(a_, name="T'")
        So, qo = T.quotient(b_, name="T''")
        ms = _matching_ideals(T, p, resid)
        assert len(ms) == 1, "local order is not local at p"
        m = ms[0]
        mn, mo = ha.push_max_ideal(m, qn), ha.push_max_ideal(m, qo)
        Tp = m.values.get(f"T{p}")
        comp = {"m": m.describe(), "T_p_residue": Tp, "ordinary": Tp not in (0, None),
                "U_q_residue": m.values.get(f"T{q}"),
                "ranks": {"S_m": m.local_rank, "S_new_m": mn.local_rank if mn else 0,
                          "S_old_m": mo.local_rank if mo else 0},
                "forms": [], "route": f"local (places of degree 1, precision p^{E})"}
        comp["rk_new_ge_2"] = comp["ranks"]["S_new_m"] >= 2
        comp["rk_full_ge_2"] = comp["ranks"]["S_m"] >= 2
        if mn is None:
            comp["note"] = "no q-new form in m"
            comps.append(comp)
            continue
        for pl in pls:
            if pl["kind"] != "new":
                continue
            chi = Character.from_rep(T, pl["rep"])
            v = chi.place(m)
            pinfo = place_info(v)
            row = {"orbit_degree": pl["degree"], "a_q_sign": pl["eps"],
                   "place": {kx: str(x) if not isinstance(x, (int, bool)) else x for kx, x in pinfo.items()}}
            r = defect(T, chi, m)
            for kx in ("eta", "c", "eta_new"):
                val = r["ord"][kx]
                assert val == "inf" or int(val) < E - 1, "valuation reaches the working precision"
            row.update({"status": "computed", "ord": r["ord"], "thm_E_identity": r["thm_E_identity"],
                        "gorenstein": r["gorenstein"], "lemma_D": r["lemma_D"],
                        "congruence_module_length": r["congruence_module_length"]})
            comp["forms"].append(row)
        comps.append(comp)
    kept_new = [t["sys"] for t in kept if t["sys"]["kind"] == "new"]
    return {"components": comps, "orbit_degrees": [s["phi"].degree() for s in kept_new],
            "old_factor_degrees": [t["sys"]["phi"].degree() for t in kept if t["sys"]["kind"] == "old"]}


def _defects_on(kept, names, q, kk, p, residues, ha, Character, defect, place_info, _matching_ideals,
                use_matrix_algebra: bool = False):
    orbits = []
    for t in kept:
        s = t["sys"]
        if s["kind"] == "new":
            orbits.append({"rep": f"o{len(orbits)}", "degree": s["phi"].degree(), "eps": s["eps"]})
    gnames = [f"T{l}" for l in names] + [f"T{q}"]
    if use_matrix_algebra:          # the S06-C4 route: closure in End((+)_s Lambda_s) (D^2-dimensional; small cells)
        per = [(t["sys"], lattice_rep(t["sys"], names, q, kk)) for t in kept]
        gens = {g: blockdiag_int([L[g] for _, L in per]) for g in gnames}
        reps = {r: {g: blockdiag_int([L[g] for s, L in per if s["kind"] == r]) for g in gnames} for r in ("new", "old")}
        i = 0
        for s, L in per:
            if s["kind"] == "new":
                reps[f"o{i}"] = L
                i += 1
        T = ha.HeckeAlgebra(gens, reps, name=f"T_{kk}({q})_W[HACS]")
    else:
        T = abstract_hecke([t["sys"] for t in kept], names, q, kk, name=f"T_{kk}({q})_W[HACS]")
    resid = {f"T{l}": r for l, r in residues.items()}
    a_, b_ = T.kernel_of_rep("new"), T.kernel_of_rep("old")
    Sn, qn = T.quotient(a_, name="T'")
    So, qo = T.quotient(b_, name="T''")
    comps = []
    for m in _matching_ideals(T, p, resid):
        mn, mo = ha.push_max_ideal(m, qn), ha.push_max_ideal(m, qo)
        Tp = m.values.get(f"T{p}")
        comp = {"m": m.describe(), "T_p_residue": Tp, "ordinary": Tp not in (0, None),
                "U_q_residue": m.values.get(f"T{q}"),
                "ranks": {"S_m": m.local_rank, "S_new_m": mn.local_rank if mn else 0,
                          "S_old_m": mo.local_rank if mo else 0},
                "forms": []}
        comp["rk_new_ge_2"] = comp["ranks"]["S_new_m"] >= 2
        comp["rk_full_ge_2"] = comp["ranks"]["S_m"] >= 2
        if mn is None:
            comp["note"] = "no q-new form in m"
            comps.append(comp)
            continue
        for o in orbits:
            chi = Character.from_rep(T, o["rep"])
            try:
                v = chi.place(m)
            except ValueError as err:
                if "does not factor" in str(err):
                    continue
                raise
            pinfo = place_info(v)
            row = {"orbit_degree": o["degree"], "a_q_sign": o["eps"],
                   "place": {kx: str(x) if not isinstance(x, (int, bool)) else x for kx, x in pinfo.items()}}
            if not pinfo["dvr"]:
                row["status"] = "open"
                row["reason"] = "O_v not a DVR"
            else:
                r = defect(T, chi, m)
                row.update({"status": "computed", "ord": r["ord"], "thm_E_identity": r["thm_E_identity"],
                            "gorenstein": r["gorenstein"], "lemma_D": r["lemma_D"],
                            "congruence_module_length": r["congruence_module_length"]})
            comp["forms"].append(row)
        comps.append(comp)
    return {"components": comps, "orbit_degrees": [o["degree"] for o in orbits],
            "old_factor_degrees": [t["sys"]["phi"].degree() for t in kept if t["sys"]["kind"] == "old"]}


# ---------------------------------------------------------------------------------------------- T5 comparison

def _gl2_form(w: dict):
    comps = [c for c in w.get("components", []) if c["forms"]]
    if len(comps) != 1 or len(comps[0]["forms"]) != 1:
        return None, None
    return comps[0], comps[0]["forms"][0]


def compare_row(g: dict, dB: dict | None, oracle_gl2: dict | None) -> dict:
    """One weight of one triple: the identity eta = c * eta^B and the agreement with S06-C4 / S06-C6."""
    comp, f = _gl2_form(g)
    row = {"weight": g["weight"], "gl2_status": g.get("status")}
    if f is None or f.get("status") != "computed":
        row.update({"status": "open", "reason": "no unique computed q-new form at m on the GL_2 side"})
        return row
    o = f["ord"]
    row.update({"ord_eta": o["eta"], "ord_c": o["c"], "ord_eta_new": o["eta_new"], "thm_E_identity": f["thm_E_identity"],
                "gorenstein_S_m": f["gorenstein"]["S_m"], "ranks": comp["ranks"], "ordinary": comp["ordinary"],
                "U_q_residue": comp["U_q_residue"], "a_q_sign": f["a_q_sign"], "place": f["place"],
                "t_f_q": g.get("t_f_q"), "sign_robust": g.get("sign_robust")})
    if dB is not None and dB.get("m") and len(dB["m"]["vp_etaB"]) == 1 and dB["m"]["rank"] == 1:
        eB = dB["m"]["vp_etaB"][0]
        row["vp_etaB"] = eB
        row["etaB_source"] = dB.get("_source", "S06-C5")
        row["etaB_eq_eta_new"] = eB == o["eta_new"]
        row["identity_with_etaB"] = o["eta"] == o["c"] + eB
        row["rank_new_definite"] = dB["m"]["rank"]
        row["dims_agree"] = dB["dim_brandt"] == g["dims"]["new"]
        row["status"] = "computed" if g.get("status") == "computed" else "open"
    else:
        row["vp_etaB"] = None
        row["etaB_status"] = "open"
        row["etaB_reason"] = ("eta^B not available at this weight from the Python oracle (S06-C5 needs p > k - 2); "
                              "native Sym^n Gram pending (HJ-8b)")
        row["status"] = "computed" if g.get("status") == "computed" else "open"
        row["identity_scope"] = "GL_2 side only (Thm E: eta = c * eta_new)"
    if oracle_gl2 is not None:
        oc, of = _gl2_form(oracle_gl2)
        if of is not None and "ord" in of:
            row["oracle_S06_C4"] = {"ord": {k: of["ord"][k] for k in ("eta", "c", "eta_new")},
                                    "ranks": oc["ranks"], "U_q_residue": oc.get("U_q_residue")}
            row["agrees_with_S06_C4"] = (all(of["ord"][k] == o[k] for k in ("eta", "c", "eta_new"))
                                         and oc["ranks"] == comp["ranks"])
        else:
            row["oracle_S06_C4"] = {"status": oracle_gl2.get("status", "not computed"),
                                    "reason": oracle_gl2.get("reason")}
    return row


NATIVE_REL = "code/results/laneC/hj8_def_native.json"


def annotate_native(rows: dict, native: dict) -> None:
    """Add worker C's native definite side (``hj8_def_native.json``, HJ-4a BrandtSym) to every T5 row.

    Weight k: the Gram eta^B at m (``vp_etaB_m``) is compared with the Python S06-C5 value (native = Python cross-check)
    and with eta_new.  Weight k + (p - 1): the ring-theoretic eta^B of the weight-k m (``m_from_weight_k``, matched by
    residual a_l mod p) gives the identity eta = c * eta^B there; the Gram values at p <= n are not eta^B and are not used."""
    by = {(r["cell"], r["weight_role"]): r for r in native["T5_comparison"]["rows"]}
    for key, row in rows.items():
        rk = row.get("k")
        nk = by.get((key, "k"))
        if rk is not None and nk is not None:
            v = nk.get("vp_etaB_m")
            rk["etaB_native"] = {"vp_etaB_m": v, "source": NATIVE_REL + " (Gram G_w, BrandtSym)"}
            if v is not None and len(v) == 1 and rk.get("vp_etaB") is not None:
                rk["etaB_native_eq_python"] = v[0] == rk["vp_etaB"]
        rs = row.get("k+p-1")
        ns = by.get((key, "k+(p-1)"))
        if rs is None or ns is None:
            continue
        mw = ns.get("m_from_weight_k") or {}
        if rs.get("status") != "computed" or "etaB_ring_vp" not in mw:
            rs["etaB_native"] = {"status": "open", "native_row": {k: ns.get(k) for k in ("weight", "pairing_perfect")},
                                 "reason": ("GL_2 side open" if rs.get("status") != "computed"
                                            else "no ring-theoretic eta^B for the weight-k m in the native file")}
            continue
        e = mw["etaB_ring_vp"]
        rs["vp_etaB"] = e
        rs["etaB_source"] = NATIVE_REL + " m_from_weight_k.etaB_ring (ring-theoretic; rank-1 block)"
        rs["etaB_status"] = "computed"
        rs.pop("etaB_reason", None)
        rs.pop("identity_scope", None)
        rs["etaB_eq_eta_new"] = e == rs["ord_eta_new"]
        rs["identity_with_etaB"] = rs["ord_eta"] == rs["ord_c"] + e
        rs["rank_new_definite"] = mw.get("rank")
        rs["ranks_agree"] = mw.get("rank") == rs["ranks"]["S_new_m"]


def t5_acceptance(rows: dict) -> dict:
    ks = [r["k"] for r in rows.values() if "k" in r]
    sh = [r["k+p-1"] for r in rows.values() if r.get("k+p-1", {}).get("status") == "computed"]
    acc = {
        "weight_k_identity_all": all(r.get("identity_with_etaB") for r in ks),
        "weight_k_agrees_S06_C6_all": all(r.get("agrees_with_S06_C6") for r in ks),
        "weight_k_agrees_S06_C4_all": all(r.get("agrees_with_S06_C4") for r in ks),
        "weight_k_native_etaB_eq_python_all": all(r.get("etaB_native_eq_python", True) for r in ks),
        "shifted_thm_E_identity_all_computed": all(r.get("thm_E_identity") for r in sh),
        "shifted_agrees_S06_C4_where_both": all(r.get("agrees_with_S06_C4") for r in sh if "agrees_with_S06_C4" in r),
        "shifted_identity_with_native_etaB_where_available": all(r["identity_with_etaB"] for r in sh
                                                                 if "identity_with_etaB" in r),
        "shifted_computed": sorted(k_ for k_, r in rows.items() if r.get("k+p-1", {}).get("status") == "computed"),
        "shifted_open": sorted(k_ for k_, r in rows.items() if r.get("k+p-1", {}).get("status") == "open"),
    }
    acc["pass"] = bool(acc["weight_k_identity_all"] and acc["weight_k_agrees_S06_C6_all"]
                       and acc["weight_k_agrees_S06_C4_all"] and acc["weight_k_native_etaB_eq_python_all"]
                       and acc["shifted_thm_E_identity_all_computed"] and acc["shifted_agrees_S06_C4_where_both"]
                       and acc["shifted_identity_with_native_etaB_where_available"])
    return acc


def t5(hacs=None, shifted: bool = True, threads: int = 8, triples=TRIPLES, log=sys.stderr) -> dict:
    root = runner._repo_root() or pathlib.Path(".")
    s06 = root / "code" / "results" / "s06"
    dB_all = json.loads((s06 / "T5_def.json").read_text())["data"]["triples"]
    gl2_or = json.loads((s06 / "T5_gl2.json").read_text())["data"]["triples"]
    c6 = json.loads((s06 / "T5.json").read_text())["data"]["triples"]
    rows = {}
    for (q, k, p) in triples:
        key = f"{q},{k},{p}"
        cache: dict = {}
        row = {}
        weights = [("k", k)] + ([("k+p-1", k + p - 1)] if shifted else [])
        for tag, kk in weights:
            t0 = time.perf_counter()
            try:
                g = gl2_cell(q, k, p, kk, hacs=hacs, data_cache=cache, threads=threads)
                g["record"] = hacs_record(q, kk - 2, p, hacs=hacs, threads=threads,
                                          timeout=CALL_TIMEOUT if tag == "k" else RECORD_TIMEOUT_SHIFTED)
            except (Refused, KeyError) as err:
                row[tag] = {"weight": kk, "status": "open", "reason": f"{type(err).__name__}: {err}"}
                print(f"{key} {tag}: open ({err})", file=log)
                continue
            dB = dB_all.get(key) if tag == "k" else None
            r = compare_row(g, dB, gl2_or.get(key, {}).get(tag))
            if tag == "k":
                c6k = c6[key]["k"]
                r["agrees_with_S06_C6"] = all(c6k.get(f) == r.get(f) for f in
                                              ("vp_etaB", "ord_eta", "ord_c", "ord_eta_new", "t_f_q",
                                               "etaB_eq_eta_new", "identity_with_etaB"))
            r["record_words"] = g["record"]
            r["gl2"] = g
            r["wall_s"] = round(time.perf_counter() - t0, 2)
            row[tag] = r
            print(f"{key} {tag} (kk={kk}): {r.get('status')} eta={r.get('ord_eta')} c={r.get('ord_c')} "
                  f"new={r.get('ord_eta_new')} etaB={r.get('vp_etaB')} C4={r.get('agrees_with_S06_C4')} "
                  f"C6={r.get('agrees_with_S06_C6')} ({r['wall_s']} s)", file=log, flush=True)
        rows[key] = row
    acc = t5_acceptance(rows)
    return {"triples": rows, "acceptance": acc}


# ---------------------------------------------------------------------------------------------- H3 and census

def degree_one_blocks(cell: dict) -> tuple[list[dict], list[dict]]:
    """(blocks of a native definite cell with residue field F_p, the other blocks)."""
    one, other = [], []
    for b in cell.get("blocks", []):
        (one if b.get("residual_eigenvalues") else other).append(b)
    return one, other


def compare_block(g: dict, blk: dict) -> dict:
    """One definite block m^B (residues a_l mod p, l in {2,3,5,7,11}) against the GL_2 maximal ideals with those
    residues: ranks, the multiset {v_p eta^B} = {ord eta_new}, Thm E per form, eta = c * eta^B where it is determined."""
    comps = [c for c in g.get("components", []) if c["ranks"]["S_new_m"] > 0]
    forms = [f for c in comps for f in c["forms"]]
    computed = g.get("status") == "computed" and all(f.get("status") == "computed" for f in forms)
    orbits = blk.get("orbits", [])
    resolved = all(o.get("resolved_Qp_orbit") and o.get("degree") == 1 for o in orbits)
    row = {"m_id": blk["m_id"], "residual_eigenvalues": blk["residual_eigenvalues"],
           "definite": {"rank": blk["rank"], "n_orbits": blk.get("n_orbits"), "old_congruent": blk.get("old_congruent"),
                        "vp_etaB": [o.get("vp_etaB") for o in orbits], "resolved_degree_one": resolved},
           "gl2": {"n_maximal_ideals": len(comps),
                   "maximal_ideals": [{"U_q_residue": c["U_q_residue"], "T_p_residue": c["T_p_residue"],
                                       "ranks": c["ranks"], "gorenstein_S_m": [f["gorenstein"]["S_m"]["gorenstein"]
                                                                              for f in c["forms"] if "gorenstein" in f],
                                       "forms": [{k: f.get(k) for k in ("orbit_degree", "a_q_sign", "ord",
                                                                         "thm_E_identity", "status")}
                                                 for f in c["forms"]]} for c in comps],
                   "sign_robust": g.get("sign_robust"), "t_f_q": g.get("t_f_q"),
                   "U_q_signs": g.get("U_q_signs")}}
    if not computed:
        row.update({"status": "open", "reason": g.get("reason") or "a GL_2 form at m is not computed"})
        return row
    if not resolved:
        row.update({"status": "open", "reason": "definite block not resolved into degree-1 Q_p-orbits (not determined)"})
        return row
    eB = sorted(o["vp_etaB"] for o in orbits)
    en = sorted(int(f["ord"]["eta_new"]) for f in forms)
    ec = sorted(int(f["ord"]["eta"]) - int(f["ord"]["c"]) for f in forms)
    row["checks"] = {
        "rank_definite_eq_rank_new_gl2": blk["rank"] == sum(c["ranks"]["S_new_m"] for c in comps),
        "etaB_multiset_eq_eta_new": eB == en,
        "thm_E_identity_all": all(f["thm_E_identity"] for f in forms),
        "identity_eta_eq_c_etaB_multiset": eB == ec,
    }
    if len(forms) == 1 and len(orbits) == 1:
        f = forms[0]
        row["checks"]["identity_with_etaB"] = int(f["ord"]["eta"]) == int(f["ord"]["c"]) + eB[0]
        tf = g.get("t_f_q")
        if isinstance(tf, int):
            row["checks"]["ord_c_eq_t_f_q"] = int(f["ord"]["c"]) == tf
            row["ord_c_minus_t_f_q"] = int(f["ord"]["c"]) - tf
    row["status"] = "computed"
    row["agree"] = all(row["checks"].values())
    return row


def _residual_minpoly(cs, red, p: int) -> str:
    """Min poly over F_p of p_l(theta), theta a root of the irreducible ``red`` in F_p[x] (PARI text, as m_id)."""
    from ..defect import hecke_alg as ha
    P = ha._P()
    num = sum(P(f"{c.numerator * pow(c.denominator, -1, p) % p}") * P("x") ** j for j, c in enumerate(cs))
    el = P.Mod(P.Mod(num, p), red)
    mp = P.minpoly(el)
    return str(P.lift(mp))


def gl2_block_unramified(q: int, k: int, p: int, blk: dict, cache: dict, hacs=None, threads: int = 8,
                         max_rank: int = 60) -> dict:
    """GL_2 side of a definite block whose residue field is F_{p^f}, f > 1 (H3): S_m = O_v (etale, eta = c = eta_new
    = (1)) when exactly one place v of all cusp systems carries the block's residual polynomials, v is unramified of
    degree f = rank of the block, and no old system meets m.  Anything else: open."""
    from ..defect import hecke_alg as ha
    P = ha._P()
    names, _ = generators(q, k, p)
    ells = sorted({int(l) for l in blk["m_id"] if int(l) != q})
    names = sorted(set(names) | set(ells))
    n = k - 2
    Lq = modz_union(q, n, names, cache, hacs, threads)
    L1 = modz_union(1, n, sorted(set(names) | {q}), cache, hacs, threads)
    if Lq["rank"] > max_rank:
        return {"status": "open", "reason": f"residue degree > 1 check limited to rank L_q <= {max_rank}"}
    rng = random.Random(1)
    co = {l: rng.randrange(1, 30) for l in [l for l in names if l != p][:4]}
    systems = [s_ for s_ in classify(Lq, L1, co, k) if s_["kind"] != "eis"]
    A = lin(Lq["T"], co)
    matches = []
    for s_ in systems:
        ev = krylov_polys(A, {l: Lq["T"][l] for l in ells}, s_["phi"], s_["mult"])
        phi = P.Pol([int(c) for c in reversed(s_["phi"].coeffs())])
        fa = P.factorpadic(phi, p, 30)
        for i in range(int(P.matsize(fa)[0])):
            f = fa[0][i]
            d = int(P.poldegree(f))
            red = P.Pol([int(P.lift(P.truncate(c))) % p for c in P.Vec(f)])
            fm = P.factormod(red, p)
            # Hensel: the reduction of a Q_p-irreducible factor is g^e, g irreducible; the place has residue degree
            # deg g and ramification e.  Its residues are those of theta mod g in either case.
            assert int(P.matsize(fm)[0]) == 1, "reduction of a Q_p-irreducible factor is a power of one irreducible"
            e_ram = int(fm[1][0])
            redl = P.lift(fm[0][0])
            if any(c.denominator % p == 0 for l in ells for c in ev[l]):
                return {"status": "open", "reason": "p in a Krylov denominator: residues not readable"}
            res = {str(l): _residual_minpoly(ev[l], redl, p) for l in ells}
            if all(str(P(res[str(l)])) == str(P(blk["m_id"][str(l)])) for l in ells):
                if e_ram > 1:                # a ramified place meets m: O_v is not etale, refuse (review HJ-8b m1)
                    return {"status": "open", "reason": f"a ramified place (e = {e_ram}) meets m",
                            "places_matching_m": matches + [{"kind": s_["kind"], "place_degree": d, "e": e_ram}]}
                matches.append({"kind": s_["kind"], "orbit_degree": s_["phi"].degree(), "place_degree": d, "e": 1})
    out = {"places_matching_m": matches}
    if len(matches) == 1 and matches[0]["kind"] == "new":
        d = matches[0]["place_degree"]
        out.update({"status": "computed", "ranks": {"S_m": d, "S_new_m": d, "S_old_m": 0},
                    "ord": {"eta": 0, "c": 0, "eta_new": 0},
                    "argument": "exactly one place v meets m, unramified of degree f = d, new, and no old system meets m: "
                                "S_m is a Z_p-order in O_v (rank d) with S_m / m = F_{p^d}, so S_m = O_v (Nakayama), "
                                "S'_m = S_m, S''_m = 0; eta = c = eta_new = (1)"})
    else:
        out.update({"status": "open", "reason": "not exactly one unramified new place at m (or an old system meets m)"})
    return out


def run_cells(cells: list[dict], hacs=None, threads: int = 8, log=sys.stderr, budget_s: float | None = None,
              checkpoint=None) -> dict:
    """GL_2 side for every degree-1 definite block of every native cell (k = weight, H3 and census)."""
    out = {}
    t0 = time.perf_counter()
    for cell in cells:
        q, k, p = cell["q"], cell["k"], cell["p"]
        key = f"{q},{k},{p}"
        if budget_s is not None and time.perf_counter() - t0 > budget_s:
            out[key] = {"status": "open", "reason": f"not run: the {budget_s:.0f} s budget of this run was used up"}
            continue
        one, other = degree_one_blocks(cell)
        cache: dict = {}
        rows = []
        t1 = time.perf_counter()
        for blk in one:
            res = {int(l): int(v) for l, v in blk["residual_eigenvalues"].items()}
            try:
                g = gl2_cell(q, k, p, k, hacs=hacs, residues=res, data_cache=cache, threads=threads)
            except Exception as err:     # every failure refuses this block only, with the reason (never silent)
                rows.append({"m_id": blk["m_id"], "status": "open", "reason": f"{type(err).__name__}: {str(err)[:300]}"})
                continue
            rows.append(compare_block(g, blk))
        others = []
        for b in other:
            row = {"m_id": b["m_id"], "definite": {"rank": b["rank"], "vp_etaB": [o.get("vp_etaB") for o in b["orbits"]],
                                                   "n_orbits": b.get("n_orbits")}}
            if b.get("n_orbits") == 1 and all(o.get("resolved_Qp_orbit") for o in b["orbits"]):
                try:
                    gl = gl2_block_unramified(q, k, p, b, cache, hacs, threads)
                except Exception as err:
                    gl = {"status": "open", "reason": f"{type(err).__name__}: {str(err)[:200]}"}
                row["gl2"] = gl
                row["status"] = gl["status"]
                if gl["status"] == "computed":
                    eB = b["orbits"][0].get("vp_etaB")
                    o = gl["ord"]
                    row["checks"] = {"rank_definite_eq_rank_new_gl2": gl["ranks"]["S_new_m"] == b["rank"],
                                     "etaB_eq_eta_new": eB == o["eta_new"],
                                     "identity_with_etaB": o["eta"] == o["c"] + eB,
                                     "thm_E_identity": o["eta"] == o["c"] + o["eta_new"]}
                    row["agree"] = all(row["checks"].values())
                else:
                    row["reason"] = gl["reason"]
            else:
                row.update({"status": "open", "reason": "definite block with several orbits and residue field "
                                                        "F_{p^f}, f > 1: outside both routes"})
            others.append(row)
        out[key] = {"q": q, "k": k, "p": p, "blocks": rows + others,
                    "wall_s": round(time.perf_counter() - t1, 2)}
        print(f"{key}: " + "; ".join(f"{r['status']}" + (f" agree={r.get('agree')}" if "agree" in r else "")
                                     + (f" ({r.get('reason','')[:60]})" if r["status"] == "open" else "")
                                     for r in out[key]["blocks"]) + f" ({out[key]['wall_s']} s)", file=log, flush=True)
        if checkpoint is not None:
            checkpoint(out)
    return out


CONVENTIONS = {
    "S": "full Hecke algebra Z[T_l (l <= Sturm + 1, l != q, l <= 97), U_q] of S_kk(Gamma_0(q)) (S06-C4's generator set "
         "minus primes > 97, the HACS descent cap); realised on (+)_s Z[gens]*1 in K_s over the orbits s that can meet m",
    "T_l": "HACS descent(N, kk-2, P).module_Z() free block F (T_l b_j = sum_i F_ij b_i), exact over Z, in HACS's basis (record words: basis rule iso_dixon/v3, saturation det_pm1)",
    "U_q": "q-new orbit: a_q = eps q^{(kk-2)/2}, eps from HACS level_n U_q charpolys (subset sum); level-one orbit g: "
           "U_q = y with y^2 - a_q(g) y + q^{kk-1} = 0, a_q(g) from HACS module_Z at level 1",
    "eta": "eta_f(q) = eta(S_m, lam_f) (S06-C4, defect.congruence.defect, base change to O)",
    "eta_new": "eta_f(1, q) = eta(S'_m, lam_f), S' = q-new quotient",
    "c": "c_q(f) = lam_f(ker(S -> S''))",
    "eta_B": "weight k: v_p det of the Gram matrix G_w (w_x weights) on the q-new orbit lattice at m (S06-C5 Python and "
             "the native BrandtSym file, cross-checked; Hsieh Rem 7.3); weight k+(p-1): the ring-theoretic congruence ideal "
             "of the definite Hecke algebra at the weight-k m (native file, m_from_weight_k.etaB_ring; the Gram is not "
             "eta^B there since p <= n)",
    "t_f_q": "v_p(a_q(g)^2 - q^{k-2}(q+1)^2), a_q(g) from HACS (level-one T_q)",
    "status": "computed / bound / open; record words quoted verbatim",
}


def _load_native(root: pathlib.Path) -> dict | None:
    f = root / NATIVE_REL
    return json.loads(f.read_text())["data"] if f.is_file() and "data" in json.loads(f.read_text()) else (
        json.loads(f.read_text()) if f.is_file() else None)


def h3_cells(native: dict) -> list[dict]:
    return [c for c in native["cells"] if str(c.get("weight_role", "")).startswith("H3")]


def census_cells(native: dict, classes=("genuine_congruence", "old_congruent")) -> list[dict]:
    """The native census cells restricted to the blocks of the given classes (each block tagged with its class)."""
    cen = native["census"]
    by = {(c["q"], c["k"], c["p"]): c for c in cen["cells"]}
    out: dict = {}
    for cls in classes:
        for e in cen["classification"][cls]:
            key = (e["q"], e["k"], e["p"])
            cell = by[key]
            blk = next(b for b in cell["blocks"] if b["m_id"] == e["m_id"])
            blk = dict(blk, census_class=cls)
            tgt = out.setdefault(key, dict(cell, blocks=[]))
            tgt["blocks"].append(blk)
    cost = lambda c: (c["q"] + 1) * (c["k"] - 1)          # ~ index(q) (n + 1): the descent cost driver
    return sorted(out.values(), key=lambda c: (0 if any(b["census_class"] == "genuine_congruence" for b in c["blocks"])
                                               else 1, cost(c), c["p"]))


def _summary(rows: dict) -> dict:
    blocks = [b for r in rows.values() for b in r.get("blocks", [])]
    comp = [b for b in blocks if b.get("status") == "computed"]
    return {"cells": len(rows), "blocks": len(blocks), "blocks_computed": len(comp),
            "blocks_open": len(blocks) - len(comp), "blocks_agree": sum(1 for b in comp if b.get("agree")),
            "blocks_disagree": [f"{k}:{b['m_id']}" for k, r in rows.items() for b in r.get("blocks", [])
                                if b.get("status") == "computed" and not b.get("agree")],
            "cells_not_run": sorted(k for k, r in rows.items() if "blocks" not in r)}


def main(argv=None) -> int:  # pragma: no cover - CLI
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("what", choices=["t5", "t5-splice", "h3", "census"],
                    help="t5: run the T5 triples; t5-splice: rerun --triples and replace those rows of --base; "
                         "h3 / census: the GL_2 side on the native definite cells (hj8_def_native.json)")
    ap.add_argument("--budget-s", type=float, default=3300, help="census: stop starting new cells after this")
    ap.add_argument("--checkpoint", default=None, help="h3 / census: checkpoint file (outside the repository)")
    ap.add_argument("--from-checkpoint", default=None,
                    help="census: take the rows of a checkpoint (no HACS run); with --rows-commit / --rows-log")
    ap.add_argument("--rows-commit", default=None, help="the code commit the checkpoint rows were computed at")
    ap.add_argument("--rows-log", default=None, help="the log of the run that wrote the checkpoint")
    ap.add_argument("--hacs", default=HACS_DEFAULT)
    ap.add_argument("--out", default=None)
    ap.add_argument("--base", default=None, help="t5-splice: the existing T5_hacs.json")
    ap.add_argument("--no-shifted", action="store_true")
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--triples", default=None, help="q,k,p;q,k,p;...")
    a = ap.parse_args(argv)
    from ..pari import get_pari
    get_pari().allocatemem(4 << 30)
    triples = TRIPLES if not a.triples else tuple(tuple(int(x) for x in t.split(",")) for t in a.triples.split(";"))
    root = runner._repo_root() or pathlib.Path(".")
    if a.what in ("h3", "census"):
        return _main_cells(a, root)
    path = pathlib.Path(a.out) if a.out else root / "code/results/laneC/T5_hacs.json"
    native = _load_native(root)
    t0 = time.perf_counter()
    data = t5(a.hacs, shifted=not a.no_shifted, threads=a.threads, triples=triples)
    runtime = round(time.perf_counter() - t0, 2)
    params = {"triples": [list(t) for t in triples], "weights": ["k"] + ([] if a.no_shifted else ["k+p-1"]),
              "threads": a.threads, "seed": 1, "local_precision_E": LOCAL_E,
              "hacs_caps": {"max_prime": HACS_MAX_PRIME, "batch": HACS_MAX_BATCH, "sum": HACS_MAX_SUM, "n": HACS_MAX_N}}
    prov = runner.provenance("code/python/langlandscape/hacs_bridge/jl_defect.py", params, runtime, a.hacs, hz=True,
                             notes="HJ-8: T5 on the GL_2 side through HACS; eta^B: S06-C5 (Python) at k, native "
                                   "BrandtSym (worker C) at k and k+(p-1)")
    if a.what == "t5-splice":
        base = json.loads(pathlib.Path(a.base).read_text())
        rows = base["data"]["triples"]
        for key, row in data["triples"].items():
            rows[key] = row
        data = {"triples": rows}
        prov_out = dict(base["provenance"])
        prov_out["spliced_rows"] = {"rows": sorted(data["triples"].keys() & {f"{q},{k},{p}" for q, k, p in triples}),
                                    "provenance": prov,
                                    "reason": "rerun after the ramified-place fix of the local route (13bd624b+)"}
        prov = prov_out
    if native is not None:
        annotate_native(data["triples"], native)
        prov["native_definite_side"] = {"file": NATIVE_REL, "commit": (native.get("provenance") or {}).get("commit")
                                        if isinstance(native, dict) else None}
    data["acceptance"] = t5_acceptance(data["triples"])
    data["conventions"] = CONVENTIONS
    out = {"provenance": prov, "data": data}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=1, default=str) + "\n")
    print(json.dumps(data["acceptance"], indent=1, default=str))
    return 0 if data["acceptance"]["pass"] else 1


def _main_cells(a, root: pathlib.Path) -> int:  # pragma: no cover - CLI
    native = _load_native(root)
    nat_prov = native.get("provenance", {})
    path = pathlib.Path(a.out) if a.out else root / ("code/results/laneC/H3_hacs.json" if a.what == "h3"
                                                      else "code/results/laneC/defect_census.json")
    if a.what == "h3":
        cells = h3_cells(native)
        budget = None
    else:
        cells = census_cells(native)
        budget = a.budget_s
    if a.triples:
        want = {tuple(int(x) for x in t.split(",")) for t in a.triples.split(";")}
        cells = [c for c in cells if (c["q"], c["k"], c["p"]) in want]
    t0 = time.perf_counter()
    params = {"what": a.what, "cells": [[c["q"], c["k"], c["p"]] for c in cells], "threads": a.threads,
              "local_precision_E": LOCAL_E, "budget_s": budget,
              "definite_side": {"file": NATIVE_REL, "commit": nat_prov.get("commit")}}

    def write(rows, final=False):
        data = {"cells": rows, "summary": _summary(rows), "conventions": CONVENTIONS,
                "status_words": "computed / open (with reason); 'not determined' = the native definite block is "
                                "not resolved into Q_p-orbits"}
        if a.what == "h3":
            data["H3"] = {"triples_(q,p,k)": [list(t) for t in H3_CASES],
                          "prediction": "ord c_q(f) - t_f(q) = 0 (prop:s06-levM, M = 1); here S_k(1) = 0, so c_q(f) = (1) "
                                        "and t_f(q) = 0: the test is vacuous (S06-xcheck doubt 1, code/cas/s06-xcheck)",
                          "S06_C7_xcheck": "code/results/s06-xcheck/H3.json: ord c = t^an = 0 for every (f, P)"}
        else:
            cen = native["census"]
            data["census"] = {"bounds": cen["bounds"], "native_params": cen["params"],
                              "classification_counts": cen["classification_counts"],
                              "trivial_cells": {"count": cen["params"]["cells_trivial_by_squarefree_chi_mod_p"],
                                                "status": "computed (definite side)",
                                                "reason": cen["rule"]},
                              "not_determined": [dict(e, status="not determined",
                                                      reason="native definite block not resolved into Q_p-orbits "
                                                             "(resolved_Qp_orbit = false); GL_2 side not run")
                                                 for e in cen["classification"]["unresolved_not_determined"]],
                              "gl2_scope": "the blocks classified genuine_congruence and old_congruent (master 08:20Z)"}
        rt = round(time.perf_counter() - t0, 2)
        prov = runner.provenance("code/python/langlandscape/hacs_bridge/jl_defect.py", params, rt, a.hacs, hz=True,
                                 notes=f"HJ-8b {a.what}: GL_2 side through HACS on the native definite cells"
                                       + ("" if final else " (CHECKPOINT, run not finished)"))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"provenance": prov, "data": data}, indent=1, default=str) + "\n")
        return data

    ckpt_path = pathlib.Path(a.checkpoint or f"/home/janosch/data/hacs-run/laneC/hj8/{a.what}.partial.json")

    def checkpoint(rows):
        ckpt_path.write_text(json.dumps(rows, default=str))

    if a.from_checkpoint:                   # finalise a capped run: its rows, no HACS call
        rows = json.loads(pathlib.Path(a.from_checkpoint).read_text())
        params["rows_from_checkpoint"] = {"file": runner.public_path(a.from_checkpoint), "rows": len(rows),
                                          "computed_at_commit": a.rows_commit,
                                          "log": runner.public_path(a.rows_log) if a.rows_log else None,
                                          "note": "the run hit its hard wall cap before writing; every finished cell "
                                                  "is in the checkpoint, written after each cell"}
    else:
        rows = run_cells(cells, a.hacs, threads=a.threads, budget_s=budget, checkpoint=checkpoint)
    if a.base:                              # splice: rerun rows replace those of the base file, both provenances kept
        base = json.loads(pathlib.Path(a.base).read_text())
        merged = dict(base["data"]["cells"])
        merged.update(rows)
        params["spliced_rows"] = sorted(rows)
        params["base_provenance"] = base["provenance"]
        rows = merged
    if a.what == "census":                  # every census cell is accounted for: not run -> open with the reason
        for c in census_cells(native):
            key = f"{c['q']},{c['k']},{c['p']}"
            if key not in rows:
                rows[key] = {"q": c["q"], "k": c["k"], "p": c["p"], "status": "open",
                             "reason": "not run: outside the time budget of the runs so far (60-min cap per run)",
                             "definite_blocks": [{"m_id": b["m_id"], "census_class": b["census_class"]}
                                                 for b in c["blocks"]]}
    data = write(rows, final=True)
    print(json.dumps(data["summary"], indent=1, default=str))
    return 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
