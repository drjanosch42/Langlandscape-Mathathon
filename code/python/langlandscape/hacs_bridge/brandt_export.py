#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-B0: export Brandt lattices as ``langlandscape_brandt/v2`` ``free_block_z`` records (JL extension; upstream untouched).

Format: ``plan/hacs/freeblockz-export-format.md`` (v2 = v1 + the required canonical class order, §1b).  The records carry the integer T_p matrices in the layout of
HACS's ``integral_descent::modexport::FreeBlockZ`` (``src/hacs/Integral/Descent/DescentModuleExportZ.h:140``), in the
``LatticeModule`` column convention T_p b_j = sum_i F_ij b_i, and ``F_fnv`` = HACS's ``MatrixFnv`` (FNV-1a-64 of the text
"F00,F01,..;F10,..", ``IsoTreeCarrierZ.cpp:269``).  Lane B's ``Lattice2HeckeZ`` reads them into ``LatticeFromFreeZ``.

* Class order (v2, both k): ascending by (|Gamma_c|, theta_c), theta_c = (r_c(1), ..., r_c(20)),
  r_c(m) = #{x in O_r(I_c) : nrd x = m} (x and -x both counted); ties -> ``order_ties`` (``canonical_order``).
  ``brandt.module(D)``'s own BFS order depends on process history (its base maximal order varies), so it is not used.
* k = 2 (``brandt.py``): M = Z-valued functions on the class set, b_j = 1_{c_j}; F_p = B_p (no transpose).
* k > 2 (``symn.py``): the rational model on (+)_c V_Q^{Gamma_c} (V_Q = V^phi), class blocks in the canonical order, then
  the Hecke-stable hull Lambda = Z[T_p : p in ops] . Z^d (the smallest Hecke-stable lattice containing Z^d, Z^d = the
  symn.py Q-coordinates), in HNF basis.  A lattice, not a canonical one: ``canonical: false`` (compare by char_Z).
* odd k: rank 0 (V^{Gamma_c} = 0).

Every value is *computed*; nothing here is ``certified``.

Usage: brandt_export.py [--cells k2|symn|all] [--out-dir code/results/s06/brandt_free_block_z]
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
import time
from fractions import Fraction
from math import lcm

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[3]  # hacs_bridge -> langlandscape -> python -> code -> repo
sys.path.insert(0, str(REPO / "code" / "python"))

import flint  # noqa: E402

from langlandscape import brandt, results, symn  # noqa: E402
from langlandscape.pari import get_pari  # noqa: E402

SCHEMA = "langlandscape_brandt/v2"
CONVENTION = "column: T_p b_j = sum_i F[i][j] b_i; F = B_p (B[c][c'] = #neighbours of c in c'); row sums l+1"
CONVENTION_SYMN = ("column: T_p b_j = sum_i F[i][j] b_i; b_j = the j-th column of basis_in_Q_coords (a basis of the "
                   "Hecke-stable hull Lambda); no row-sum identity (no Eisenstein system at k > 2)")
THETA_L = 20          # the fixed length of the class theta series in the sort key (v2 writer rule; independent of ops)
ORDER_KEY = ("classes sorted ascending by (|Gamma_c|, (r_c(1),...,r_c(20))), r_c(m) = #{x in O_r(I_c) : nrd x = m} "
             "(x, -x both counted); ties listed in order_ties, order within a tie unspecified")
RULE_K2 = "brandt_k2_canonical/v2: b_j = 1_{c_j}, c_j the j-th left-ideal class; " + ORDER_KEY
RULE_SYMN = ("brandt_symn_int_canonical/v2: Lambda = Z[T_p : p in ops] . Z^d (the Hecke-stable hull: the smallest "
             "Hecke-stable lattice containing Z^d), Z^d = the Q-coordinates of symn.SymBrandt's rational model "
             "(+)_c V_Q^{Gamma_c} (V_Q = V^phi, Q-basis and Gamma_c-invariant bases as in symn.py) with the class blocks "
             "in the k = 2 canonical order (" + ORDER_KEY + "); basis = the columns of the lower-triangular HNF of Lambda; "
             "depends on the ops list and on symn.py's class representatives (canonical: false)")
FNV_OFFSET = 0xCBF29CE484222325
FNV_PRIME = 0x100000001B3
K2_DS = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)   # the primes D <= 43 (HJ-A2's k = 2 grid is a subset)
SYMN_DS, SYMN_KS = (2, 3, 5, 7, 11, 13), tuple(range(2, 13))
OPS_BOUND = 50
OPS_BOUND_SYMN = 20   # k > 2: symn.py's neighbour tables are O(l^4) in Python; primes < 20 here, more on request (ops=...)


# ---------------------------------------------------------------- FNV (HACS MatrixFnv, byte-exact)
def fnv1a64(s: str) -> int:
    h = FNV_OFFSET
    for c in s.encode("ascii"):
        h = ((h ^ c) * FNV_PRIME) & 0xFFFFFFFFFFFFFFFF
    return h


def matrix_text(F) -> str:
    """HACS's canonical text: rows joined by ';', entries by ',', entries as nf::BigInt::to_string (= Python str(int))."""
    return ";".join(",".join(str(int(x)) for x in row) for row in F)


def f_fnv(F) -> str:
    return "0x%016x" % fnv1a64(matrix_text(F))


# ---------------------------------------------------------------- exact linear algebra helpers
def primes_below(b: int, avoid: int) -> list[int]:
    return [p for p in range(2, b) if all(p % q for q in range(2, int(p ** 0.5) + 1)) and avoid % p]


def matmul(A, B):
    n, m, k = len(A), len(B[0]) if B else 0, len(B)
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)] for i in range(n)]


def charpoly_low_high(F) -> list[int]:
    r = len(F)
    if r == 0:
        return [1]
    cp = flint.fmpz_mat(r, r, [int(x) for row in F for x in row]).charpoly()
    return [int(c) for c in cp.coeffs()]


def _qrank(vecs) -> int:
    if not vecs:
        return 0
    return flint.fmpq_mat(len(vecs), len(vecs[0]), [flint.fmpq(Fraction(x).numerator, Fraction(x).denominator)
                                                       for v in vecs for x in v]).rank()


def _flat(A):
    return [x for row in A for x in row]


def algebra_dim(mats) -> int:
    """dim_Q of the Q-algebra generated by the commuting matrices ``mats`` (span of 1 closed under the generators)."""
    r = len(mats[0]) if mats else 0
    if r == 0:
        return 0
    I = [[Fraction(int(i == j)) for j in range(r)] for i in range(r)]
    basis, frontier = [I], [I]
    while frontier:
        new = []
        for A in frontier:
            for T in mats:
                B = matmul(T, A)
                if _qrank([_flat(X) for X in basis] + [_flat(B)]) > len(basis):
                    basis.append(B)
                    new.append(B)
        frontier = new
    return len(basis)


def _z_hnf_rows(rows):
    """Z-basis (as Fraction rows) of the Z-span of rational row vectors ``rows`` (full HNF, zero rows dropped)."""
    den = 1
    for v in rows:
        for x in v:
            den = lcm(den, Fraction(x).denominator)
    m = flint.fmpz_mat(len(rows), len(rows[0]), [int(Fraction(x) * den) for v in rows for x in v]).hnf()
    out = []
    for i in range(m.nrows()):
        v = [Fraction(int(m[i, j]), den) for j in range(m.ncols())]
        if any(v):
            out.append(v)
    return out


def hecke_stable_hull(mats):
    """Columns of P: a Z-basis of Lambda = Z[mats] . Z^d (Z[mats] the Z-algebra, a finite Z-module since char_Z holds)."""
    d = len(mats[0])
    I = [[Fraction(int(i == j)) for j in range(d)] for i in range(d)]
    alg = _z_hnf_rows([_flat(I)])
    while True:
        cand = [v for v in alg]
        for v in alg:
            A = [v[i * d:(i + 1) * d] for i in range(d)]
            for T in mats:
                cand.append(_flat(matmul(T, A)))
        nxt = _z_hnf_rows(cand)
        if nxt == alg:
            break
        alg = nxt
        assert max(Fraction(x).denominator for v in alg for x in v) < 10 ** 60, "Z[T] not finite (non-integral T?)"
    cols = []
    for v in alg:
        A = [v[i * d:(i + 1) * d] for i in range(d)]
        cols += [[A[i][j] for i in range(d)] for j in range(d)]      # the columns A e_j
    basis = _z_hnf_rows(cols)          # rows = basis vectors of Lambda (HNF)
    assert len(basis) == d
    P = [[basis[j][i] for j in range(d)] for i in range(d)]           # columns = basis
    return P


def _qinv(P):
    d = len(P)
    m = flint.fmpq_mat(d, d, [flint.fmpq(x.numerator, x.denominator) for row in P for x in row]).inv()
    return [[Fraction(int(m[i, j].p), int(m[i, j].q)) for j in range(d)] for i in range(d)]


# ---------------------------------------------------------------- record
def make_record(D, M, k, ops, mats, *, gammas, basis_rule, proof, origin, class_keys=None, e_eis=None, extra=None,
                order_ties=None):
    r = len(mats[0]) if mats else 0
    F = [[[str(int(x)) for x in row] for row in A] for A in mats]
    rec = {
        "schema": SCHEMA, "status": "ok" if r else "rank0", "D": D, "M": M, "k": k, "n": k - 2, "N": D * M, "rank": r,
        "ops": list(ops), "F": F if r else [[] for _ in ops],
        "F_fnv": [f_fnv(A) for A in mats] if r else [f_fnv([]) for _ in ops],
        "proof": [proof if r else "rank0" for _ in ops],
        "basis_rule": basis_rule, "convention": CONVENTION if k == 2 else CONVENTION_SYMN,
        "lattice": "functions", "tag": "computed",
        "phi_fnv": "-", "saturation": "exact_basis" if r else "rank0", "q0_key": "-", "bound_basis": "-",
        "bits_F": [max((abs(int(x)).bit_length() for row in A for x in row), default=0) for A in mats] if r else [0] * len(ops),
        "gammas": list(gammas), "charpoly_Z": [[str(c) for c in charpoly_low_high(A)] for A in mats] if r else [["1"]] * len(ops),
        "origin": origin,
    }
    if order_ties is not None:
        rec["order_ties"] = order_ties
    if k > 2:
        rec["canonical"] = False
    if class_keys is not None:
        rec["class_keys"] = class_keys
        rec["basis_fnv"] = "0x%016x" % fnv1a64(";".join(class_keys))
    if r:
        rec["d_algebra"] = algebra_dim([[[Fraction(int(x)) for x in row] for row in A] for A in mats])
        rec["e_eis"] = (1 if k == 2 else 0) if e_eis is None else e_eis
    if extra:
        rec.update(extra)
    return rec


def no_integral_basis(D, M, k, ops, reason, *, gammas, charpolys=None):
    rec = {"schema": SCHEMA, "status": "no_integral_basis", "reason": reason, "D": D, "M": M, "k": k, "n": k - 2,
           "N": D * M, "rank": None, "ops": list(ops), "F": [], "F_fnv": [], "proof": [], "basis_rule": "-",
           "convention": CONVENTION if k == 2 else CONVENTION_SYMN, "lattice": "functions", "tag": "computed", "gammas": list(gammas), "origin": "jl:symn.py"}
    if charpolys is not None:
        rec["charpoly_Z"] = charpolys
    return rec


CROSS_CHECK_BOUND = 14   # primes below this: the theta-series B_p is asserted equal to brandt.py's neighbour count m.T(p)


def brandt_theta(m: "brandt.BrandtModule", ops) -> list:
    """B_p[i][j] = #{x in conj(I_i) I_j : nrd x = p N_i N_j} / |Gamma_j| (theta series of the normalised norm form).

    The same matrices as ``brandt.py``'s ``T(p)`` (neighbour counts; O(p^4) enumeration), here by PARI ``qfrep`` on the
    integral Gram ``gram(conj(I_i) I_j) / (N_i N_j)`` (x^T G x = 2 nrd(x)/(N_i N_j); flag 1 counts even norms, +-x once).
    Asserted equal to ``m.T(p)`` for every p < CROSS_CHECK_BOUND in ``ops``.
    """
    pari = get_pari()
    B, reps, g = m.B, m.reps, m.gammas
    top = max(ops)
    cnt = [[None] * m.h for _ in range(m.h)]
    for i, (I, Ni) in enumerate(reps):
        for j, (J, Nj) in enumerate(reps):
            G = B.gram(B.lmul(B.lconj(I), J)) / (Ni * Nj)
            cnt[i][j] = [2 * int(x) for x in pari.qfrep(G, top, 1)]
    mats = []
    for p in ops:
        A = []
        for i in range(m.h):
            row = []
            for j in range(m.h):
                c = cnt[i][j][p - 1]
                assert c % g[j] == 0, "theta count not divisible by |Gamma_j|"
                row.append(c // g[j])
            A.append(row)
        if p < CROSS_CHECK_BOUND:
            assert A == m.T(p), (m.D, p, A, m.T(p))
        mats.append(A)
    return mats


def class_theta(m: "brandt.BrandtModule", c: int, L: int = THETA_L) -> tuple:
    """theta_c = (r(1), ..., r(L)), r(m) = #{x in O_r(I_c) : nrd x = m}, x and -x both counted (so r(1) = |Gamma_c|).

    O_r(I_c) = conj(I_c) I_c / N_c^2, so the Gram gram(conj(I) I) / N^2 has x^T G x = 2 nrd(x); PARI ``qfrep(G, L, 1)``
    counts x^T G x = 2, 4, ..., 2L with +-x once, hence the factor 2.
    """
    B = m.B
    I, N = m.reps[c]
    G = B.gram(B.lmul(B.lconj(I), I)) / (N * N)
    return tuple(2 * int(x) for x in get_pari().qfrep(G, L, 1))


def canonical_order(m: "brandt.BrandtModule"):
    """(perm, order_ties): perm[a] = the brandt.module index of the class at canonical position a (v2 writer rule).

    Sort ascending by (|Gamma_c|, theta_c) (``class_theta``); ``order_ties`` = all pairs [a, b], a < b, of canonical
    positions with equal keys (a tied group is contiguous; the order inside it is whatever the stable sort leaves).
    """
    keys = [(m.gammas[c], class_theta(m, c)) for c in range(m.h)]
    assert all(t[0] == g for g, t in keys), "r_c(1) != |Gamma_c|"
    perm = sorted(range(m.h), key=lambda c: keys[c])
    ties = [[a, b] for a in range(m.h) for b in range(a + 1, m.h) if keys[perm[a]] == keys[perm[b]]]
    return perm, ties


def permute(A, perm):
    return [[A[perm[a]][perm[b]] for b in range(len(perm))] for a in range(len(perm))]


def k2_record(D: int, M: int = 1, ops=None):
    m = brandt.module(D, M)
    ops = ops or primes_below(OPS_BOUND, D * M)
    perm, ties = canonical_order(m)
    mats = [permute(A, perm) for A in brandt_theta(m, ops)]
    keys = [str(m.reps[c][0].key) for c in perm]
    return make_record(D, M, 2, ops, mats, gammas=[m.gammas[c] for c in perm], basis_rule=RULE_K2, proof="exact_count",
                       origin="jl:brandt.py(theta,cross-checked)", class_keys=keys, order_ties=ties)


def _rational_model(sb: "symn.SymBrandt", ells):
    """The matrices of T_ell on the rational model (+)_c V_Q^{Gamma_c} (Q-coordinates of symn.py), column convention."""
    cap = {}

    def grab(ell, Cm, Cinv):
        cap["Cm"], cap["Cinv"] = Cm, Cinv
        return [1]

    sb._rational_model_charpoly = grab          # instance attribute: run symn's own asserted Q-structure once, keep Cm/Cinv
    sb.q_structure_report([ells[0]])
    del sb._rational_model_charpoly
    Cm, Cinv = cap["Cm"], cap["Cinv"]
    symn.SymBrandt._rational_model_charpoly(sb, ells[0], Cm, Cinv)   # fills sb._Winv (asserted dims)
    S, dim = sb.S, sb.n + 1
    Winv = sb._Winv
    emb = lambda q: symn.mat_vec(Cm, [symn.QS(x, 0, S.a) for x in q], S.zero)   # noqa: E731
    out = []
    for ell in ells:
        cols = []
        for c, W in enumerate(Winv):
            for w in W:
                Phi = [[S.zero] * dim for _ in range(sb.h)]
                Phi[c] = emb(w)
                TPhi = sb.apply_formula(ell, Phi)
                col = []
                for cc in range(sb.h):
                    q = symn.mat_vec(Cinv, TPhi[cc], S.zero)
                    assert all(x.is_rational() for x in q), "T_ell leaves V_Q"
                    col += symn.solve_in_span(Winv[cc], [x.r for x in q], Fraction(0)) if Winv[cc] else []
                cols.append(col)
        out.append([[Fraction(cols[j][i]) for j in range(sb.dim)] for i in range(sb.dim)])
    return out


def symn_record(D: int, k: int, ops=None):
    if k == 2:
        return k2_record(D, 1, ops)
    ops = ops or primes_below(OPS_BOUND_SYMN, D)
    sb = symn.SymBrandt(D, k)
    perm, ties = canonical_order(sb.S.mod)
    gammas = [sb.gammas[c] for c in perm]
    if sb.dim == 0:
        return make_record(D, 1, k, ops, [[] for _ in ops], gammas=gammas, basis_rule=RULE_SYMN, proof="rank0",
                           origin="jl:symn.py", order_ties=ties)
    if k % 2:
        raise AssertionError("odd k with nonzero invariants")
    Q = _rational_model(sb, ops)
    # the class blocks of the Q-coordinates in canonical order: new coordinate t <- old coordinate idx[t]
    off, o = [], 0
    for W in sb._Winv:
        off.append(o)
        o += len(W)
    idx = [off[c] + i for c in perm for i in range(len(sb._Winv[c]))]
    Q = [permute(A, idx) for A in Q]
    P = hecke_stable_hull(Q)
    Pi = _qinv(P)
    mats = []
    for A in Q:
        F = matmul(Pi, matmul(A, P))
        assert all(x.denominator == 1 for row in F for x in row), "F not integral on the Hecke-stable hull"
        mats.append([[int(x) for x in row] for row in F])
    return make_record(D, 1, k, ops, mats, gammas=gammas, basis_rule=RULE_SYMN, proof="exact_rational_model",
                       origin="jl:symn.py+integral_basis", order_ties=ties,
                       extra={"basis_in_Q_coords": [[str(x) for x in row] for row in P]})


# ---------------------------------------------------------------- checks (the HJ-B0 acceptance, per record)
def check_record(rec: dict) -> dict:
    out = {"fnv": True, "square": True, "commute": True, "row_sums": None, "symmetry": None}
    if rec["status"] != "ok":
        return out
    r, ops = rec["rank"], rec["ops"]
    mats = [[[int(x) for x in row] for row in F] for F in rec["F"]]
    out["square"] = all(len(A) == r and all(len(row) == r for row in A) for A in mats)
    out["fnv"] = all(f_fnv(A) == h for A, h in zip(mats, rec["F_fnv"]))
    out["commute"] = all(matmul(A, B) == matmul(B, A) for i, A in enumerate(mats) for B in mats[i + 1:])
    out["charpoly"] = all([str(c) for c in charpoly_low_high(A)] == cp for A, cp in zip(mats, rec["charpoly_Z"]))
    if rec["k"] == 2:
        out["row_sums"] = all(sum(row) == p + 1 for A, p in zip(mats, ops) for row in A)
        g = rec["gammas"]
        out["symmetry"] = all(g[j] * A[i][j] == g[i] * A[j][i] for A in mats for i in range(r) for j in range(r))
    return out


def symn_charpoly_check(rec: dict, grid: dict):
    """char_Z = symn.json (symn's ells only; symn.json lists charpolys low -> high)."""
    cell = grid.get(f"{rec['D']},{rec['k']}")
    if cell is None:
        return None
    ok = True
    for ell, e in cell["ell"].items():
        p = int(ell)
        want = [int(c) for c in e["charpoly_brandt"]]
        if rec["status"] == "rank0":
            ok &= want == [1]
        elif rec["status"] == "ok":
            ok &= [int(c) for c in rec["charpoly_Z"][rec["ops"].index(p)]] == want
        else:
            return None
    return ok


# ---------------------------------------------------------------- driver
def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--cells", choices=("k2", "symn", "all"), default="all")
    ap.add_argument("--out-dir", default="s06/brandt_free_block_z", help="relative to code/results/")
    a = ap.parse_args(argv)
    grid = results.read("s01/symn.json")["data"]["grid"]
    cells = []
    if a.cells in ("k2", "all"):
        cells += [(D, 2) for D in K2_DS]
    if a.cells in ("symn", "all"):
        cells += [(D, k) for D in SYMN_DS for k in SYMN_KS if not (k == 2 and D in K2_DS)]
    index_path = REPO / "code" / "results" / a.out_dir / "index.json"
    index = {}
    if index_path.exists():
        index = {(c["D"], c["M"], c["k"]): c for c in json.loads(index_path.read_text())["data"]["cells"]}
    writer = f"python:brandt_export@{results.git_commit()}"
    for D, k in cells:
        t0 = time.perf_counter()
        rec = symn_record(D, k)
        chk = check_record(rec)
        chk["symn_charpoly"] = symn_charpoly_check(rec, grid)
        dt = time.perf_counter() - t0
        assert all(v is not False for v in chk.values()), (D, k, chk)
        name = f"D{D}_M1_k{k}.json"
        results.write(f"{a.out_dir}/{name}", {"schema": SCHEMA, "writer": writer, "free_block_z": rec, "checks": chk},
                      script="code/python/langlandscape/hacs_bridge/brandt_export.py", params={"D": D, "M": 1, "k": k, "ops": rec["ops"]},
                      runtime_s=dt, notes="HJ-B0; format plan/hacs/freeblockz-export-format.md (v2); computed")
        index[(D, 1, k)] = {"D": D, "M": 1, "k": k, "file": name, "status": rec["status"], "rank": rec["rank"], "checks": chk}
        print(f"D={D} k={k} status={rec['status']} rank={rec['rank']} checks={chk} {dt:.1f}s", flush=True)
    cl = [index[key] for key in sorted(index)]
    results.write(f"{a.out_dir}/index.json", {"schema": SCHEMA, "writer": writer, "cells": cl},
                  script="code/python/langlandscape/hacs_bridge/brandt_export.py", params={"cells": a.cells}, runtime_s=0.0,
                  notes="index of the free_block_z cells (HJ-B0)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
