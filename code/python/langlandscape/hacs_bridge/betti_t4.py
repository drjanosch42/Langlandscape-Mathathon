# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-A3 = S06-H1 (T4): the Betti side coker(Psi*Psi)_m as a Z_17-module, q = 3, p = l = 17, k in {12, 28, 44, 60, 124}.

One gating Betti route (B), one optional supplementary Betti route (A), and one Hecke side, kept apart on purpose:

* **Betti-amalgam (route B, gating)**: the 2x2 block matrix alpha*alpha on L^2, L = H^1(SL_2(Z), Sym^n Z_(17))/tors (the
  lattice the model's exact rational quotient sees), with all four blocks computed as the actual composites of the
  Mayer--Vietoris maps (omega o dg_1, omega o dg_q, omega' o dg_1, omega' o dg_q) by the exchange model
  ``task1_v6/scripts/amalgam.py`` (HACS answer to the JL exchange, CC-BY-4.0; imported from its path, not copied) and a
  transfer block adapted, with attribution, from ``task1_v6/scripts/cell.py``. Localised at m by e_m (= e_{T_3}, checked),
  Smith form over Z_17. No HACS data enters this route.
* **Betti-HACS (route A, OFF by default; supplementary, non-gating, needs Q4)**: the integral T_2, T_3, T_17 on
  H^1/tors in HACS's certified basis (``descent(1, k-2, [2, 3, 17]).module_Z()``), put into
  alpha*alpha = [[q+1, -T_q], [-q^{2-k} T_q, q+1]]. ``module_Z()`` is only called with ``--allow-module-z`` /
  ``allow_module_z=True`` (Q4: default no, pending Fabian).
* **Hecke side**: length_{Z_17} T(1)_m/(delta) from HACS's exact char_Z(T_3 | H^1/tors) (cusp part, 17-adic branch through
  tau(3)), delta made integral: 3^{k-2} delta = 16 * 3^{k-2} - T_3^2.

Conventions: task1_v6/results.md section 0 verbatim (``CONVENTIONS`` below); the s03 form is the swap-conjugate and is
recorded beside it.  The ordinary projector e: T_17 is a unit on the m-part (checked), so e acts as the identity there; we
compute e = lim T_17^{N} mod 17^E explicitly and check e * e_m = e_m.

CLI: ``python -m langlandscape.hacs_bridge.betti_t4 [--hacs BIN] [--out FILE] [--ks 12,28,...] [--no-offroute]
[--allow-module-z]``.
"""

from __future__ import annotations

import argparse
import functools
import importlib.util
import json
import math
import pathlib
import sys
import time
from fractions import Fraction
from typing import Sequence

import sympy as sp

from . import runner

ELL = 17
QPRIME = 3                       # the amalgam prime (called p in task1_v6)
KS = (12, 28, 44, 60, 124)
N_MAX_HACS = 60                  # descent(N, n, primes): 0 <= n <= 60
TAU = {2: -24, 3: 252, 17: -6905934}
E_DEFAULT = 12                   # work mod 17^E; every reported valuation is checked < E
SEED_EXPECTED = {12: 1, 28: 1, 44: 1, 60: 1, 124: 2}        # seed prediction ord_17 c_3 (\stexp, not gating)
RN6 = {12: 1, 28: 1, 44: 1, 60: 1}                           # checks-results-2026-11-14 RN-6 (B14): ord_17 c_3
TASK1C_K12 = [1, 1]                                          # exchange Task 1(c): coker(alpha*alpha) at m_Delta = (Z/17)^2
Q4_STATUS = "default no (pending Fabian)"                    # may this WP call HACS module_Z()?
KGEELL_INTERPRETATION = "expected (k >= ell: outside the if:s03-amalgam range l > k; S06-M7 \\stexp)"

AMALGAM_REL = "code/hacs/docs/jl_exchange/hacs-answers/task1_v6/scripts/amalgam.py"
CELL_K12_REL = "code/hacs/docs/jl_exchange/hacs-answers/task1_v6/data/cells/cell_p3_k12.json"

CONVENTIONS = {
    "source": "code/hacs/docs/jl_exchange/hacs-answers/task1_v6/results.md section 0 (verbatim); amalgam prime p := q = 3",
    "g": "g = diag(1, p)",
    "kappa": "kappa(c)(x) = rho_n(g) c(g^{-1} x g)",
    "alpha": "alpha(x, y) = dg_1 x - dg_p y",
    "alpha_star": "alpha*(z) = (omega z, -omega' z), omega = cor^{SL_2(Z)}_{Gamma_0(p)}, omega' = kappa^{-1} o cor^{G_2}_{Gamma_0(p)}",
    "alpha_star_alpha": "alpha*alpha = [[p+1, -T_p], [-p^{2-k} T_p, p+1]] on H^1(SL_2(Z), V)^2",
    "T_q": "classical T_q (no p^{k/2-1} twist); HACS free block F in the column convention T b_j = sum_i F_ij b_i",
    "s03_form": "s03 (code/results/s03/C3_rerun.json): [[q+1, -q^{2-k} T_q], [-T_q, q+1]] = J (alpha*alpha) J, J = [[0,1],[1,0]] "
                 "(block swap); same determinant and isomorphic cokernel (both computed and compared per k)",
    "rho_n": "column j of rho_n(A) holds the coefficients of (ax+cy)^{n-j}(bx+dy)^j in the basis x^{n-t}y^t",
}


def repo_root() -> pathlib.Path:
    return pathlib.Path(__file__).resolve().parents[4]


# ------------------------------------------------------------------ local linear algebra over Z_l (mod l^E)
def vl(x: int, ell: int) -> int:
    x = int(x)
    if x == 0:
        raise ValueError("v_l(0)")
    v = 0
    while x % ell == 0:
        x //= ell
        v += 1
    return v


def to_mod(x, Q: int) -> int:
    if isinstance(x, Fraction):
        return x.numerator * pow(x.denominator, -1, Q) % Q
    if isinstance(x, sp.Rational) and not isinstance(x, sp.Integer):
        return int(x.p) * pow(int(x.q), -1, Q) % Q
    return int(x) % Q


def local_smith(M: Sequence[Sequence[int]], ell: int, E: int) -> list[int]:
    """Valuations of the elementary divisors of an integer (or l-integral) matrix over Z_l, computed mod l^E.

    The value E stands for "zero mod l^E" (i.e. valuation >= E, in particular a free part of the cokernel)."""
    Q = ell ** E
    A = [[to_mod(x, Q) for x in row] for row in M]
    rows = len(A)
    cols = len(A[0]) if rows else 0
    out: list[int] = []
    for k in range(min(rows, cols)):
        best = None
        for i in range(k, rows):
            for j in range(k, cols):
                if A[i][j]:
                    v = vl(A[i][j], ell)
                    if best is None or v < best[0]:
                        best = (v, i, j)
                        if v == 0:
                            break
            if best is not None and best[0] == 0:
                break
        if best is None:
            out += [E] * (min(rows, cols) - k)
            break
        v, i, j = best
        A[k], A[i] = A[i], A[k]
        for row in A:
            row[k], row[j] = row[j], row[k]
        piv = A[k][k]
        u = pow(piv // ell ** v, -1, Q)
        for i2 in range(k + 1, rows):
            if A[i2][k]:
                f = (A[i2][k] // ell ** v) * u % Q
                A[i2] = [(x - f * y) % Q for x, y in zip(A[i2], A[k])]
        for j2 in range(k + 1, cols):
            if A[k][j2]:
                f = (A[k][j2] // ell ** v) * u % Q
                for row in A:
                    row[j2] = (row[j2] - f * row[k]) % Q
        out.append(v)
    return out


def module_from_vals(vals: Sequence[int], E: int) -> dict:
    """Torsion part of the cokernel (elementary divisors l^v, 0 < v < E) plus the count of vals >= E (free / unresolved)."""
    tors = sorted(v for v in vals if 0 < v < E)
    return {"elementary_divisor_valuations": tors, "length": sum(tors), "unresolved_or_free": sum(1 for v in vals if v >= E)}


def mat_mul(A, B, Q):
    n, m, p = len(A), len(B), len(B[0])
    Bt = list(zip(*B))
    return [[sum(A[i][t] * Bt[j][t] for t in range(m)) % Q for j in range(p)] for i in range(n)]


def mat_pow(A, N: int, Q: int):
    n = len(A)
    R = [[int(i == j) for j in range(n)] for i in range(n)]
    B = [row[:] for row in A]
    while N:
        if N & 1:
            R = mat_mul(R, B, Q)
        N >>= 1
        if N:
            B = mat_mul(B, B, Q)
    return R


def poly_at_matrix(coeffs_high_low: Sequence[int], T, Q: int):
    n = len(T)
    R = [[0] * n for _ in range(n)]
    for c in coeffs_high_low:
        R = mat_mul(R, T, Q)
        for i in range(n):
            R[i][i] = (R[i][i] + int(c)) % Q
    return R


def charpoly_mod_prime(T, ell: int) -> list[int]:
    """det(x - T) mod ell, coefficients high -> low."""
    from sympy.polys.matrices import DomainMatrix
    F = sp.GF(ell)
    n = len(T)
    dm = DomainMatrix([[F(int(x) % ell) for x in row] for row in T], (n, n), F)
    return [int(c) % ell for c in dm.charpoly()]


def primary_idempotent(T, lam: int, ell: int, E: int):
    """The idempotent of Z_l[T] (as a matrix mod l^E) onto the generalised eigenspace of T for the residue lam mod l.

    Returns (e, a) with a = multiplicity of (x - lam) in char(T) mod l (= rank of e)."""
    Q = ell ** E
    n = len(T)
    x = sp.symbols("x")
    chi = sp.Poly(charpoly_mod_prime(T, ell), x, modulus=ell)
    lin = sp.Poly(x - lam, x, modulus=ell)
    a = 0
    g = chi
    while True:
        qq, r = sp.div(g, lin)
        if not r.is_zero:
            break
        g, a = qq, a + 1
    if a == 0:
        return [[0] * n for _ in range(n)], 0
    s, t, h = sp.gcdex(g, lin ** a)          # s g + t (x-lam)^a = h = 1
    assert h.as_expr() == 1
    sg = (s * g)
    coeffs = [int(c) % ell for c in sg.all_coeffs()]
    e = poly_at_matrix(coeffs, [[int(v) % Q for v in row] for row in T], Q)
    for _ in range(64):                       # Newton / idempotent lifting e <- 3e^2 - 2e^3
        e2 = mat_mul(e, e, Q)
        if e2 == e:
            return e, a
        e3 = mat_mul(e2, e, Q)
        e = [[(3 * u - 2 * w) % Q for u, w in zip(r2, r3)] for r2, r3 in zip(e2, e3)]
    raise RuntimeError("idempotent lifting did not converge")


def ordinary_idempotent(T, ell: int, E: int):
    """e = lim T^{N!} mod l^E, as T^N with N = l^{E+4} * lcm_{f <= r}(l^f - 1); checked idempotent."""
    Q = ell ** E
    r = len(T)
    N = ell ** (E + 4 + int(math.log(max(r, 2), ell)) + 1)
    for f in range(1, r + 1):
        N = N * (ell ** f - 1) // math.gcd(N, ell ** f - 1)
    e = mat_pow([[int(v) % Q for v in row] for row in T], N, Q)
    if mat_mul(e, e, Q) != e:
        raise RuntimeError("T^N is not idempotent mod l^E")
    return e


def rank_mod(M, ell: int) -> int:
    return sum(1 for v in local_smith(M, ell, 1) if v == 0)


def block_ops(Tq, c: int, q: int, Q: int):
    """alpha*alpha (task1_v6) and the s03 form, as 2r x 2r matrices mod Q, from the T_q matrix (mod Q).

    task1_v6: [[q+1, -T], [-q^{2-k} T, q+1]];  s03: [[q+1, -q^{2-k} T], [-T, q+1]]."""
    r = len(Tq)
    def blk(a11, a12, a21, a22):
        out = [[0] * (2 * r) for _ in range(2 * r)]
        for i in range(r):
            for j in range(r):
                out[i][j] = a11[i][j]; out[i][r + j] = a12[i][j]
                out[r + i][j] = a21[i][j]; out[r + i][r + j] = a22[i][j]
        return out
    I4 = [[(q + 1) * int(i == j) % Q for j in range(r)] for i in range(r)]
    mT = [[(-v) % Q for v in row] for row in Tq]
    mcT = [[(-v * c) % Q for v in row] for row in Tq]      # c = q^{2-k} mod Q
    return blk(I4, mT, mcT, I4), blk(I4, mcT, mT, I4)


def localise(Mx, e_small, Q: int):
    """Mx * diag(e, e) + (1 - diag(e, e)): its cokernel is e * coker(Mx) when Mx commutes with e."""
    r = len(e_small)
    n = 2 * r
    Eb = [[0] * n for _ in range(n)]
    for i in range(r):
        for j in range(r):
            Eb[i][j] = e_small[i][j]; Eb[r + i][r + j] = e_small[i][j]
    ME = mat_mul(Mx, Eb, Q)
    return [[(ME[i][j] + int(i == j) - Eb[i][j]) % Q for j in range(n)] for i in range(n)]


def commutes(A, B, Q):
    return mat_mul(A, B, Q) == mat_mul(B, A, Q)


def betti_from_hecke_matrices(T: dict[int, list], k: int, E: int = E_DEFAULT) -> dict:
    """Common back end of both Betti routes: T[p] are l-integral matrices (mod-able) of T_2, T_3, T_17 on L.

    If 'X' and 'Y' are present they are the actual off-diagonal blocks omega o dg_q and omega' o dg_1, and 'D1', 'Dq' (if
    present) the actual diagonal blocks omega o dg_1 and omega' o dg_q (checked = q+1, as in cell.py); else
    X = T_3, Y = 3^{2-k} T_3 and the diagonal is q+1 (task1_v6 section 0)."""
    Q = ELL ** E
    Tm = {p: [[to_mod(v, Q) for v in row] for row in M] for p, M in T.items() if isinstance(p, int)}
    r = len(Tm[3])
    c = pow(pow(QPRIME, k - 2, Q), -1, Q)   # q^{2-k} mod 17^E (q a 17-adic unit)
    out: dict = {"rank_L": r}
    e3, a3 = primary_idempotent(Tm[3], TAU[3] % ELL, ELL, E)
    e2, a2 = primary_idempotent(Tm[2], TAU[2] % ELL, ELL, E)
    em = mat_mul(e3, e2, Q)
    out["rank_e_T3"] = a3
    out["rank_e_T2"] = a2
    out["rank_e_m"] = rank_mod(em, ELL)
    out["e_m_idempotent"] = mat_mul(em, em, Q) == em
    out["e_T3_equals_e_m"] = em == e3
    # ordinary projector
    t17 = Tm[17]
    e_ord = ordinary_idempotent(t17, ELL, E)
    out["rank_e_ord"] = rank_mod(e_ord, ELL)
    out["e_ord_e_m_equals_e_m"] = mat_mul(e_ord, em, Q) == em
    out["T17_unit_on_m_part"] = rank_mod([[(mat_mul(t17, em, Q)[i][j] + int(i == j) - em[i][j]) % Q for j in range(r)]
                                          for i in range(r)], ELL) == r
    # blocks
    if "X" in T:
        X = [[to_mod(v, Q) for v in row] for row in T["X"]]
        Y = [[to_mod(v, Q) for v in row] for row in T["Y"]]
        out["check_X_equals_T3"] = X == Tm[3]
        out["check_Y_equals_q^(2-k)X"] = Y == [[v * c % Q for v in row] for row in X]
        I4 = [[(QPRIME + 1) * int(i == j) for j in range(r)] for i in range(r)]
        if "D1" in T:
            D1 = [[to_mod(v, Q) for v in row] for row in T["D1"]]
            Dq = [[to_mod(v, Q) for v in row] for row in T["Dq"]]
            out["check_omega_dg_1_equals_q+1"] = D1 == I4
            out["check_omega'_dg_q_equals_q+1"] = Dq == I4
            if D1 != I4 or Dq != I4:
                raise RuntimeError(f"diagonal blocks of alpha*alpha are not q+1 at k = {k}")
            out["blocks"] = ("all four blocks actual composites: omega o dg_1, omega' o dg_q (diagonal, computed, = q+1 "
                             "checked), omega o dg_q (X), omega' o dg_1 (Y)")
        else:
            D1 = Dq = I4
            out["blocks"] = ("off-diagonal blocks actual composites omega o dg_q (X), omega' o dg_1 (Y); diagonal q+1 "
                             "(not computed)")
        AA = [[0] * (2 * r) for _ in range(2 * r)]
        for i in range(r):
            for j in range(r):
                AA[i][j] = D1[i][j]; AA[r + i][r + j] = Dq[i][j]
                AA[i][r + j] = (-X[i][j]) % Q; AA[r + i][j] = (-Y[i][j]) % Q
        _, S03 = block_ops(Tm[3], c, QPRIME, Q)
    else:
        AA, S03 = block_ops(Tm[3], c, QPRIME, Q)
        out["blocks"] = "X = T_3, Y = 3^{2-k} T_3 (task1_v6 section 0 identities)"
    for p in (2, 17):
        if not commutes(Tm[3], Tm[p], Q):
            raise RuntimeError(f"T_3 and T_{p} do not commute mod 17^E")
    em_blk = [[0] * (2 * r) for _ in range(2 * r)]
    for i in range(r):
        for j in range(r):
            em_blk[i][j] = em[i][j]; em_blk[r + i][r + j] = em[i][j]
    out["alpha*alpha_commutes_with_e_m"] = commutes(AA, em_blk, Q)
    loc = localise(AA, mat_mul(e_ord, em, Q), Q)
    v_loc = local_smith(loc, ELL, E)
    v_s03 = local_smith(localise(S03, mat_mul(e_ord, em, Q), Q), ELL, E)
    v_full = local_smith(AA, ELL, E)
    out["coker_m"] = module_from_vals(v_loc, E)
    out["coker_m_s03_form"] = module_from_vals(v_s03, E)
    out["s03_form_same_coker"] = out["coker_m"] == out["coker_m_s03_form"]
    out["coker_unlocalised_17_part"] = module_from_vals(v_full, E)
    out["precision"] = f"17^{E}"
    if out["coker_m"]["unresolved_or_free"]:
        raise RuntimeError(f"valuation >= E = {E} at k = {k}: raise E")
    return out


# ------------------------------------------------------------------ HACS read: charpoly (always), module_Z (opt-in, Q4)
def hacs_module_script(n: int, allow_module_z: bool = False) -> str:
    """The HACS script. ``module_Z()`` appears in it only if ``allow_module_z`` (Q4: default no, pending Fabian)."""
    src = ('set coefficient_ring = "Z";\n'
           f"d = descent(1, {n}, [2, 3, 17]);\n"
           'print("@@GROUPS " + json(d.groups));\n'
           'for c in d.charpoly { print("@@CP " + json([c.p, c.exact, c.determined])); }\n')
    if allow_module_z:
        src += ("m = d.module_Z();\n"
                'print("@@MZ " + json(m));\n')
    return src


def hacs_read(k: int, hacs=None, allow_module_z: bool = False) -> dict:
    """HACS charpoly data (always); with ``allow_module_z`` also the module_Z free block (route A). A module_Z refusal is
    recorded (``module_Z_refusal``), never fatal: route A is supplementary."""
    n = k - 2
    res = runner.run_script(hacs_module_script(n, allow_module_z), hacs=hacs, threads=4, timeout=3600)
    cp = {}
    for p, ex, det in res.tags["CP"]:
        assert det, (k, p)
        cp[p] = [int(x) for x in ex]
    out = {"charpoly_Z": cp, "groups": res.tags["GROUPS"][0], "wall_s": round(res.wall_s, 2), "module_Z_called": False}
    if not allow_module_z:
        return out
    out["module_Z_called"] = True
    mz = res.tags["MZ"][0]
    if mz["status"] != "ok" or mz["free_block"] != "exact":
        out["module_Z_refusal"] = f"{mz.get('refusal')} {mz.get('free_refusal')}"
        return out
    out.update({"F": {op["p"]: [[int(x) for x in row] for row in op["F"]] for op in mz["ops"]},
                "charpoly_Z_module": {op["p"]: [int(x) for x in op["charpoly_Z"]] for op in mz["ops"]},
                "torsion_17": [t for t in mz["torsion_generators"] if t["ell"] == ELL], "basis": mz["basis"],
                "F_fnv": {op["p"]: op["F_fnv"] for op in mz["ops"]}})
    return out


def charpoly_exact(M) -> list[int]:
    return [int(c) for c in sp.Matrix(M).charpoly(sp.symbols("x")).all_coeffs()]


# ------------------------------------------------------------------ Betti route 2: amalgam.py (no HACS data)
def load_amalgam(root: pathlib.Path | None = None):
    path = (root or repo_root()) / AMALGAM_REL
    spec = importlib.util.spec_from_file_location("task1_v6_amalgam", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod, path


def amalgam_level1(k: int, primes=(2, 3, 17), E: int = E_DEFAULT) -> dict:
    """Exact rational level-1 model of task1_v6/amalgam.py, at q = 3.

    Basis: the classes of e_c (c non-pivot of the rational quotient) -- the coordinates of the model; the lattice
    L = image of V_{Z_(17)} = H^1(SL_2(Z), V_{Z_(17)})/tors is computed (17-saturation by HNF) and all matrices are
    conjugated into a Z_(17)-basis of L.  The model's maps come from ``amalgam.py`` (imported from its path, not copied).
    The four blocks of alpha*alpha: omega o dg_1 (module level, omega o iota), X = omega o dg_q via the Shapiro module,
    Y = omega' o dg_1 and omega' o dg_q via the transfer to G_2 over right cosets.  The block computing them is adapted,
    with attribution and snippet-level REUSE tags, from ``task1_v6/scripts/cell.py`` l. 33--61 (CC-BY-4.0)."""
    A, path = load_amalgam()
    import numpy as np
    t0 = time.perf_counter()
    p = QPRIME
    n = k - 2
    d = n + 1
    g = (1, 0, 0, p)
    gp = (p, 0, 0, 1)
    RS = np.array(A.rho(A.S, n), dtype=object)
    RU = np.array(A.rho(A.U, n), dtype=object)
    Rows1 = A.relation_rows(n, RS, RU, d)
    piv1, np1, proj1 = A.quotient_basis_Q(Rows1)
    r1 = len(np1)
    # the lattice L inside Q^{r1}: span of proj1(e_j), j = 0..n
    cols = []
    for j in range(d):
        v = [0] * d; v[j] = 1
        cols.append(proj1(v))
    P1 = sp.Matrix(r1, d, lambda i, j: sp.Rational(cols[j][i].numerator, cols[j][i].denominator))
    den = int(sp.ilcm(*[int(x.q) for x in P1]))
    if den % ELL:
        Bm = sp.eye(r1)
        lattice_note = "L = Z_(17)-span of the classes of e_c, c non-pivot (no 17 in any denominator of proj(e_j))"
    else:
        from sympy.matrices.normalforms import hermite_normal_form
        H = hermite_normal_form((P1 * den).applyfunc(sp.Integer))
        assert H.shape == (r1, r1)
        Bm = H / den
        lattice_note = f"L saturated by HNF over Z (common denominator {den}, 17-part {ELL ** vl(den, ELL)})"
    Binv = Bm.inv()
    # torsion of H^1(SL_2(Z), V_{Z_(17)}) = torsion of V/R: Smith of the relation rows at 17
    vrel = local_smith([[int(x) for x in row] for row in Rows1], ELL, E)
    tors_rel = sorted(v for v in vrel if 0 < v < E)
    # Adapted from code/hacs/docs/jl_exchange/hacs-answers/task1_v6/scripts/cell.py l. 33-61 (HACS project,
    # © Fabian Januszewski, CC-BY-4.0); changes: names qualified by the imported module A; only the non-pivot basis
    # vectors e_c are used (columns in the model's coordinates); the module-level check omega(iota v) = (p+1) v and the
    # omega' o dg_p sanity cocycle are kept but collected as the matrices D1, Dq of the diagonal blocks (later conjugated
    # into L and checked = q+1) instead of booleans; T_q for q in `primes` computed in the same loop; unused loop index
    # dropped; the assertion on inner[1] moved before its use.
    # SPDX-SnippetBegin
    # SPDX-SnippetCopyrightText: 2024-2026 Fabian Januszewski
    # SPDX-License-Identifier: CC-BY-4.0
    L = A.Level(p, n)
    def cv(v):
        return A.Cocycle1(n, [0] * d, A.vsub(A.mat_vec(A.rho(A.U, n), v), v))
    def cls(cfun):
        return proj1(A.cocycle_to_rep(n, cfun, None, [Fraction(0)] * d))
    uts = [A.mm(A.S, s) for s in L.reps]
    def idx(gam):
        return L.cls(A.mm(A.Sinv, gam))
    Xc, Yc, D1c, Dqc, Tc = [], [], [], [], {q: [] for q in primes}
    for c_ in np1:
        v = [0] * d; v[c_] = 1
        c = cv(v)
        z = lambda h, c=c: A.mat_vec(A.rho(g, n), c((h[0], h[1] * p, h[2] // p, h[3])))     # dg_p(c_v)
        Xc.append(proj1(L.omega(L.shapiro_forward(z))))
        def Ycoc(gam, c=c):                                                               # omega' o dg_1 (c_v)
            acc = [Fraction(0)] * d
            for ut in uts:
                tp = idx(A.mm(ut, gam))
                inner = A.mm(A.mm(ut, gam), A.inv1(uts[tp]))
                assert inner[1] % p == 0
                h = (inner[0], inner[1] // p, inner[2] * p, inner[3])
                acc = A.vadd(acc, A.mat_vec(A.rho(A.mm(A.inv1(ut), gp), n), c(h)))
            return [x / Fraction(p ** n) for x in acc]
        Yc.append(cls(Ycoc))
        D1c.append(proj1(L.omega(L.iota(v))))                                             # omega o dg_1 (c_v)
        def Wcoc(gam, c=c):                                                               # omega' o dg_p (c_v)
            acc = [Fraction(0)] * d
            for ut in uts:
                tp = idx(A.mm(ut, gam))
                inner = A.mm(A.mm(ut, gam), A.inv1(uts[tp]))
                assert inner[1] % p == 0
                hh = (inner[0], inner[1] // p, inner[2] * p, inner[3])
                zz = A.mat_vec(A.rho(g, n), c((hh[0], hh[1] * p, hh[2] // p, hh[3])))
                acc = A.vadd(acc, A.mat_vec(A.rho(A.mm(A.inv1(ut), gp), n), zz))
            return [x / Fraction(p ** n) for x in acc]
        Dqc.append(cls(Wcoc))
        for q in primes:
            Tc[q].append(cls(A.hecke_cocycle(c, q, n, lambda Y_: True)))
    # SPDX-SnippetEnd
    def to_L(colsQ):
        M = sp.Matrix(r1, r1, lambda i, j: sp.Rational(colsQ[j][i].numerator, colsQ[j][i].denominator))
        ML = Binv * M * Bm
        for x in ML:
            if x.q % ELL == 0:
                raise RuntimeError("matrix not 17-integral on L")
        return [[ML[i, j] for j in range(r1)] for i in range(r1)]
    T = {q: to_L(Tc[q]) for q in primes}
    T["X"] = to_L(Xc)
    T["Y"] = to_L(Yc)
    T["D1"] = to_L(D1c)
    T["Dq"] = to_L(Dqc)
    cp3 = [int(sp.Rational(c)) for c in sp.Matrix(T[3]).charpoly(sp.symbols("x")).all_coeffs()]
    return {"T": T, "rank_H1": r1, "lattice": lattice_note, "torsion_17_H1": [f"Z/17^{v}" for v in tors_rel],
            "charpoly_T3": cp3, "wall_s": round(time.perf_counter() - t0, 2), "amalgam_path": str(path)}


# ------------------------------------------------------------------ Hecke side
def cusp_charpoly_level1(cp_H1: Sequence[int], k: int, q: int) -> list[int]:
    """char_Z(T_q | H^1(SL_2(Z); Sym^{k-2})/tors) = chi_cusp^2 (x - 1 - q^{k-1})  ->  chi_cusp (exact, checked)."""
    x = sp.symbols("x")
    P = sp.Poly(cp_H1, x)
    Qt, rem = sp.div(P, sp.Poly(x - (1 + q ** (k - 1)), x))
    assert rem.is_zero, "Eisenstein factor does not divide"
    lc, facs = sp.factor_list(Qt.as_expr())
    assert lc == 1
    res = sp.Poly(1, x)
    for f, m in facs:
        assert m % 2 == 0, "H^1/Eis is not a square"
        res *= sp.Poly(f, x) ** (m // 2)
    return [int(c) for c in res.all_coeffs()]


def branch_factors(chi: Sequence[int], lam: int, ell: int = ELL, prec: int = 30) -> list[list[int]]:
    """17-adic factors h of chi (monic, coefficients mod 17^prec, high -> low) with h mod 17 a power of (x - lam)."""
    import cypari2
    pari = cypari2.Pari()
    x = pari("x")
    fac = pari.factorpadic(pari.Pol([int(c) for c in chi]), ell, prec)
    out = []
    for i in range(int(pari.matsize(fac)[0])):
        h = [int(pari.lift(c)) for c in pari.Vec(fac[0][i])]
        mult = int(fac[1][i])
        hbar = pari.Pol([pari.Mod(c, ell) for c in h])
        dgr = len(h) - 1
        if hbar == pari.Mod(1, ell) * (x - lam) ** dgr:
            out += [h] * mult
    return out


def hecke_side(chi_cusp: Sequence[int], k: int, E: int = E_DEFAULT) -> dict:
    """length_{Z_17} T(1)_m/(delta), T(1)_m = Z_17[x]/(h), h = the branch factor of chi_cusp(T_3) through tau(3).

    The module structure of Z_17[x]/(h, 16 q^{k-2} - x^2) is the Smith form of 16 q^{k-2} - C_h^2 (C_h companion of h)."""
    hs = branch_factors(chi_cusp, TAU[3] % ELL)
    if not hs:
        return {"status": "computed", "branch_degree": 0, "length": 0, "T_m_over_delta": module_from_vals([], E)}
    if len(hs) > 1:
        raise RuntimeError("several branch factors (repeated T_3 eigenvalue): T(1)_m not monogenic in T_3 here")
    h = hs[0]
    dgr = len(h) - 1
    Q = ELL ** E
    C = [[0] * dgr for _ in range(dgr)]                  # companion of h (column convention)
    for i in range(1, dgr):
        C[i][i - 1] = 1
    for i in range(dgr):
        C[i][dgr - 1] = (-h[dgr - i]) % Q
    C2 = mat_mul(C, C, Q)
    A16 = 16 * pow(QPRIME, k - 2, Q) % Q
    D = [[(A16 * int(i == j) - C2[i][j]) % Q for j in range(dgr)] for i in range(dgr)]
    mod = module_from_vals(local_smith(D, ELL, E), E)
    if mod["unresolved_or_free"]:
        raise RuntimeError("Hecke side: valuation >= E")
    lam_mod = h[-1] * -1 % Q if dgr == 1 else None
    return {"status": "computed" if dgr == 1 else "open",
            **({} if dgr == 1 else {"reason": f"branch degree {dgr} > 1: T(1)_m = Z_17[T_3] (monogenic) not checked"}),
            "branch_degree": dgr,
            "monogenic": ("T(1)_m has Z_17-rank 1 (one 17-adic eigenform with a_3 = tau(3) mod 17), so T(1)_m = Z_17 = Z_17[T_3]"
                          if dgr == 1 else "not checked (degree > 1)"),
            "T_m_over_delta": mod, "length": mod["length"],
            "a3_mod_17^E": lam_mod,
            "delta_integral": "3^{k-2} delta = 16*3^{k-2} - T_3^2 (3 a 17-adic unit)"}


@functools.lru_cache(maxsize=None)
def _pari_t_proxy_cached(k: int) -> str:
    return json.dumps(_pari_t_proxy(k))


def pari_t_proxy(k: int) -> dict:
    return json.loads(_pari_t_proxy_cached(k))


def _pari_t_proxy(k: int) -> dict:
    """ord_17(a_3(G_k)^2 - 16*3^{k-2}) on the 17-adic eigenform G_k of S_k(SL_2(Z)) with a_3 = tau(3) mod 17 (PARI mf)."""
    import cypari2
    pari = cypari2.Pari()
    t = time.perf_counter()
    mf = pari(f"mfinit([1,{k}],1)")
    cp = pari.charpoly(pari.mfheckemat(mf, 3))
    chi = [int(c) for c in pari.Vec(cp)]
    hs = branch_factors(chi, TAU[3] % ELL)
    if len(hs) != 1:
        return {"status": "open", "reason": f"branch degree {len(hs)} in T_3 (not 1)"}
    h = hs[0]
    res = pari.polresultant(pari.Pol(h), pari(f"16*3^{k-2} - x^2"))
    v = int(pari.valuation(res, ELL))
    return {"status": "computed", "value": v, "branch_degree": len(h) - 1, "charpoly_T3_cusp_PARI": chi,
            "wall_s": round(time.perf_counter() - t, 2),
            "method": "PARI mfinit/mfheckemat (q-expansion Hecke matrices; independent of HACS and of amalgam.py); "
                      "proxy formula of stage-06 H1: ord_17(a_3(G_k)^2 - 3^{k-2} 16) on the old branch",
            "caveat": "the identification of this proxy with the Kim-Ota / Pollack-Weston Tamagawa exponent t_f(3) of the "
                      "3-new form is not checked here (cor:s06-allweights, \\stpmc)"}


# ------------------------------------------------------------------ one weight
ROUTE_A_OFF = ("not run: HACS module_Z() is OFF by default (Q4: default no, pending Fabian); opt in with --allow-module-z "
               "/ allow_module_z=True")


def run_k(k: int, hacs=None, E: int = E_DEFAULT, allow_module_z: bool = False) -> dict:
    t0 = time.perf_counter()
    row: dict = {"k": k, "n": k - 2, "k_mod_16": k % 16,
                 "expected": {"status": "expected", "ord17_c3_seed": SEED_EXPECTED[k],
                              "Betti_expected_from_seed": [SEED_EXPECTED[k]] * 2}}
    row["t_G_proxy"] = pari_t_proxy(k)
    if k - 2 > N_MAX_HACS:
        reason = (f"HACS descent caps Sym^n at n <= {N_MAX_HACS}; k = {k} needs n = {k - 2}. Confirmed on the binary: "
                  "'type error: descent(N, n, primes): n must satisfy 0 <= n <= 60 (the cost bound of this verb)', exit 3")
        row["status"] = "not_reachable"
        row["betti_hacs"] = {"status": "not_reachable", "reason": reason, "gating": False}
        row["hecke"] = {"status": "not_reachable", "reason": reason}
        row["pending_crosscheck"] = "S06-C3"
        return row
    hr = hacs_read(k, hacs, allow_module_z)
    # Hecke side (HACS descent(...).charpoly only)
    chi = cusp_charpoly_level1(hr["charpoly_Z"][3], k, 3)
    hk = hecke_side(chi, k, E)
    hk["source"] = "HACS descent(1, k-2, [2,3,17]).charpoly: exact char_Z(T_3 | H^1/tors), cusp part"
    hk["charpoly_T3_cusp"] = [str(c) for c in chi]
    hk["hacs_groups"] = hr["groups"]
    hk["hacs_wall_s"] = hr["wall_s"]
    row["hecke"] = hk
    # Betti route B (gating): amalgam
    am = amalgam_level1(k, E=E)
    ba = betti_from_hecke_matrices(am["T"], k, E)
    ba.update({"status": "computed", "gating": True, "source": "task1_v6/scripts/amalgam.py (imported), no HACS data",
               "lattice": am["lattice"], "torsion_17_H1": am["torsion_17_H1"], "rank_H1": am["rank_H1"],
               "charpoly_T3_equals_HACS": am["charpoly_T3"] == hr["charpoly_Z"][3], "amalgam_wall_s": am["wall_s"]})
    if k >= ELL:
        ba["interpretation"] = KGEELL_INTERPRETATION
        row["interpretation"] = KGEELL_INTERPRETATION
    row["betti_amalgam"] = ba
    # Betti route A (supplementary, opt-in): HACS module_Z
    if not allow_module_z:
        bh = {"status": "not_run", "reason": ROUTE_A_OFF, "gating": False, "needs": "Q4"}
    elif "F" not in hr:
        bh = {"status": "refused", "reason": f"module_Z refused: {hr.get('module_Z_refusal')}", "supplementary": True,
              "gating": False, "needs": "Q4"}
    else:
        bh = betti_from_hecke_matrices(hr["F"], k, E)
        bh.update({"status": "computed", "supplementary": True, "gating": False, "needs": "Q4",
                   "source": "HACS module_Z() free block F (exact over Z, basis " + hr["basis"]["rule"] + "), T_2, T_3, T_17",
                   "charpoly_F3_equals_charpoly_Z": charpoly_exact(hr["F"][3]) == hr["charpoly_Z"][3],
                   "F_fnv": hr["F_fnv"], "hacs_torsion_17": hr["torsion_17"]})
    row["betti_hacs"] = bh
    v = hk.get("T_m_over_delta", {}).get("elementary_divisor_valuations", [])
    want = sorted(v + v)
    hk_ok = hk["status"] == "computed"
    row["agreement"] = {
        "betti_amalgam_iso_(T_m/delta)^2": hk_ok and ba["coker_m"]["elementary_divisor_valuations"] == want,
        "t_G_proxy_equals_hecke_length": row["t_G_proxy"].get("value") == hk["length"],
        "RN6_ord17_c3": RN6.get(k), "hecke_length_equals_RN6": RN6.get(k) == hk["length"],
        "seed_expected_matches": SEED_EXPECTED[k] == hk["length"],
    }
    if bh["status"] == "computed":
        row["agreement"]["supplementary_route_A"] = {
            "gating": False, "needs": "Q4",
            "betti_hacs_iso_(T_m/delta)^2": bh["coker_m"]["elementary_divisor_valuations"] == want,
            "betti_hacs_equals_betti_amalgam": bh["coker_m"] == ba["coker_m"]}
    if k == 12:
        row["agreement"]["task1c_(Z/17)^2"] = ba["coker_m"]["elementary_divisor_valuations"] == TASK1C_K12
        try:
            cell = json.loads((repo_root() / CELL_K12_REL).read_text())
            row["agreement"]["task1c_cell_alpha*alpha_vals"] = cell["ell"]["17"]["alpha*alpha_elementary_divisor_valuations"]
        except (OSError, KeyError, ValueError):
            pass
    row["status"] = "computed"
    row["pending_crosscheck"] = "S06-C3"
    row["wall_s"] = round(time.perf_counter() - t0, 2)
    return row


def offroute_k(k: int, E: int = E_DEFAULT) -> dict:
    """Beyond the HACS cap: amalgam Betti and PARI Hecke data only (supplementary, not part of the HACS route)."""
    t0 = time.perf_counter()
    am = amalgam_level1(k, E=E)
    ba = betti_from_hecke_matrices(am["T"], k, E)
    ba.update({"lattice": am["lattice"], "torsion_17_H1": am["torsion_17_H1"], "rank_H1": am["rank_H1"]})
    tp = pari_t_proxy(k)
    hk = hecke_side(tp["charpoly_T3_cusp_PARI"], k, E) if tp["status"] == "computed" else {"status": "open"}
    hk["source"] = "PARI mfheckemat charpoly of T_3 on S_k(1) (not HACS)"
    v = hk.get("T_m_over_delta", {}).get("elementary_divisor_valuations", [])
    return {"k": k, "status": "computed", "gating": False, "interpretation": KGEELL_INTERPRETATION,
            "note": "supplementary, off the HACS route (HACS cap n <= 60): Betti from amalgam.py alone, Hecke side from PARI; "
                    "amalgam beyond the if:s03-amalgam range l > k, so the reading as coker(Psi*Psi)_m of prop:s06-betti is \\stexp",
            "betti_amalgam": ba, "hecke_pari": hk,
            "betti_iso_(T_m/delta)^2": hk.get("status") == "computed"
                                       and ba["coker_m"]["elementary_divisor_valuations"] == sorted(v + v),
            "seed_expected_matches": hk.get("length") == SEED_EXPECTED.get(k),
            "wall_s": round(time.perf_counter() - t0, 2)}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--hacs", default=None)
    ap.add_argument("--out", default=str(repo_root() / "code/results/s06/T4_betti.json"))
    ap.add_argument("--ks", default=",".join(map(str, KS)))
    ap.add_argument("--E", type=int, default=E_DEFAULT)
    ap.add_argument("--no-offroute", action="store_true")
    ap.add_argument("--allow-module-z", action="store_true",
                    help="also run route A (HACS module_Z(); supplementary, non-gating; Q4: default no, pending Fabian)")
    a = ap.parse_args(argv)
    ks = [int(x) for x in a.ks.split(",")]
    t0 = time.perf_counter()
    rows = []
    for k in ks:
        r = run_k(k, a.hacs, a.E, a.allow_module_z)
        print(f"k={k}: {r['status']}", file=sys.stderr)
        rows.append(r)
    off = []
    if not a.no_offroute:
        off = [offroute_k(k, a.E) for k in ks if k - 2 > N_MAX_HACS]
    reach = [r for r in rows if r["status"] == "computed"]
    acc = {
        "k12_task1c_(Z/17)^2": next((r["agreement"].get("task1c_(Z/17)^2") for r in reach if r["k"] == 12), None),
        "gating_route": "B (amalgam)",
        "betti_iso_(T_m/delta)^2_all_reachable": all(r["agreement"]["betti_amalgam_iso_(T_m/delta)^2"] for r in reach),
        "RN6_agree_all_reachable": all(r["agreement"]["hecke_length_equals_RN6"] for r in reach if r["k"] in RN6),
        "seed_prediction": {"status": "expected", "gating": False, "values": SEED_EXPECTED},
        "pending_crosscheck": "S06-C3",
    }
    acc["pass"] = bool(acc["k12_task1c_(Z/17)^2"] and acc["betti_iso_(T_m/delta)^2_all_reachable"]
                       and acc["RN6_agree_all_reachable"])
    runtime = round(time.perf_counter() - t0, 2)
    params = {"module_z_allowed": a.allow_module_z, "Q4": Q4_STATUS, "q": QPRIME, "p": ELL, "ell": ELL, "ks": ks, "E": a.E, "hacs_primes": [2, 3, 17], "N_max_hacs": N_MAX_HACS,
              "tau": TAU, "branch": "17-adic eigensystem of Delta-type (T_2 = -24, T_3 = 252 mod 17), k = 12 mod 16"}
    out = {"provenance": runner.provenance("code/python/langlandscape/hacs_bridge/betti_t4.py", params, runtime, a.hacs),
           "data": {"module_z_allowed": a.allow_module_z, "Q4": Q4_STATUS, "conventions": CONVENTIONS,
                    "localisation": ("m = (17, T_2 + 24, T_3 - 252, ...): the m-part of L (x) Z_17 is cut out by e_m = e_2(T_2) e_3(T_3), "
                                     "the primary idempotents for the residues tau(2), tau(3) mod 17 (lifted mod 17^E). At every k "
                                     "here e_m = e_{T_3} already (checked: e_T3_equals_e_m), so T_2 plays no role in the "
                                     "localisation; e_{T_2} alone would not suffice (at k = 60 the residue tau(2) has T_2-multiplicity "
                                     "4 > 2 = rank e_m, see rank_e_T2), but multiplying by it does not change e_{T_3}. At level 1 "
                                     "the T_3-branch has degree 1, so it is one eigenform, of Delta-type by Deligne-Serre applied to "
                                     "Delta * E_16^{(k-12)/16} (E_16 = 1 mod 17). coker(M)_m = coker(M diag(e,e) + 1 - diag(e,e))."),
                    "ordinary_projector": ("e = lim T_17^{N!}, computed as T_17^N mod 17^E and checked idempotent. T_17 = tau(17) = 10 "
                                           "mod 17 is a unit on the m-part (checked: T17_unit_on_m_part), so e e_m = e_m (checked): "
                                           "e acts as the identity on the m-part and e coker(Psi*Psi)_m = coker(Psi*Psi)_m."),
                    "routes": {"betti_amalgam": "route B, GATING. task1_v6 amalgam.py (imported) + transfer block adapted from "
                                                "cell.py: all four blocks of alpha*alpha as actual composites from cocycles "
                                                "(diagonal checked = q+1); no HACS data",
                               "betti_hacs": "route A, " + ("supplementary, gating: false, needs: Q4" if a.allow_module_z else
                                             "NOT RUN (module_Z() off by default; Q4: default no, pending Fabian)")
                                             + ". HACS module_Z() integral T_q on H^1/tors, alpha*alpha in the task1_v6 convention",
                               "hecke": "HACS descent(...).charpoly only: exact char_Z(T_3) (cusp part), "
                                        "length Z_17[x]/(h, 16*3^{k-2} - x^2); status open if branch degree > 1",
                               "t_G_proxy": "PARI mf, stage-06 H1 proxy ord_17(a_3^2 - 16*3^{k-2})"},
                    "hecke_structure": "not read: this WP uses descent / charpoly (and module_Z only if opted in), so no default_fp / "
                                       "hz_theta_order is involved (the binary's hecke_structure records are not consulted)",
                    "table": [{"k": r["k"], "status": r["status"],
                               "betti_hacs": r.get("betti_hacs", {}).get("coker_m", {}).get("elementary_divisor_valuations"),
                               "betti_amalgam": r.get("betti_amalgam", {}).get("coker_m", {}).get("elementary_divisor_valuations"),
                               "hecke_status": r.get("hecke", {}).get("status"),
                               "hecke_length": r.get("hecke", {}).get("length"),
                               "interpretation": r.get("interpretation"),
                               "t_G_proxy": r["t_G_proxy"].get("value"),
                               "expected_seed": SEED_EXPECTED[r["k"]], "RN6": RN6.get(r["k"])} for r in rows],
                    "acceptance": acc, "rows": rows, "supplementary_off_route": off,
                    "amalgam_licence": ("amalgam.py: CC-BY-4.0 (HACS answer to the JL exchange, task1_v6), imported from its "
                                        "path, not copied. The omega/omega' block of amalgam_level1 is adapted from "
                                        "task1_v6/scripts/cell.py l. 33-61 (HACS project, (c) Fabian Januszewski, CC-BY-4.0), "
                                        "with attribution and SPDX snippet tags in betti_t4.py"),
                    "rn6_source": "plan/hacs/checks-results-2026-11-14.md RN-6 (B14), b14_t4.oc / b14_post.py"}}
    p = pathlib.Path(a.out)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=1, default=str) + "\n")
    print(json.dumps(acc, indent=1, default=str))
    return 0 if acc["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
