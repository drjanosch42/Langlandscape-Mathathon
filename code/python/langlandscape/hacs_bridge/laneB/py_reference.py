# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Python reference values + timings for Brandt lattices of B_{q,oo}, q prime < QMAX (lane B, HJ-6 reference).

Writes code/results/laneB/py_reference.json (results.py conventions).  Run from code/python:
  python -m langlandscape.hacs_bridge.laneB.py_reference.py [QMAX=1000] [NPROC=16]

Per q: h; Eisenstein congruence module L/(Z e + L_cusp), e = constant function, L = Z^h (indicator basis),
L_cusp = Z-primitive orthogonal complement of e for the pairing <f,g> = sum_x f(x)g(x)/|Gamma_x|  (the pairing
for which all T_p are self-adjoint; w_x = |Gamma_x|/2 gives the same pairing up to scalar, hence the same lattice).
Closed form: phi(f) = sum f(x)(N/|Gamma_x|), N = lcm|Gamma_x|;  L/(Ze+L_cusp) = gZ/phi(e)Z, g = gcd(N/|Gamma_x|),
cyclic of order phi(e)/g.  Expected num((q-1)/12) (Mazur 1977; Gross 1987, cited).
Hecke-algebra index: Z-span A of all monomials in the T_p (p <= 13, p != q) inside M_h(Z) (h <= HMAX_SNF only);
Smith invariants d_i of A inside its saturation (A^sat/A = sum Z/d_i).
"""
from __future__ import annotations
import math, multiprocessing as mp, sys, time
from math import gcd
from fractions import Fraction
sys.path.insert(0, __import__("pathlib").Path(__file__).resolve().parent.as_posix())
import brandt_fbz as bf  # noqa: E402
from langlandscape import brandt, results  # noqa: E402
from langlandscape.pari import get_pari  # noqa: E402
from langlandscape.quat import prime_factors  # noqa: E402

HMAX_SNF = 20   # Hecke-algebra Smith only for h <= this (T_p cost); ops = primes <= 13, p != q


def eis_module(gammas):
    N = math.lcm(*gammas)
    c = [N // g for g in gammas]
    gg = math.gcd(*c)
    return sum(c) // gg


def hecke_smith(Ts, h):
    pari = get_pari()
    gens = [[[int(x) for x in r] for r in T] for T in Ts]
    I = [[int(i == j) for j in range(h)] for i in range(h)]
    flat = lambda M: [x for r in M for x in r]
    mul = brandt.matmul
    basis = [I]
    def lat(mats):
        cols = [flat(M) for M in mats]
        Mt = pari.matrix(h * h, len(cols), [cols[j][i] for i in range(h * h) for j in range(len(cols))])
        H = pari.mathnf(Mt)
        return H, int(pari.matsize(H)[1])
    H, r = lat(basis)
    for _ in range(h + 2):
        new = list(basis) + [mul(T, M) for T in gens for M in basis]
        H2, r2 = lat(new)
        # keep a basis of the lattice as matrices: columns of HNF
        cols = [[int(H2[i, j]) for i in range(h * h)] for j in range(r2)]
        newbasis = [[c[i * h:(i + 1) * h] for i in range(h)] for c in cols]
        if H2 == H:
            break
        H, r, basis = H2, r2, newbasis
    H = H
    snf = pari.matsnf(H)
    inv = [int(x) for x in snf if int(x) > 1]
    return {"rank": r, "smith_nontrivial": inv}


def one(q):
    t0 = time.perf_counter()
    m = brandt.module(q)
    t_cls = time.perf_counter() - t0
    num = (q - 1) // gcd(q - 1, 12)
    order = eis_module(m.gammas)
    rec = {"q": q, "h": m.h, "num_q_minus_1_over_12": num, "eis_order": order, "eis_order_eq_num": order == num,
           "eis_v_ell": {str(l): _v(order, l)
                         for l in prime_factors(num) if l >= 5},
           "mass_ok": sum(Fraction(1, g) for g in m.gammas) == Fraction(q - 1, 24), "t_class_set_s": t_cls}
    if m.h <= HMAX_SNF:
        ops = [p for p in bf.primes_upto(13) if p != q]
        t1 = time.perf_counter()
        Ts = [m.T(p) for p in ops]
        rec["t_brandt_ops_s"] = time.perf_counter() - t1
        rec["ops"] = ops
        t2 = time.perf_counter()
        rec["hecke_Z_index"] = hecke_smith(Ts, m.h)
        rec["t_smith_s"] = time.perf_counter() - t2
    else:
        t1 = time.perf_counter(); m.T(2); rec["t_T2_s"] = time.perf_counter() - t1
    rec["t_total_s"] = time.perf_counter() - t0
    return rec


def _v(n, l):
    v = 0
    while n % l == 0:
        n //= l; v += 1
    return v


if __name__ == "__main__":
    qmax = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    npr = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    qs = [q for q in bf.primes_upto(qmax) if q >= 11]
    qs.sort(reverse=True)
    with results.Timer() as t, mp.get_context("spawn").Pool(npr, maxtasksperchild=1) as pool:
        recs = []
        for r in pool.imap_unordered(one, qs, chunksize=1):
            recs.append(r); print(r["q"], r["h"], round(r["t_total_s"], 1), flush=True)
    recs.sort(key=lambda r: r["q"])
    results.write("laneB/py_reference.json", {str(r["q"]): r for r in recs},
                  script="code/python/langlandscape/hacs_bridge/laneB/py_reference.py", params={"qmax": qmax, "nproc": npr, "HMAX_SNF": HMAX_SNF},
                  runtime_s=t.seconds,
                  notes="Eisenstein module = L/(Ze+L_cusp), pairing sum f g/|Gamma_x|; expected Z/num((q-1)/12) (cited Mazur 1977/Gross 1987). "
                        "Times are wall times with up to nproc concurrent jobs (contended).")
