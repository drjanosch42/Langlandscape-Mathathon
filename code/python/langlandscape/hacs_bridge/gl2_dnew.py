# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-A1: the GL2 side of the Jacquet-Langlands oracle, computed with HACS.

For a level N = D*M (squarefree) and a weight k (even) this module obtains, from the HACS integral descent
``descent(N, k-2, P)``, the exact characteristic polynomials of T_p (p in P, p not dividing N) on
H^1(Gamma_0(N); Sym^{k-2} Z^2)/tors, and extracts from them

* the cuspidal charpoly  chi_cusp  of T_p on S_k(Gamma_0(N)):
      chi_H1 = chi_cusp^2 * (x - (1+p^{k-1}))^c,   c = #cusps = 2^omega(N)  (minus 1 if k = 2),
* the N-new charpoly (exactly new at level N): with S_k(N) = sum_{d | N} sigma_0(N/d) S_k^new(d) (N squarefree),
      chi_cusp(N) = prod_{d | N} chi_new(d)^{sigma_0(N/d)},
  every lower level being computed from HACS as well, exact divisibility asserted at each step,
* for D prime (M = 1) the U_D eigenvalue a_D = +-D^{k/2-1} on every D-new Galois orbit, from ``level_n(D, k-2, ell, [D])``
  (charpoly of U_D on H^1(Gamma_0(D); Sym^{k-2} F_ell)) for several primes ell.

Conventions: classical normalisation (a_p, no p^{k/2-1} rescaling); polynomials are stored **constant term first**
(as in code/results/s01/symn.json), HACS ``descent`` returns them high -> low; a_D = +D^{k/2-1} is "+" (this is the sign
of ``Pi_D`` in pi_sign.json: a_D = +lambda(Pi_D)).

HACS facts used (verified in the HJ-A1 session): ``level_n`` needs coefficient_ring != Z, so descent and level_n run in
separate scripts; U_D is returned only as a charpoly, so signs are attached to Galois orbits (irreducible factors of the
T_p charpoly), see :func:`assign_signs`.

* the D-new charpoly at level N = D*M: the forms of level d*D (d | M) with multiplicity sigma_0(M/d),
      chi_Dnew(D, M) = prod_{d | M} chi_new(dD)^{sigma_0(M/d)}     (= chi_new(D) for M = 1).

HACS 0.2.1 pitfall (plan/hacs/REPORT.md section 6): Eisenstein eigenvalues are twisted at levels divisible by 9 or 16;
this module therefore refuses non-squarefree N.

Cost gates. ``descent`` (psi(N)(n+1) <= 300, Console/Bindings/Descent.cpp) and ``level_n`` (psi(N)(n+1) <= 1000) have a
*silent envelope*, not a hard bound: outside it the confirmation policy of Console/Core/Confirm.h decides, and a script
with ``set confirm = "yes";`` runs the call.  The only hard refusal is memory (estimated peak RSS above min(session cap,
80 % of MemAvailable)).  Every script of this module sets ``confirm = "yes"``; the caller's own caps (rule 19: predicted
RSS / wall from the measured model ``RULE19_MODEL``, an RSS watchdog that kills a child above ``--rss-cap-gib``, the
wall budget) decide which extended cells run.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import itertools
import json
import math
import os
import pathlib
import resource
import signal
import sys
import threading
import time
from typing import Iterable

import flint
import sympy

from . import runner

X = flint.fmpz_poly([0, 1])
RESULT_REL = "code/results/s05/gl2_dnew.json"
HEAVY_LOCK = "/home/janosch/data/hacs-run/laneA/heavy.lock"
SMALL_PRIMES = [2, 3, 5, 7, 11, 13]
CONFIRM_YES = 'set confirm = "yes";\n'   # run outside the silent envelope (Confirm.h); memory stays a hard refusal


# ------------------------------------------------------------------------------------------------------------------
# pure arithmetic
# ------------------------------------------------------------------------------------------------------------------

def primes_upto(n: int) -> list[int]:
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def factorint(n: int) -> dict[int, int]:
    return {int(p): int(e) for p, e in sympy.factorint(n).items()}


def divisors(n: int) -> list[int]:
    return sorted(int(d) for d in sympy.divisors(n))


def sigma0(n: int) -> int:
    return len(divisors(n))


def is_squarefree(n: int) -> bool:
    return all(e == 1 for e in factorint(n).values())


def psi(N: int) -> int:
    r = N
    for p in factorint(N):
        r = r * (p + 1) // p
    return r


def n_cusps(N: int) -> int:
    return sum(int(sympy.totient(math.gcd(d, N // d))) for d in divisors(N))


def dim_cusp_forms(N: int, k: int):
    """dim S_k(Gamma_0(N)) (trivial character, k >= 2 even; 0 for k odd), Cohen-Oesterle formula."""
    from fractions import Fraction
    if k % 2:
        return 0
    if k == 2 and N == 1:
        return 0
    f = factorint(N)
    nu2 = 0 if N % 4 == 0 else math.prod(1 + (0 if p == 2 else (1 if p % 4 == 1 else -1)) for p in f)
    nu3 = 0 if N % 9 == 0 else math.prod(1 + (0 if p == 3 else (1 if p % 3 == 1 else -1)) for p in f)
    g4 = {0: Fraction(1, 4), 2: Fraction(-1, 4)}[k % 4]
    g3 = {0: Fraction(1, 3), 1: Fraction(0), 2: Fraction(-1, 3)}[k % 3]
    d = Fraction(k - 1, 12) * psi(N) + g4 * nu2 + g3 * nu3 - Fraction(n_cusps(N), 2)
    if k == 2:
        d += 1
    assert d.denominator == 1 and d >= 0, (N, k, d)
    return int(d)


def dim_new(N: int, k: int) -> int:
    """dim S_k(Gamma_0(N))^new by Moebius-type inversion: beta(p) = -2, beta(p^2) = 1."""
    tot = 0
    for d in divisors(N):
        m = N // d
        fm = factorint(m)
        if any(e > 2 for e in fm.values()):
            continue
        b = math.prod(-2 if e == 1 else 1 for e in fm.values())
        tot += b * dim_cusp_forms(d, k)
    return tot


def dim_H1(N: int, k: int) -> int:
    """rank of H^1(Gamma_0(N); Sym^{k-2}) for k even >= 2: 2 dim S_k + (#cusps, minus 1 if k = 2)."""
    return 2 * dim_cusp_forms(N, k) + n_cusps(N) - (1 if k == 2 else 0)


def poly_from_high(coeffs: Iterable) -> flint.fmpz_poly:
    return flint.fmpz_poly([int(c) for c in reversed(list(coeffs))])


def poly_list(P: flint.fmpz_poly) -> list[int]:
    return [int(c) for c in P.coeffs()]


def exact_div(A: flint.fmpz_poly, B: flint.fmpz_poly, what: str) -> flint.fmpz_poly:
    q, r = divmod(A, B)
    assert r == 0, f"exact divisibility failed: {what}"
    return q


def eis_poly(N: int, k: int, p: int) -> flint.fmpz_poly:
    c = n_cusps(N) - (1 if k == 2 else 0)
    return (X - (1 + p ** (k - 1))) ** c


def cusp_from_h1(H1: flint.fmpz_poly, N: int, k: int, p: int) -> flint.fmpz_poly:
    """chi_H1 = chi_cusp^2 * Eis  ->  chi_cusp; exact, every irreducible multiplicity of the quotient must be even."""
    Q = exact_div(H1, eis_poly(N, k, p), f"Eisenstein factor at N={N}, k={k}, p={p}")
    content, facs = Q.factor()
    assert content == 1, "leading constant of the H^1 charpoly is not 1"
    res = flint.fmpz_poly([1])
    for f, m in facs:
        assert m % 2 == 0, f"H^1/Eis is not a square (N={N}, k={k}, p={p})"
        res = res * f ** (m // 2)
    return res


def remove_old(cusp_N: flint.fmpz_poly, N: int, new_lower: dict[int, flint.fmpz_poly]) -> flint.fmpz_poly:
    """chi_new(N) = chi_cusp(N) / prod_{d | N, d < N} chi_new(d)^{sigma_0(N/d)}  (N squarefree), exact."""
    old = flint.fmpz_poly([1])
    for d, P in new_lower.items():
        assert N % d == 0 and d < N
        old = old * P ** sigma0(N // d)
    return exact_div(cusp_N, old, f"old part at N={N}")


def dnew_from_new(D: int, M: int, new_at: dict[int, flint.fmpz_poly]) -> flint.fmpz_poly:
    """D-new charpoly at level D*M (squarefree): prod_{d | M} chi_new(d*D)^{sigma_0(M/d)}.

    S_k(Gamma_0(DM)) = sum_{e | DM} sigma_0(DM/e) S_k^new(e); the D-new part keeps the e divisible by D, i.e. e = dD with
    d | M, with multiplicity sigma_0(DM/(dD)) = sigma_0(M/d).  ``new_at[e]`` = chi_new(e).  M = 1: chi_new(D)."""
    assert math.gcd(D, M) == 1 and is_squarefree(D * M)
    out = flint.fmpz_poly([1])
    for d in divisors(M):
        out = out * new_at[d * D] ** sigma0(M // d)
    return out


def dim_dnew(D: int, M: int, k: int) -> int:
    """dim of the D-new part of S_k(Gamma_0(DM)) = sum_{d | M} sigma_0(M/d) dim S_k^new(dD)."""
    return sum(sigma0(M // d) * dim_new(d * D, k) for d in divisors(M))


def ramanujan_ok(P: flint.fmpz_poly, p: int, k: int) -> bool:
    """All roots of P real with |root| <= 2 p^{(k-1)/2}: exact Sturm count on R(y) = P(x)P(-x), y = x^2, in [0, 4p^{k-1}]."""
    if P.degree() <= 0:
        return True
    cs = P.coeffs()
    neg = flint.fmpz_poly([c if i % 2 == 0 else -c for i, c in enumerate(cs)])
    Rx = P * neg                      # even polynomial in x
    ry = flint.fmpz_poly(Rx.coeffs()[::2])
    f = sympy.Poly([int(c) for c in reversed(ry.coeffs())], sympy.Symbol("y")).sqf_part()
    # count the distinct roots in [0, 4 p^{k-1}] and compare with all distinct roots
    n_in = f.count_roots(0, 4 * p ** (k - 1))
    return n_in == f.degree()


# ------------------------------------------------------------------------------------------------------------------
# sign assignment from charpolys only
# ------------------------------------------------------------------------------------------------------------------

def assign_signs(P: flint.fmpz_poly, n_plus: int, n_minus: int, cap: int = 2):
    """Distribute the sign counts (n_plus, n_minus) of U_D over the irreducible factors of P.

    The sign of U_D is constant on a Galois orbit of newforms; a factor F of the T_p charpoly with multiplicity m is a
    union of orbits, of which j_F carry '+'.  Returns (status, factors) with factors = [(F, deg, mult, n_plus, n_minus)];
    status: 'constant' (one sign only), 'unique' (the subset-sum has one solution), 'ambiguous' (several; ``factors``
    then holds the first solution and the count is capped by ``cap``), 'inconsistent' (none).
    """
    content, facs = P.factor()
    fl = [(f, f.degree(), m) for f, m in facs]
    deg = sum(d * m for _, d, m in fl)
    assert deg == n_plus + n_minus, (deg, n_plus, n_minus)
    if n_minus == 0 or n_plus == 0:
        sgn = (1, 0) if n_minus == 0 else (0, 1)
        return "constant", [(f, d, m, m * sgn[0], m * sgn[1]) for f, d, m in fl]
    sols: list[tuple[int, ...]] = []

    def rec(i: int, rem: int, cur: tuple[int, ...]):
        if len(sols) >= cap:
            return
        if i == len(fl):
            if rem == 0:
                sols.append(cur)
            return
        _, d, m = fl[i]
        for j in range(m + 1):
            if j * d <= rem:
                rec(i + 1, rem - j * d, cur + (j,))

    rec(0, n_plus, ())
    if not sols:
        return "inconsistent", []
    s = sols[0]
    out = [(f, d, m, j, m - j) for (f, d, m), j in zip(fl, s)]
    return ("unique" if len(sols) == 1 else "ambiguous"), out


def u_d_split(cp_ell: list[int], ell: int, D: int, k: int, t1: flint.fmpz_poly):
    """Split the mod-ell charpoly of U_D on H^1(Gamma_0(D); Sym^{k-2}) into known part and (x-s)^a (x+s)^b.

    Known part: Eisenstein (x-1)[(x-D^{k-1}) if k>2] times, for k > 2, prod_f (x^2 - lam_f x + D^{k-1})^2 over the
    level-1 eigenforms (chi_1 = charpoly of T_D at level 1).  Returns (a, b) = (mult of +s, mult of -s) in H^1, i.e.
    twice the number of D-new forms with a_D = +-s.  Raises AssertionError on any inconsistency.
    """
    s = D ** (k // 2 - 1)
    cp = flint.nmod_poly(cp_ell, ell)
    x = flint.nmod_poly([0, 1], ell)
    known = (x - 1) if k == 2 else (x - 1) * (x - D ** (k - 1))
    if k > 2:
        lam, y = sympy.symbols("lam y")
        g = sympy.resultant(sympy.Poly(poly_list(t1)[::-1], lam).as_expr(), y ** 2 - lam * y + D ** (k - 1), lam)
        old = flint.fmpz_poly([int(c) for c in reversed(sympy.Poly(g, y).all_coeffs())])
        known = known * flint.nmod_poly(poly_list(old * old), ell)
    R, rem = divmod(cp, known)
    assert rem == 0, f"U_D charpoly: known (Eisenstein + old) part does not divide (D={D}, k={k}, ell={ell})"
    a = 0
    while R(s % ell) == 0 and R.degree() > 0:
        R = R // (x - s)
        a += 1
    b = 0
    while R.degree() > 0 and R(-s % ell) == 0:
        R = R // (x + s)
        b += 1
    assert R.degree() == 0, f"U_D has an eigenvalue outside +-{s} mod {ell}"
    return a, b


# ------------------------------------------------------------------------------------------------------------------
# rule 19: RSS watchdog, call log, cost model
# ------------------------------------------------------------------------------------------------------------------

class RssCapExceeded(RuntimeError):
    """A HACS child was killed by the watchdog above the RSS cap."""


class RssWatchdog:
    """Polls the children of this process (``/proc/<pid>/stat`` ppid) and SIGKILLs any whose VmRSS exceeds ``cap_bytes``.

    Also tracks the per-pid peak (VmHWM) so every HACS call reports its own peak RSS."""

    def __init__(self, cap_bytes: int, interval: float = 0.05):
        self.cap, self.interval = int(cap_bytes), interval
        self.killed: set[int] = set()
        self.peak: dict[int, int] = {}
        self._stop = threading.Event()
        self._th = threading.Thread(target=self._loop, daemon=True)

    def __enter__(self):
        self._th.start()
        return self

    def __exit__(self, *exc):
        self._stop.set()
        self._th.join()

    @staticmethod
    def _children(me: int) -> list[int]:
        out = []
        for e in os.scandir("/proc"):
            if not e.name.isdigit():
                continue
            try:
                with open(f"/proc/{e.name}/stat") as fh:
                    st = fh.read()
            except OSError:
                continue
            if int(st[st.rindex(")") + 2:].split()[1]) == me:
                out.append(int(e.name))
        return out

    @staticmethod
    def _status(pid: int) -> tuple[int, int]:
        rss = hwm = 0
        try:
            with open(f"/proc/{pid}/status") as fh:
                for line in fh:
                    if line.startswith("VmRSS:"):
                        rss = int(line.split()[1]) * 1024
                    elif line.startswith("VmHWM:"):
                        hwm = int(line.split()[1]) * 1024
        except OSError:
            pass
        return rss, hwm

    def _loop(self):
        me = os.getpid()
        while not self._stop.is_set():
            for pid in self._children(me):
                rss, hwm = self._status(pid)
                self.peak[pid] = max(self.peak.get(pid, 0), hwm, rss)
                if rss > self.cap and pid not in self.killed:
                    self.killed.add(pid)
                    with contextlib.suppress(OSError):
                        os.kill(pid, signal.SIGKILL)
            self._stop.wait(self.interval)

    def snapshot(self) -> set[int]:
        return set(self.peak) | set(self.killed)


WATCHDOG: RssWatchdog | None = None
#: one entry per HACS process: {"verb", "N", "k", "wall_s", "peak_rss_mib"}
CALL_LOG: list[dict] = []
#: per-call timeout (s) of HACS processes; the CLI sets it from the remaining wall budget
CALL_TIMEOUT: float = 3600.0
#: ENGINE_THREADS of every HACS child (shared box: <= 8)
THREADS: int = 4


def _children_maxrss() -> int:
    return resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024   # Linux: KiB


def _run_hacs(src: str, verb: str, N: int, k: int, hacs, threads: int) -> runner.ScriptResult:
    """runner.run_script with ``confirm = "yes"``, the watchdog's kill turned into RssCapExceeded, and a CALL_LOG entry."""
    before = WATCHDOG.snapshot() if WATCHDOG else set()
    ru0 = _children_maxrss()
    t = time.perf_counter()
    try:
        r = runner.run_script(CONFIRM_YES + src, hacs=hacs, threads=threads, timeout=CALL_TIMEOUT)
        err = None
    except runner.HacsScriptError as e:
        r, err = None, e
    wall = time.perf_counter() - t
    new = (WATCHDOG.snapshot() - before) if WATCHDOG else set()
    peak = max((WATCHDOG.peak.get(p, 0) for p in new) if WATCHDOG else (), default=0)
    ru1 = _children_maxrss()
    if ru1 > ru0:                       # this child set a new high-water mark: exact
        peak = max(peak, ru1)
    killed = bool(WATCHDOG and new & WATCHDOG.killed)
    CALL_LOG.append({"verb": verb, "N": N, "k": k, "wall_s": round(wall, 3), "peak_rss_mib": round(peak / 2 ** 20, 1),
                     "killed": killed})
    if killed:
        raise RssCapExceeded(f"{verb}({N}, k={k}) killed above {WATCHDOG.cap / 2 ** 30:.2f} GiB RSS")
    if err is not None:
        raise err
    return r


#: rule-19 cost model of ONE cell's dominant HACS process, descent(N, k-2, 3 primes <= 13) at ENGINE_THREADS = 8:
#:   wall_s = exp(a) psi^b (k-1)^c,   peak_rss_mib = r0 + exp(ra) psi^rb (k-1)^rc,
#: least squares in logs on the 13 cells measured 2026-11-15 (``fit``; cell totals incl. lower levels and level_n,
#: max relative error 13.5 % (RSS) / 18.5 % (wall), hence ``margin``).  Validation point: (29, 20) predicted 4.2 GiB,
#: measured: killed by the watchdog above 3 GiB.  level_n (sparse, mod ell) is < 0.1 s there.
RULE19_MODEL: dict = {
    "descent_wall": {"a": -10.3261, "b": 2.2605, "c": 2.1542},
    "descent_rss": {"r0": 40.0, "ra": -7.4230, "rb": 2.1283, "rc": 2.8894},
    "margin": 1.2,
    "fit": {"measured": "D,k: peak_rss_mib, hacs_wall_s (threads 8)",
            "points": {"47,6": [268.3, 7.2], "23,12": [584.2, 6.7], "31,10": [541.5, 8.5], "41,8": [559.5, 9.4],
                       "43,8": [597.1, 11.2], "37,10": [728.1, 16.1], "17,16": [717.5, 7.9], "19,16": [945.2, 12.0],
                       "13,22": [1004.9, 9.8], "11,24": [1102.7, 8.2], "17,18": [1022.9, 9.1], "23,14": [985.3, 9.7],
                       "13,24": [1539.9, 10.1]},
            "killed": {"29,20": "> 3072 MiB (watchdog)"}},
}


def predict_descent(N: int, k: int, model: dict = RULE19_MODEL) -> tuple[float, float]:
    """(wall_s, peak_rss_mib) predicted for descent(N, k-2, P)."""
    if k == 2 and N == 1:
        return 0.0, 0.0
    w, r = model["descent_wall"], model["descent_rss"]
    ps, n1 = psi(N), k - 1
    wall = math.exp(w["a"]) * ps ** w["b"] * n1 ** w["c"]
    rss = r["r0"] + math.exp(r["ra"]) * ps ** r["rb"] * n1 ** r["rc"]
    return wall * model["margin"], rss * model["margin"]


def predict_cell(D: int, k: int, M: int = 1, done: set | None = None, model: dict = RULE19_MODEL) -> tuple[float, float]:
    """(wall_s, max peak RSS MiB) of a cell: the descents at every d | DM not in ``done`` (pairs (d, k)), plus level 1."""
    done = set() if done is None else done
    wall, rss = 0.0, 0.0
    for d in set(divisors(D * M)) | {1}:
        if (d, k) in done:
            continue
        w, r = predict_descent(d, k, model)
        wall += w
        rss = max(rss, r)
    return wall, rss


# ------------------------------------------------------------------------------------------------------------------
# HACS calls
# ------------------------------------------------------------------------------------------------------------------

def descent_charpolys(N: int, k: int, primes: list[int], hacs=None, threads: int | None = None):
    """{p: fmpz_poly chi_H1(T_p)} and the wall time of ``descent(N, k-2, primes)``."""
    src = ('set coefficient_ring = "Z";\n'
           f"d = descent({N}, {k - 2}, {json.dumps(primes)});\n"
           'print("@@STATUS " + json(d.status));\n'
           'for c in d.charpoly { print("@@CP " + json([c.p, c.exact, c.determined])); }\n')
    r = _run_hacs(src, "descent", N, k, hacs, threads or THREADS)
    assert r.tags["STATUS"][0] == "ok", r.tags["STATUS"]
    out = {}
    for p, ex, det in r.tags["CP"]:
        assert det, f"charpoly at p={p} not determined"
        out[int(p)] = poly_from_high(ex)
    assert set(out) == set(primes)
    return out, r.wall_s


def level_n_ud(D: int, k: int, ells: list[int], hacs=None, threads: int | None = None):
    """{ell: (h1, charpoly of U_D mod ell, constant term first)} and the wall time."""
    src = "".join(f'A = level_n({D}, {k - 2}, {l}, [{D}]);\n'
                  f'print("@@LN " + json([A.h1, A.ops[0].p, A.ops[0].bad, A.ops[0].charpoly]));\n' for l in ells)
    r = _run_hacs(src, "level_n", D, k, hacs, threads or THREADS)
    out = {}
    for l, (h1, p, bad, cp) in zip(ells, r.tags["LN"]):
        assert p == D and bad, "level_n op is not U_D"
        out[l] = (int(h1), [int(c) for c in cp])
    return out, r.wall_s


def ells_for(D: int, k: int, count: int) -> list[int]:
    """Primes ell > max(k, 5) (so Sym^{k-2} is semisimple over F_ell), ell != D."""
    return [p for p in primes_upto(400) if p > max(k, 5) and p != D][:count]


# ------------------------------------------------------------------------------------------------------------------
# a cell
# ------------------------------------------------------------------------------------------------------------------

def cell_primes(N: int, count: int = 3) -> list[int]:
    return [p for p in SMALL_PRIMES if N % p][:count]


def new_charpolys(N: int, k: int, primes: list[int], hacs=None, cache: dict | None = None, timing: dict | None = None):
    """{p: chi_new(N) charpoly of T_p on S_k(Gamma_0(N))^new} for squarefree N, all lower levels from HACS.

    ``cache[(d, k, p)]`` holds chi_new(d); ``timing[(d,k)]`` the HACS wall time spent at level d.
    """
    assert N >= 1 and is_squarefree(N), "N must be squarefree (HACS 0.2.1 Eisenstein pitfall at 9 | N, 16 | N)"
    assert k % 2 == 0 and k >= 2
    cache = {} if cache is None else cache
    timing = {} if timing is None else timing
    for d in divisors(N):
        need = [p for p in primes if (d, k, p) not in cache and d % p]
        if not need:
            continue
        if k == 2 and d == 1:
            for p in need:
                cache[(1, 2, p)] = flint.fmpz_poly([1])
            continue
        H1, wall = descent_charpolys(d, k, need, hacs)
        timing[(d, k)] = timing.get((d, k), 0.0) + wall
        for p in need:
            cusp = cusp_from_h1(H1[p], d, k, p)
            lower = {e: cache[(e, k, p)] for e in divisors(d) if e < d}
            new = remove_old(cusp, d, lower)
            assert new.degree() == dim_new(d, k), (d, k, p, new.degree(), dim_new(d, k))
            cache[(d, k, p)] = new
    return {p: cache[(N, k, p)] for p in primes}


def compute_cell(D: int, k: int, M: int = 1, hacs=None, cache=None, timing=None, n_ell: int = 3,
                 signs: bool = True, primes: list[int] | None = None) -> dict:
    """The record of one (D, M, k): the D-new charpolys at level N = DM, checks, and (D prime, M = 1) the U_D signs.

    ``charpoly_new`` is the D-new part (prod_{d | M} chi_new(dD)^{sigma_0(M/d)}, :func:`dnew_from_new`); for M = 1 it is
    the D-new = N-new charpoly.  For M > 1 the N-new charpoly is recorded as ``charpoly_N_new``."""
    N = D * M
    t0 = time.perf_counter()
    cache = {} if cache is None else cache
    timing = {} if timing is None else timing
    primes = primes or cell_primes(N)
    rec: dict = {"D": D, "M": M, "k": k, "N": N, "primes": primes, "dim_new_formula": dim_dnew(D, M, k)}
    if k % 2:
        rec.update(dim_new=0, charpoly_new={str(p): [1] for p in primes}, trivial="k odd: -1 acts as -1")
        rec["checks"] = {"degree_eq_dim_formula": True, "ramanujan": True}
        rec["runtime_s"] = 0.0
        return rec
    t_before = sum(timing.values())
    new_N = new_charpolys(N, k, primes, hacs, cache, timing)       # fills cache[(e, k, p)] for every e | N
    new = {p: dnew_from_new(D, M, {e: cache[(e, k, p)] for e in divisors(N)}) for p in primes}
    rec["dim_new"] = new[primes[0]].degree()
    rec["charpoly_new"] = {str(p): poly_list(P) for p, P in new.items()}
    if M > 1:
        rec["dim_N_new"] = new_N[primes[0]].degree()
        rec["charpoly_N_new"] = {str(p): poly_list(P) for p, P in new_N.items()}
    rec["checks"] = {"degree_eq_dim_formula": all(P.degree() == rec["dim_new_formula"] for P in new.values()),
                     "ramanujan": all(ramanujan_ok(P, p, k) for p, P in new.items())}
    if signs and rec["dim_new"] > 0:
        if M == 1 and sympy.isprime(D):
            rec["U_D"] = u_d_signs(D, k, new, hacs, cache, timing, n_ell)
        else:
            rec["U_D"] = None
            rec["U_D_null_reason"] = ("U_D signs are implemented for D prime, M = 1 only (one U_D on the D-new part); "
                                      f"D = {D}, M = {M}: the U_q, q | D, split is not implemented")
    rec["hacs_wall_s"] = sum(timing.values()) - t_before
    rec["runtime_s"] = time.perf_counter() - t0
    return rec


def factor_rows(status: str, facs) -> list[dict]:
    """JSON rows of :func:`assign_signs` factors; 'ambiguous' (several subset-sum solutions): the per-factor split is not
    determined, so n_plus / n_minus are null (the cell totals stay exact)."""
    amb = status == "ambiguous"
    return [{"poly": poly_list(F), "deg": d, "mult": m, "n_plus": None if amb else jp, "n_minus": None if amb else jm}
            for F, d, m, jp, jm in facs]


def u_d_signs(D: int, k: int, new: dict[int, flint.fmpz_poly], hacs, cache, timing, n_ell: int) -> dict:
    s = D ** (k // 2 - 1)
    # chi_1(T_D) at level 1 (needed for the old part of U_D); k = 2: none
    t1 = flint.fmpz_poly([1])
    if k > 2:
        if (1, k, "T", D) not in cache:
            H1, wall = descent_charpolys(1, k, [D], hacs)
            timing[(1, k)] = timing.get((1, k), 0.0) + wall
            cache[(1, k, "T", D)] = cusp_from_h1(H1[D], 1, k, D)
        t1 = cache[(1, k, "T", D)]
    # number of ell needed so that prod(ell) > 2 s (CRT range for an integer in [-s, s]), at least 2, at most n_ell
    need, prod = 0, 1
    ells_all = ells_for(D, k, 40)
    for l in ells_all:
        need += 1
        prod *= l
        if prod > 2 * s and need >= 2:
            break
    use = ells_all[:max(2, min(n_ell, need)) if n_ell else need]
    got, wall = level_n_ud(D, k, use, hacs)
    timing[(D, k, "level_n")] = wall
    dnew = new[next(iter(new))].degree()
    exp_h1 = dim_H1(D, k)
    pairs = []
    for l in use:
        h1, cp = got[l]
        assert h1 == exp_h1, f"level_n h1={h1} != 2 dim S + eis = {exp_h1} at ell={l} (torsion?)"
        pairs.append((l,) + u_d_split(cp, l, D, k, t1))
    ab = {(a, b) for _, a, b in pairs}
    assert len(ab) == 1, f"U_D sign counts differ between ell: {pairs}"
    a, b = next(iter(ab))
    assert a % 2 == 0 and b % 2 == 0 and (a + b) == 2 * dnew
    n_plus, n_minus = a // 2, b // 2
    # sign distribution on the irreducible factors of T_p (p = first prime giving a unique/constant answer)
    best = None
    for p, P in new.items():
        status, facs = assign_signs(P, n_plus, n_minus)
        if best is None or (status in ("constant", "unique") and best[1] not in ("constant", "unique")):
            best = (p, status, facs)
        if status in ("constant", "unique"):
            break
    p, status, facs = best
    prodl = math.prod(use)
    return {"s": s, "n_plus": n_plus, "n_minus": n_minus, "ells": use, "crt_modulus_gt_2s": prodl > 2 * s,
            "ell_charpoly_check": "U_D charpoly mod ell = Eis * old^2 * (x-s)^a (x+s)^b for every ell listed",
            "sign_status": status, "factor_prime": p,
            "factors": factor_rows(status, facs),
            "wall_level_n_s": wall}


# ------------------------------------------------------------------------------------------------------------------
# acceptance against the S01 records
# ------------------------------------------------------------------------------------------------------------------

def repo_root() -> pathlib.Path:
    return pathlib.Path(__file__).resolve().parents[4]


def _poly_str(c): return [str(x) for x in c]


def compare_symn(cells: dict[tuple[int, int], dict], symn: dict) -> dict:
    """RHS of symn.json: at k = 2 the RHS carries the extra Eisenstein factor (x - ell - 1)."""
    ok, total, bad, n_ell_cmp = 0, 0, [], 0
    for key, g in symn["grid"].items():
        D, k = g["D"], g["k"]
        total += 1
        rec = cells[(D, k)]
        good = True
        for ell, e in g["ell"].items():
            ell = int(ell)
            n_ell_cmp += 1
            mine = flint.fmpz_poly(rec["charpoly_new"][str(ell)])
            if k == 2:
                mine = mine * (X - ell - 1)
            if poly_list(mine) != [int(c) for c in e["rhs"]]:
                good = False
        if good:
            ok += 1
        else:
            bad.append(key)
    return {"cases": total, "ok": ok, "bad": bad, "ell_comparisons": n_ell_cmp}


def compare_pi_sign(cells: dict[tuple[int, int], dict], pis: dict) -> dict:
    """a_D = +lambda(Pi_D): '+' eigenspace charpoly_T of pi_sign.json vs the product of the '+' factors."""
    ok, total, bad, detail = 0, 0, [], {}
    for key, g in pis["grid"].items():
        D, k = g["D"], g["k"]
        total += 1
        rec = cells[(D, k)]
        mf = g["mf"]
        if g["no_newforms"] or mf["dim"] == 0:
            good = rec["dim_new"] == 0
            detail[key] = "no newforms"
        else:
            u = rec["U_D"]
            detail[key] = {"sign_status": u["sign_status"], "n_plus": u["n_plus"], "n_minus": u["n_minus"]}
            good = u["sign_status"] in ("constant", "unique") and _pi_sign_match(rec, mf)
        ok += bool(good)
        if not good:
            bad.append(key)
    return {"cases": total, "ok": ok, "bad": bad, "detail": detail}


def _pi_sign_match(rec: dict, mf: dict) -> bool:
    """Compare the '+'/'-' charpolys of T_p of pi_sign.json with the sign split of the HACS factors at the same p.

    The factor split is available at ``factor_prime``; for the other primes the split polynomial is not derivable from
    charpolys alone, so only dimensions are compared there.  When the sign is constant the full charpoly is compared at
    every prime."""
    u = rec["U_D"]
    dims_ok = (mf["eigenspaces"]["+"]["dim"] == u["n_plus"]) and (mf["eigenspaces"]["-"]["dim"] == u["n_minus"])
    ok = dims_ok
    for sg, key_n, key_s in (("+", "n_plus", 1), ("-", "n_minus", -1)):
        for p, ref in mf["eigenspaces"][sg]["charpoly_T"].items():
            ref = [int(c) for c in ref]
            if u[key_n] == 0:
                ok = False
            elif (u["n_minus"] if sg == "+" else u["n_plus"]) == 0:
                ok = ok and ref == rec["charpoly_new"][p]
            elif int(p) == u["factor_prime"]:
                F = flint.fmpz_poly([1])
                for f in u["factors"]:
                    F = F * flint.fmpz_poly(f["poly"]) ** f["n_plus" if sg == "+" else "n_minus"]
                ok = ok and poly_list(F) == ref
            else:
                # different prime: the eigenspace polynomial divides the full charpoly with the right degree
                ok = ok and len(ref) - 1 == u[key_n] and \
                    divmod(flint.fmpz_poly(rec["charpoly_new"][p]), flint.fmpz_poly(ref))[1] == 0
    return bool(ok)


# ------------------------------------------------------------------------------------------------------------------
# CLI
# ------------------------------------------------------------------------------------------------------------------

HEAVY_SH = "/home/janosch/data/hacs-run/heavy.sh"   # node-wide heavy-job semaphore (2 slots); wraps the whole command


@contextlib.contextmanager
def heavy_lock(path: str = HEAVY_LOCK):
    """Hold the lane heavy-run flock (blocking).  Not needed when the command already runs as
    ``flock <lane lock> heavy.sh <label> python -m ...`` (the box rule; do not combine with --lock then)."""
    pathlib.Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        try:
            yield True
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)


def ext_levels(Dmax: int) -> list[int]:
    """Extended-grid discriminants: squarefree D <= Dmax with omega(D) odd (primes, and e.g. 30, 42)."""
    return [D for D in range(2, Dmax + 1) if is_squarefree(D) and len(factorint(D)) % 2 == 1]


def inside_envelope(D: int, k: int, M: int = 1) -> bool:
    """Every descent of the cell inside the silent envelope psi(N)(k-1) <= 300 (descent.cpp kMaxModuleRank)."""
    return psi(D * M) * (k - 1) <= 300


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="python -m langlandscape.hacs_bridge.gl2_dnew", description=__doc__.split("\n")[0])
    ap.add_argument("--Dmax", type=int, default=50, help="extended grid: squarefree D <= Dmax with omega(D) odd")
    ap.add_argument("--kmax", type=int, default=24, help="extended grid: even k <= kmax")
    ap.add_argument("--cells", help="explicit extended cells 'D:k,D:k,...' (overrides --Dmax/--kmax)")
    ap.add_argument("--rss-cap-gib", type=float, default=3.0,
                    help="per-HACS-process RSS cap: cells predicted above it are skipped (predicted_rss), a child "
                         "exceeding it is killed by the watchdog (rss_cap)")
    ap.add_argument("--wall-budget-min", type=float, default=20.0,
                    help="total HACS wall budget of the run (all cells); extended cells that would exceed it, by the "
                         "rule-19 prediction or in fact, are skipped (budget)")
    ap.add_argument("--threads", type=int, default=8, help="ENGINE_THREADS per HACS child (<= 8 on the shared box)")
    ap.add_argument("--n-ell", type=int, default=3, help="max number of ell per U_D sign computation (0: until CRT range)")
    ap.add_argument("--no-ext", action="store_true", help="only the symn / pi_sign cells")
    ap.add_argument("--no-base", action="store_true", help="skip the symn / pi_sign cells (rule-19 measurement runs)")
    ap.add_argument("--no-signs-ext", action="store_true", help="no U_D signs on the extended-only cells")
    ap.add_argument("--predict-only", action="store_true", help="print the rule-19 prediction and stop")
    ap.add_argument("--hacs", default=None)
    ap.add_argument("--out", default=None, help=f"default <repo>/{RESULT_REL}")
    ap.add_argument("--lock", action="store_true",
                    help="hold the lane heavy-run flock (only when NOT already run under flock + heavy.sh)")
    ap.add_argument("--box-busy", action="store_true",
                    help="the node semaphore was not obtained: run no cell outside the envelope (box_busy)")
    a = ap.parse_args(argv)
    assert 1 <= a.threads <= 8
    global THREADS
    THREADS = a.threads
    if a.predict_only:
        return _run(a, True)
    cm = heavy_lock() if a.lock else contextlib.nullcontext(True)
    with cm:
        return _run(a, not a.box_busy)


def _hacs_wall() -> float:
    return sum(c["wall_s"] for c in CALL_LOG)


def _run(a, box_free: bool = True) -> int:
    global WATCHDOG, CALL_TIMEOUT
    t0 = time.perf_counter()
    root = repo_root()
    symn = json.load(open(root / "code/results/s01/symn.json"))["data"]
    pis = json.load(open(root / "code/results/s01/pi_sign.json"))["data"]
    want: dict[tuple[int, int], dict] = {}
    if not a.no_base:
        for g in symn["grid"].values():
            want[(g["D"], g["k"])] = {"origin": ["symn"], "signs": True}
        for g in pis["grid"].values():
            w = want.setdefault((g["D"], g["k"]), {"origin": [], "signs": True})
            w["origin"].append("pi_sign")
    if not a.no_ext:
        if a.cells:
            ext = [tuple(int(t) for t in c.split(":")) for c in a.cells.split(",")]
        else:
            ext = [(D, k) for D in ext_levels(a.Dmax) for k in range(2, a.kmax + 1, 2)]
        for D, k in ext:
            w = want.setdefault((D, k), {"origin": [], "signs": not a.no_signs_ext})
            w["origin"].append("ext")
    cap_mib = a.rss_cap_gib * 1024
    budget_s = a.wall_budget_min * 60
    # ---- rule 19: prediction, printed before the bulk run; cells inside the envelope first, then by predicted wall
    order = sorted(want, key=lambda c: (not inside_envelope(*c), predict_cell(*c)[0], c))
    done: set = set()
    plan, skipped, cum = [], [], 0.0
    for D, k in order:
        w, r = predict_cell(D, k, 1, done)
        entry = {"D": D, "k": k, "predicted_wall_s": round(w, 1), "predicted_rss_mib": round(r, 1)}
        heavy = not inside_envelope(D, k)
        if heavy and r > cap_mib:
            skipped.append(dict(entry, reason="predicted_rss"))
            continue
        if heavy and cum + w > budget_s:
            skipped.append(dict(entry, reason="budget"))
            continue
        if heavy and not box_free:
            skipped.append(dict(entry, reason="box_busy"))
            continue
        cum += w
        done |= {(d, k) for d in set(divisors(D)) | {1}}
        plan.append(((D, k), entry))
    big = [e for _, e in plan if not inside_envelope(e["D"], e["k"])]
    print(f"RULE19 prediction: {len(plan)} cells to run ({len(big)} outside the silent envelope), predicted HACS wall "
          f"{cum:.0f} s (budget {budget_s:.0f} s), max predicted RSS "
          f"{max([e['predicted_rss_mib'] for _, e in plan] or [0]):.0f} MiB (cap {cap_mib:.0f} MiB); skipped "
          f"{len(skipped)}: " + ", ".join(f"{s['D']}:{s['k']}({s['reason']})" for s in skipped), flush=True)
    for e in big:
        print(f"  predict D={e['D']} k={e['k']} wall={e['predicted_wall_s']}s rss={e['predicted_rss_mib']}MiB", flush=True)
    if a.predict_only:
        return 0
    cache: dict = {}
    timing: dict = {}
    cells: dict[tuple[int, int], dict] = {}
    errors = []
    with RssWatchdog(int(a.rss_cap_gib * 2 ** 30)) as wd:
        WATCHDOG = wd
        try:
            for (D, k), entry in plan:
                w = want[(D, k)]
                remaining = budget_s - _hacs_wall()
                heavy = not inside_envelope(D, k)
                if heavy and remaining < entry["predicted_wall_s"]:
                    skipped.append(dict(entry, reason="budget", hacs_wall_so_far_s=round(_hacs_wall(), 1)))
                    continue
                CALL_TIMEOUT = max(60.0, remaining) if heavy else 3600.0
                n_calls = len(CALL_LOG)
                t = time.perf_counter()
                try:
                    rec = compute_cell(D, k, 1, a.hacs, cache, timing, a.n_ell, w["signs"])
                except RssCapExceeded as e:
                    skipped.append(dict(entry, reason="rss_cap", detail=str(e), calls=CALL_LOG[n_calls:]))
                    print(f"cell D={D} k={k} SKIPPED rss_cap: {e}", flush=True)
                    continue
                except runner.HacsTimeout as e:
                    skipped.append(dict(entry, reason="budget", detail=f"timeout {e.timeout:.0f} s", calls=CALL_LOG[n_calls:]))
                    print(f"cell D={D} k={k} SKIPPED budget (timeout)", flush=True)
                    continue
                except (AssertionError, runner.HacsError) as e:
                    if not heavy:
                        raise
                    errors.append({"D": D, "k": k, "error": str(e)[:2000]})
                    print(f"cell D={D} k={k} ERROR {str(e)[:300]}", flush=True)
                    continue
                calls = CALL_LOG[n_calls:]
                rec["origin"] = w["origin"]
                rec["peak_rss_mib"] = max([c["peak_rss_mib"] for c in calls] or [0.0])
                if heavy:
                    rec["rule19"] = dict(entry, calls=calls)
                cells[(D, k)] = rec
                print(f"cell D={D} k={k} dim_new={rec['dim_new']} checks={rec['checks']} "
                      f"{time.perf_counter() - t:.1f}s peak_rss={rec['peak_rss_mib']}MiB"
                      + (f" (predicted {entry['predicted_wall_s']}s / {entry['predicted_rss_mib']}MiB)" if heavy else ""),
                      flush=True)
        finally:
            WATCHDOG = None
    base_ok = not a.no_base
    acc_symn = compare_symn(cells, symn) if base_ok else None
    acc_pi = compare_pi_sign(cells, pis) if base_ok else None
    ext_cells = [c for c in cells.values() if "ext" in c["origin"]]
    ext_ok = [c for c in ext_cells if all(c["checks"].values())]
    n_ext_total = sum("ext" in w["origin"] for w in want.values())
    sign_status: dict[str, int] = {}
    for c in cells.values():
        st = (c["U_D"] or {}).get("sign_status", "null") if "U_D" in c else "none"
        sign_status[st] = sign_status.get(st, 0) + 1
    total = time.perf_counter() - t0
    peak = max([c["peak_rss_mib"] for c in CALL_LOG] or [0.0])
    data = {
        "conventions": {
            "normalisation": "classical a_p (no p^{k/2-1} rescaling); polynomials are charpolys of T_p on the D-new part of "
                             "S_k(Gamma_0(DM)) (here M = 1: S_k(Gamma_0(D))^new), coefficient lists constant term first "
                             "(as symn.json); k odd -> [1]",
            "a_D": "a_D = U_D eigenvalue = +-D^{k/2-1}; '+' means a_D = +D^{k/2-1} = +lambda(Pi_D) (pi_sign.json)",
            "k_2": "symn.json RHS at k = 2 carries the Eisenstein factor (x-ell-1), added here for the comparison only",
            "extraction": "H^1/tors charpoly = chi_cusp^2 (x-1-p^{k-1})^c; chi_new(N) = chi_cusp(N)/prod_{d|N,d<N} chi_new(d)^sigma0(N/d); "
                          "D-new part at DM = prod_{d|M} chi_new(dD)^sigma0(M/d)",
            "signs": "charpoly of U_D only (no matrices): signs attach to Galois orbits = irreducible factors of the T_p "
                     "charpoly; sign_status says whether this determines them (constant/unique/ambiguous); for "
                     "'ambiguous' the per-factor n_plus/n_minus are null and only the cell totals are exact; composite D: "
                     "U_D = null with U_D_null_reason",
            "cost_gate": "descent psi(N)(k-1) <= 300 and level_n psi(N)(k-1) <= 1000 are HACS confirm gates (silent "
                         "envelope, Console/Core/Confirm.h), not hard bounds; every script sets confirm = \"yes\"; cells "
                         "outside are capped by this driver (rule 19 prediction, RSS watchdog, wall budget)",
        },
        "acceptance": {"symn": acc_symn, "pi_sign": acc_pi,
                       "extended": {"cells_total": n_ext_total, "cells": len(ext_cells), "ok": len(ext_ok),
                                    "skipped": skipped, "errors": errors},
                       "sign_status": sign_status},
        "rule19": {"model": RULE19_MODEL, "rss_cap_gib": a.rss_cap_gib, "wall_budget_s": budget_s,
                   "threads": THREADS, "predicted_hacs_wall_s": round(cum, 1), "actual_hacs_wall_s": round(_hacs_wall(), 1),
                   "peak_rss_mib": peak, "box_semaphore": box_free},
        "hacs_wall_s": sum(timing.values()),
        "per_level_wall_s": {",".join(map(str, k_)): round(v, 3) for k_, v in sorted(timing.items(), key=str)},
        "cells": {f"{D},{k}": c for (D, k), c in sorted(cells.items())},
        "status": "computed",
    }
    prov = runner.provenance("code/python/langlandscape/hacs_bridge/gl2_dnew.py",
                             {"Dmax": a.Dmax, "kmax": a.kmax, "cells": a.cells, "rss_cap_gib": a.rss_cap_gib,
                              "wall_budget_min": a.wall_budget_min, "threads": a.threads, "n_ell": a.n_ell,
                              "no_ext": a.no_ext, "no_base": a.no_base, "no_signs_ext": a.no_signs_ext},
                             total, a.hacs)
    out = pathlib.Path(a.out) if a.out else root / RESULT_REL
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"provenance": prov, "data": data}, indent=None, sort_keys=True, separators=(",", ":")) + "\n")
    print(f"symn {acc_symn and (acc_symn['ok'], acc_symn['cases'])}  pi_sign {acc_pi and (acc_pi['ok'], acc_pi['cases'])}  "
          f"ext {len(ext_ok)}/{len(ext_cells)} ran of {n_ext_total} (skipped {len(skipped)}, errors {len(errors)})  "
          f"signs {sign_status}  hacs {_hacs_wall():.1f}s (predicted {cum:.0f}s) total {total:.1f}s peak {peak} MiB "
          f"-> {out} ({out.stat().st_size} B)")
    good = (not base_ok or (acc_symn["ok"] == acc_symn["cases"] and acc_pi["ok"] == acc_pi["cases"]))
    return 0 if good and len(ext_ok) == len(ext_cells) and not errors else 1


if __name__ == "__main__":
    sys.exit(main())
