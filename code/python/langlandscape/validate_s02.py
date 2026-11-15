"""S02-C2: validation of the tree-quotient builder (tex H02.2 (a)-(c), ``plan/staged/stage-02-tree-quotients.tex``).

For every definite ``D <= 53`` (squarefree, omega(D) odd), prime ``q <= 13`` with ``q`` not dividing ``D`` and a few levels
(``U = O^x``, ``U_0(M)``, ``U_1(N)`` with coprime level) checks on ``BG(U, q)``:

(a) connectivity (``TreeQuotient.components() == 1``);
(b) fibre sums ``sum_{e in s_j^{-1}(x)} |Gamma_x|/|Gamma_e| = q + 1`` for ``j = 0, 1`` and all ``x``;
(c) mass identity ``sum_e 1/|Gamma_e| = (q+1) sum_x 1/|Gamma_x|`` (full stabilisers, convention of ``tree.py``; same
    with the weights ``w``), at maximal level ``sum_x 1/w_x = phi(D)/12``, and ``rk H_1 = E - 2X + 1`` where
    ``rk H_1 = E - rank_Q(boundary)`` is computed independently from the boundary matrix
    ``d = (-s_{0*}, s_{1*}) : Q^E -> Q^{2X}`` (exact elimination).

Run: ``python3 -m langlandscape.validate_s02`` -> ``code/results/s02/validation.json``.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from math import gcd

from . import results, tree
from .classset import definite_D_list, euler_phi_ram

D_MAX = 53
Q_MAX = 13
PRIMES = [2, 3, 5, 7, 11, 13]


def rank_Q(rows: list[dict]) -> int:
    """Rank over Q of sparse rows ``{col: value}`` (exact Gaussian elimination)."""
    piv: dict[int, dict] = {}
    r = 0
    for row in rows:
        row = {k: Fraction(v) for k, v in row.items() if v}
        while row:
            c = min(row)
            if c not in piv:
                a = row[c]
                piv[c] = {k: v / a for k, v in row.items()}
                r += 1
                break
            a = row[c]
            for k, v in piv[c].items():
                nv = row.get(k, 0) - a * v
                if nv:
                    row[k] = nv
                else:
                    row.pop(k, None)
    return r


def boundary_rank(T) -> int:
    """Rank of ``d : Q^E -> Q^{2X}``, ``e -> -(s0 e, 0) + (s1 e, 1)`` (one sparse row per edge)."""
    return rank_Q([{T.s0[e]: -1, T.X + T.s1[e]: 1} for e in range(T.E)])


def check_case(D: int, q: int, level: tree.Level) -> dict:
    T = tree.build(D, q, level)
    X, E = T.X, T.E
    ncomp = T.components()
    conn = ncomp == 1
    fibre = True
    for s in (T.s0, T.s1):
        fib = [Fraction(0)] * X
        for e, x in enumerate(s):
            fib[x] += Fraction(T.stab_v[x], T.stab_e[e])
        fibre &= all(f == q + 1 for f in fib)
    mv = sum(Fraction(1, s) for s in T.stab_v)
    me = sum(Fraction(1, s) for s in T.stab_e)
    mass = me == (q + 1) * mv
    mass &= sum(Fraction(1, w) for w in T.w_e) == (q + 1) * sum(Fraction(1, w) for w in T.w_v)
    if level == tree.Level.max():
        mass &= sum(Fraction(1, w) for w in T.w_v) == Fraction(euler_phi_ram(D), 12)
    rk_bd = boundary_rank(T)
    h1 = E - rk_bd
    h1_ok = h1 == E - 2 * X + ncomp
    return {
        "D": D, "q": q, "level": {"N1": level.N1, "N0": level.N0}, "X": X, "E": E, "rk_H1": h1,
        "rk_boundary": rk_bd, "rk_H1_formula": E - 2 * X + 1, "connected": conn, "fibre_sums": bool(fibre),
        "mass": bool(mass), "vertex_mass": mv, "edge_mass": me, "rk_H1_ok": bool(h1_ok and h1 == E - 2 * X + 1),
        "all_pass": bool(conn and fibre and mass and h1_ok and h1 == E - 2 * X + 1),
    }


def levels_for(D: int, q: int) -> list[tree.Level]:
    """Maximal level plus up to one ``U_0(M)`` (``M`` prime) and one ``U_1(N)`` coprime to ``D q``."""
    out = [tree.Level.max()]
    ok = [p for p in PRIMES if (D * q) % p]
    if ok:
        out.append(tree.Level.U0(ok[0]))
    ok1 = [N for N in (3, 4, 5, 7) if gcd(N, D * q) == 1]
    if ok1 and D <= 23:
        out.append(tree.Level.U1(ok1[0]))
    return out


def cases(Dmax: int = D_MAX, qmax: int = Q_MAX):
    for D in definite_D_list():
        if D > Dmax:
            continue
        for q in PRIMES:
            if q <= qmax and D % q:
                for lv in levels_for(D, q):
                    yield D, q, lv


def run(Dmax: int = D_MAX, qmax: int = Q_MAX) -> list[dict]:
    rows = []
    for D, q, lv in cases(Dmax, qmax):
        rows.append(check_case(D, q, lv))
        r = rows[-1]
        print(D, q, lv, r["X"], r["E"], r["rk_H1"], "OK" if r["all_pass"] else "FAIL", file=sys.stderr, flush=True)
    return rows


def main() -> None:
    with results.Timer() as t:
        rows = run()
    results.write(
        "s02/validation.json",
        {"cases": rows, "n_cases": len(rows), "all_pass": all(r["all_pass"] for r in rows)},
        script="code/python/langlandscape/validate_s02.py",
        params={"D_max": D_MAX, "q_max": Q_MAX, "levels": "max, U0(M) first prime M coprime to Dq, U1(N) for D<=23"},
        runtime_s=t.seconds,
        notes="S02-C2: H02.2 (a)-(c) on BG(U,q); rk H_1 independently from rank_Q of the boundary matrix.",
    )


if __name__ == "__main__":
    main()
