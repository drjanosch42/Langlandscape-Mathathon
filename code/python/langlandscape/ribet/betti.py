# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C5: Betti-side check of ``prop:s03-PsiPsi`` / ``def:s03-LR`` with PARI ``mf`` (no HACS).

Normalisation (authority: ``mathematics/chapters/s03/5-amalgam.tex``, ``prop:s03-PsiPsi``, table of
stage-03.md section 0.2.8, confirmed by WP M5), ``V = Sym^{k-2}``, ``T_q`` the classical integral operator::

    Psi^* Psi = [[ q+1 ,  -q^{2-k} T_q ],
                 [ -T_q ,  q+1         ]]            det = (q+1)^2 - q^{2-k} T_q^2.

(The seed's matrix ``[[q+1,-T_q],[-q^{2-k}T_q,q+1]]`` swaps the two off-diagonal entries; same det.)

For each ``(M, q, k)`` on the grid (``q`` prime, ``q`` not dividing ``M``, ``k`` even, ``S_k(Gamma_0(M)) != 0``)
we take ``P(x) = charpoly(T_q | S_k(Gamma_0(M)))`` (full cuspidal space, old + new, ``mfheckemat``) and record

* ``Dint(lam) := q^{k-2} * det = q^{k-2}(q+1)^2 - lam^2`` (an algebraic integer for every eigenvalue);
  det itself is ``q^{2-k} * Dint``.
* the charpoly-level norm ``R = prod_lam Dint(lam) = (-1)^d P(s) P(-s)``, ``s = (q+1) q^{(k-2)/2}`` (an integer, ``k`` even).
  ``R = 0`` iff det vanishes on some eigenvector ("vanishing"); by Deligne ``|lam| <= 2 q^{(k-1)/2} < s``
  so ``R != 0`` always.
* ``level_raising_primes`` = primes ``l`` dividing ``R`` (``l`` not dividing ``q``-unit issues aside, ``q`` is a unit
  in ``Z_(l)`` for ``l != q``): these are the primes where ``det`` can be non-invertible, i.e. the primes of
  ``def:s03-LR``.  ``q | R`` is recorded separately (``level_raising_primes_equal_q``): ``q`` is a unit
  in ``det = q^(2-k) Dint`` only up to that power, and ``l = q`` is not a level-raising prime in the sense of the tex.

Petersson cross-check (:func:`petersson_check`): for rational newforms ``f`` of level ``M`` we compute
``<f|B_q, f>/<f,f>`` and ``<f|B_q, f|B_q>/<f,f>`` at level ``Mq`` with ``mfpetersson`` (``B_q f(z) = f(qz)``);
classically these are ``lam q^{1-k}/(q+1)`` and ``q^{-k}``.  This confirms the *size* ``q^{1-k}`` of the
off-diagonal Gram coefficient (consistent with the exponent ``2-k`` after the factor ``q`` coming from
``c`` of determinant ``q``), but not *which of the two slots* ``(1,2)``/``(2,1)`` carries ``q^{2-k}``
(that depends on the coefficient-system / ordering convention, ``rem`` in the tex): the slot assignment is
therefore flagged ``untested by PARI``.
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction

from langlandscape import results
from langlandscape.pari import get_pari

SCRIPT = "code/python/langlandscape/ribet/betti.py"
LEVELS = (1, 2, 3, 5, 7, 11)
Q_MAX = 13
WEIGHTS = (2, 4, 6, 8, 10, 12)
PETERSSON_CASES = ((11, 2, 2), (11, 2, 3), (5, 4, 2), (5, 4, 3), (1, 12, 2), (1, 12, 3), (7, 4, 2))

#: the normalisation table (tex / M5 / stage-03 0.2.8); entries as strings in q, k, lambda
NORMALISATION = {
    "source": "mathematics/chapters/s03/5-amalgam.tex prop:s03-PsiPsi; plan/implementation/stage-03.md 0.2.8",
    "matrix": [["q+1", "-q^(2-k)*lambda"], ["-lambda", "q+1"]],
    "entries": {"(1,1)": "q+1", "(1,2)": "-q^(2-k)*lambda", "(2,1)": "-lambda", "(2,2)": "q+1"},
    "det": "(q+1)^2 - q^(2-k)*lambda^2",
    "q_2_minus_k_slot": "(1,2)",
    "seed_matrix_not_used": [["q+1", "-lambda"], ["-q^(2-k)*lambda", "q+1"]],
    "off_diagonal_assignment": "untested by PARI",
}


def primes_upto(n: int) -> list[int]:
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def _factor_primes(n: int) -> list[int]:
    pari = get_pari()
    if n in (0, 1, -1):
        return []
    m = pari.factorint(abs(n))
    return sorted(int(x) for x in m[0])


def case(M: int, q: int, k: int) -> dict | None:
    """Data for one ``(M, q, k)``, or ``None`` if ``S_k(Gamma_0(M)) = 0``."""
    pari = get_pari()
    mf = pari.mfinit([M, k], 1)
    d = int(pari.mfdim(mf))
    if d == 0:
        return None
    P = pari.charpoly(pari.mfheckemat(mf, q))
    coeffs = [int(c) for c in pari.Vec(P)]  # descending, leading 1
    s = (q + 1) * q ** ((k - 2) // 2)
    x = pari("x")
    Ps = int(P.subst(x, s))
    Pms = int(P.subst(x, -s))
    R = (-1) ** d * Ps * Pms
    primes = _factor_primes(R)
    return {
        "M": M, "q": q, "k": k, "dim": d,
        "charpoly_Tq": coeffs,
        "s": s,
        "norm_Dint": R,
        "norm_Dint_factorization": [[int(p), int(e)] for p, e in zip(
            pari.factorint(abs(R))[0], pari.factorint(abs(R))[1])] if R else [],
        "det_vanishes": R == 0,
        "level_raising_primes": [p for p in primes if p != q],
        "level_raising_primes_equal_q": q in primes,
        "matrix_entries": ["q+1", "-q^(2-k)*lambda", "-lambda", "q+1"],
        "det_formula": "(q+1)^2 - q^(2-k) lambda^2 = q^(2-k) * ((q^(k-2))(q+1)^2 - lambda^2)",
    }


def petersson_check(M: int, k: int, q: int) -> dict | None:
    """Gram data of ``{f, f|B_q}`` for the first rational newform ``f`` of level ``M``, weight ``k``."""
    pari = get_pari()
    mfn = pari.mfinit([M, k], 0)
    if int(pari.mfdim(mfn)) == 0:
        return None
    f = pari.mfeigenbasis(mfn)[0]
    lam = pari.mfcoef(f, q)
    if str(pari.type(lam)) != "t_INT":
        return None
    lam = int(lam)
    mf = pari.mfinit([M * q, k], 1)
    g = pari.mfbd(f, q)
    F, G = pari.mfsymbol(mf, f), pari.mfsymbol(mf, g)
    ff, fg, gg = pari.mfpetersson(F, F), pari.mfpetersson(F, G), pari.mfpetersson(G, G)
    r1, r2 = float(pari.real(fg / ff)), float(pari.real(gg / ff))
    p1 = lam * q ** (1 - k) / (q + 1)
    p2 = q ** (-k)
    return {
        "M": M, "k": k, "q": q, "lambda": lam,
        "ratio_fg_over_ff": r1, "predicted_fg_over_ff": p1,
        "ratio_gg_over_ff": r2, "predicted_gg_over_ff": p2,
        "match": abs(r1 - p1) < 1e-8 * max(1.0, abs(p1)) and abs(r2 - p2) < 1e-8 * max(1.0, abs(p2)),
        "implied_(q+1)<f|Bq,f>/<f,f>": f"{Fraction(lam) / q ** (k - 1)}",
    }


def grid() -> list[tuple[int, int, int]]:
    return [(M, q, k) for M in LEVELS for q in primes_upto(Q_MAX) if M % q for k in WEIGHTS]


def compute() -> dict:
    cases = [c for c in (case(*t) for t in grid()) if c is not None]
    pet = [c for c in (petersson_check(*t) for t in PETERSSON_CASES) if c is not None]
    vanishing = [[c["M"], c["k"], c["q"]] for c in cases if c["det_vanishes"]]
    return {
        "normalisation": NORMALISATION,
        "cases": cases,
        "vanishing_triples_M_k_q": vanishing,
        "petersson_check": pet,
        "petersson_status": (
            "ratios <f|Bq,f>/<f,f> = lam q^(1-k)/(q+1) and <f|Bq,f|Bq>/<f,f> = q^(-k) confirmed by mfpetersson "
            "on the listed cases; slot assignment of q^(2-k) in (1,2) vs (2,1) remains untested by PARI"
            if pet and all(p["match"] for p in pet) else "petersson check failed or partial; untested by PARI"
        ),
    }


def main() -> None:
    with results.Timer() as t:
        data = compute()
    path = results.write(
        "s03/betti_det.json", data, script=SCRIPT,
        params={"levels": list(LEVELS), "q_max": Q_MAX, "weights": list(WEIGHTS),
                "petersson_cases": [list(c) for c in PETERSSON_CASES]},
        runtime_s=t.seconds,
        notes="S03-C5: det(Psi*Psi) = (q+1)^2 - q^(2-k) T_q^2 on S_k(Gamma_0(M)); full normalisation table recorded.",
    )
    print(f"wrote {path}: {len(data['cases'])} cases, vanishing: {data['vanishing_triples_M_k_q']}", file=sys.stderr)


if __name__ == "__main__":
    main()
