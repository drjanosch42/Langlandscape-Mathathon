# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C3: T4, Hecke side.  ``T(1)_m`` at ``p = 17``, weights ``k in {12, 28, 44, 60, 124}``, ``q = 3``.

Tex: ``plan/staged/stage-06-integral-defect.tex`` (T4), ``prop:s06-betti`` (a): ``coker(Psi^*Psi)_m = (T(1)_m/delta)^2`` with
``delta = (q+1)^2 - q^{2-k} T_q^2``, and ``cor:s06-allweights`` (``ord eta - ord eta_new = t_{G_k}(q)``).  Normalised
integrally: ``delta_int = q^{k-2} (q+1)^2 - T_q^2 = q^{k-2} delta`` (``q`` a unit at ``p``, same ideal in ``T_m``).

``m`` is the maximal ideal of the level-1 weight-``k`` Hecke algebra through ``Delta mod 17``
(``T_l = tau(l) mod 17`` for the generators, ``T_17 = tau(17)``, a unit: ``m`` is ordinary, so no further projector is needed).
Status: every number is *computed*.  The prediction ``ord_17 c_3 = 1,1,1,1,2`` is the seed's; for ``k >= 17`` it is \\stexp.

``t_{G_k}(3)`` independently (Galois side): for each Galois orbit of eigenforms of ``S_k(SL_2(Z))`` (PARI ``mf``, not the
integral Hecke matrices of :mod:`.hecke_alg`) and each prime ``P | 17`` of its coefficient field congruent to ``Delta``,
``ord_P(a_3^2 - 3^{k-2} 16)``.  Here ``a_3^2 - 3^{k-2}(q+1)^2`` is the old-branch Tamagawa expression of the seed.
"""

from __future__ import annotations

from ..pari import get_pari
from . import hecke_alg as ha
from .hecke_alg import HeckeAlgebra, find_maximal_ideal, local_length, mf_integral_hecke

P_PRIME, Q = 17, 3
WEIGHTS = (12, 28, 44, 60, 124)
PREDICTION = {12: 1, 28: 1, 44: 1, 60: 1, 124: 2}
TAU = {2: -24, 3: 252, 5: 4830, 7: -16744}      # Ramanujan tau (classical values)


def hecke_side(k: int, p: int = P_PRIME, q: int = Q) -> dict:
    """``T(1)`` at weight ``k``, ``m`` through ``Delta mod p``, ``length_{Z_p} T_m/(delta_int)``."""
    gens = sorted(set(ha.hecke_generators(1, k) + [q, p]))
    mats, _ = mf_integral_hecke(1, k, gens, 1)
    T = HeckeAlgebra(mats)
    eig = {f"T{l}": TAU[l] % p for l in gens if l in TAU}
    eig[f"T{p}"] = _tau_mod(p, p)
    m = find_maximal_ideal(T, p, eig)
    x = T.gen(f"T{q}")
    delta = T.sub(T.scalar(q ** (k - 2) * (q + 1) ** 2), T.mul(x, x))
    ln = local_length(T.whole(), T.ideal([delta]), m)
    return {"k": k, "dim_T": T.d, "generators": gens, "m_values": {g: int(v) for g, v in m.values.items()},
            "local_rank": m.local_rank, "residue_degree": m.residue_degree, "length": ln,
            "ord_p_T_p_unit": m.values.get(f"T{p}") not in (0, None)}


def _tau_mod(n: int, p: int) -> int:
    """``tau(n) mod p`` from PARI (``mfcoefs(Delta, n)``)."""
    P = get_pari()
    return int(P(f"mfcoefs(mfDelta(), {n})[{n} + 1]")) % p


def galois_side(k: int, p: int = P_PRIME, q: int = Q) -> dict:
    """``t_{G_k}(q)``: ``ord_P(a_q^2 - q^{k-2}(q+1)^2)`` at the primes ``P | p`` of the eigenform fields congruent to Delta.

    Independent of the integral Hecke matrices (PARI ``mfeigenbasis``, ``nfinit``, ``idealprimedec``).  Returns the
    per-place valuations (``ord_P``, normalised by the uniformiser of ``K_P``) and ``length = sum f_P ord_P`` (the
    ``Z_p``-length of the corresponding quotient of ``prod O_P``).
    """
    P = get_pari()
    P(f"mf_ = mfinit([1, {k}], 1)")
    P("B_ = mfeigenbasis(mf_); FL_ = mffields(mf_)")
    n = int(P("#B_"))
    ls = [l for l in (2, 3, 5, 7) if l != p]
    places = []
    for i in range(1, n + 1):
        P(f"pol_ = FL_[{i}]; nf_ = nfinit([pol_, [{p}]]); pr_ = idealprimedec(nf_, {p}); c_ = mfcoefs(B_[{i}], 7)")
        npr = int(P("#pr_"))
        for j in range(1, npr + 1):
            cond = " && ".join(f"nfeltval(nf_, lift(c_[{l}+1]) - ({TAU[l]}), pr_[{j}]) >= 1" for l in ls)
            if int(P(f"if({cond}, 1, 0)")) != 1:
                continue
            a = f"lift(c_[{q}+1])"
            expr = f"{a}^2 - {q}^{k - 2}*{(q + 1) ** 2}"
            v = int(P(f"nfeltval(nf_, {expr}, pr_[{j}])")) if int(P(f"{expr} != 0")) else None
            places.append({"orbit": i, "orbit_degree": int(P("poldegree(pol_)")), "poly": str(P("pol_")),
                           "e": int(P(f"pr_[{j}].e")), "f": int(P(f"pr_[{j}].f")), "ord": v})
    return {"k": k, "places": places,
            "t": [pl["ord"] for pl in places],
            "length": sum(pl["f"] * pl["ord"] for pl in places)}


def row(k: int) -> dict:
    h, g = hecke_side(k), galois_side(k)
    return {**h, "t_Gk_3": g, "prediction": PREDICTION.get(k),
            "length_equals_prediction": h["length"] == PREDICTION.get(k),
            "length_equals_t_Gk": h["length"] == g["length"]}


def main() -> None:  # pragma: no cover - script entry point
    """Write ``code/results/s06/T4_hecke.json``."""
    from .. import results
    with results.Timer() as tm:
        rows = [row(k) for k in WEIGHTS]
    path = results.write("s06/T4_hecke.json", rows, script="code/python/langlandscape/defect/t4_hecke.py",
                         params={"p": P_PRIME, "q": Q, "k": list(WEIGHTS), "prediction": PREDICTION,
                                 "delta": "q^(k-2)(q+1)^2 - T_q^2"},
                         runtime_s=round(tm.seconds, 3),
                         notes="S06-C3 T4 Hecke side, all computed; prediction ord=1,1,1,1,2 recorded (\\stexp for k>=17), not gating")
    print(path)


if __name__ == "__main__":  # pragma: no cover
    main()
