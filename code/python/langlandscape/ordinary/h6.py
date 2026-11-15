# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C3 (H6): the literal ``U'_p`` breaks Hida (d); ``U_p^* = <p>_M U'_p`` and ``e != e*`` (cross-check of Lean WP L5).

Cases ``(D, M)``: ``(2, 7)`` (the C3a case, ``M`` nontrivial so ``<p>_M != 1``) and ``(3, 1)``; ``p = 5``, mod ``5^3``, ``s = 1, 2``.
(1) failure witness: ``pi_* U_p = U_p pi_*`` (``pi_* : Z[X_2] -> Z[X_1]``) but ``pi_* U'_p != U'_p pi_*`` (integer matrices),
    and for the ordinary projector ``e'`` of ``U'_p``: ``pi_* e'_2 != e'_1 pi_*`` and ``(1 - e'_1) pi_* e'_2 != 0`` mod ``5^3``
    (``pi_*`` does not map ``e' Z[X_2]`` into ``e' Z[X_1]``), whereas ``pi_* e_2 = e_1 pi_*``.
(2) adjoint identity with the sign of ``results/s04/H6_sign.json`` (``+1``): ``U_p^T = <p>_M U'_p`` exactly (integers) and mod ``5^3``
    on ``S_1, S_2`` (the other sign is recorded); ``<p>_M`` nontrivial for ``M = 7``.
(3) ``e = e_{U_p}`` vs ``e* = e_{U_p^T} = e^T``: ``e != e*`` on ``S_1, S_2`` (``(2,7)``), ``rk`` equal, pairing ``e x e*`` perfect mod 5.
Run: ``cd code/python && python -m langlandscape.ordinary.h6`` -> ``code/results/s04/H6.json``.
"""

from __future__ import annotations

import json

import numpy as np

from .. import results
from . import proj, tower as tw

P, MM = 5, 3
Q = P**MM
CASES = [(2, 7), (3, 1)]


def _ne(A, B):
    return bool(((A - B) % Q != 0).any())


def case(D: int, M: int, sign: str, smax: int = 2) -> dict:
    T = tw.tower(D, P, M)
    out = {"D": D, "M": M}
    for s in range(1, smax + 1):
        n = len(T.X(s))
        U, Up, Dp = T.Up(s), T.Up_prime(s), T.p_M(s)
        assert (U.sum(axis=0) == P).all() and (Up.sum(axis=0) == P).all()
        Dpow = Dp if sign == "+1" else proj.inv(Dp, P, MM)
        Dother = proj.inv(Dp, P, MM) if sign == "+1" else Dp
        adj_exact = bool((U.T == Dpow @ Up).all())
        adj_mod = not _ne(U.T, proj.mul(Dpow, Up, Q))
        adj_other_mod = not _ne(U.T, proj.mul(Dother, Up, Q))
        Pe = proj.ordinary_projector(U, P, MM)
        Ps = proj.ordinary_projector(U.T.copy(), P, MM)
        Pp = proj.ordinary_projector(Up, P, MM)
        G = proj.mul(Pe.basis.T.copy(), Ps.basis, Q)
        d = {"n": n, "p_M_trivial": bool((Dp == np.eye(n, dtype=np.int64)).all()),
             "adjoint_identity_exact_integer": adj_exact, "adjoint_identity_mod_5^3": adj_mod,
             "adjoint_other_sign_mod_5^3": adj_other_mod,
             "rk_e": Pe.rank, "rk_e_star": Ps.rank, "rk_e_prime": Pp.rank,
             "e_star_eq_e_transpose": not _ne(Ps.e, Pe.e.T), "e_ne_e_star": _ne(Pe.e, Ps.e),
             "pairing_e_estar_gram_invertible_mod_5": bool(proj.is_invertible_mod_p(G, P)) if Pe.rank else True}
        if s == 1:
            pi = T.pi_push(1)
            n2 = len(T.X(2))
            U2, Up2 = T.Up(2), T.Up_prime(2)
            Pe2 = proj.ordinary_projector(U2, P, MM)
            Pp2 = proj.ordinary_projector(Up2, P, MM)
            piU = (pi @ U2 == U @ pi).all()
            piUp = (pi @ Up2 == Up @ pi).all()
            I1 = np.eye(n, dtype=np.int64)
            d["hida_d_s1_to_s2"] = {
                "pi_Up_equals_Up_pi_integer": bool(piU), "pi_Uprime_equals_Uprime_pi_integer": bool(piUp),
                "pi_e_equals_e_pi_mod_5^3": not _ne(proj.mul(pi, Pe2.e, Q), proj.mul(Pe.e, pi, Q)),
                "pi_eprime_equals_eprime_pi_mod_5^3": not _ne(proj.mul(pi, Pp2.e, Q), proj.mul(Pp.e, pi, Q)),
                "(1-e')_1_pi_e'_2_nonzero_mod_5^3 (info: pi_* e'X2 lands in e'X1 even though pi_* e' != e' pi_*)": _ne(proj.mul((I1 - Pp.e) % Q, proj.mul(pi, Pp2.e, Q), Q), 0 * pi[:, :1].repeat(n2, 1)),
                "(1-e)_1_pi_e_2_zero_mod_5^3 (pi_* e X2 in e X1)": not _ne(proj.mul((I1 - Pe.e) % Q, proj.mul(pi, Pe2.e, Q), Q), 0 * pi[:, :1].repeat(n2, 1)),
                "rk_e_X2": Pe2.rank, "rk_eprime_X2": Pp2.rank,
                "failure_witnessed": (not piUp) and bool(piU)}
        out[f"s{s}"] = d
    return out


def run(write: bool = True, smax: int = 2) -> dict:
    sign = json.load(open(results.repo_root() / "code/results/s04/H6_sign.json"))["data"]["sign"]
    with results.Timer() as tm:
        data = {"sign_from_C3a": sign, "cases": [case(D, M, sign, smax) for D, M in CASES]}
        c0 = data["cases"][0]
        data["checks"] = {
            "failure_witnessed": all(c["s1"]["hida_d_s1_to_s2"]["failure_witnessed"] for c in data["cases"]),
            "adjoint_identity_exact_mod_5^3": all(c[f"s{s}"]["adjoint_identity_mod_5^3"] and c[f"s{s}"]["adjoint_identity_exact_integer"]
                                                  for c in data["cases"] for s in range(1, smax + 1)),
            "e_ne_e_star_D2_M7": all(c0[f"s{s}"]["e_ne_e_star"] for s in range(1, smax + 1)),
            "e_ne_e_star_by_case": {f"D{c['D']}M{c['M']}": [c[f"s{s}"]["e_ne_e_star"] for s in range(1, smax + 1)] for c in data["cases"]},
        }
    if write:
        results.write("s04/H6.json", data, script="code/python/langlandscape/ordinary/h6.py (cd code/python && python -m langlandscape.ordinary.h6)",
                      params={"cases": CASES, "p": P, "m": MM, "s": [1, 2], "sign": sign}, runtime_s=round(tm.seconds, 2),
                      notes="S04-C3: H6; literal U'_p breaks Hida (d) with pi_*; U_p^* = <p>_M U'_p")
    return data


if __name__ == "__main__":
    print(json.dumps(run()["checks"], indent=1))
