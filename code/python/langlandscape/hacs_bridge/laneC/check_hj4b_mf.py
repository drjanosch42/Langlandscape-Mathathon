# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-4b cross-check: native Sym^n Brandt char-polys at level U_0(M) (code/results/laneC/hj4b_level.json) against PARI.

JL at Eichler level M (gcd(M, D) = 1, D squarefree with omega(D) odd): M(U_0(M); V_k) = S_k(Gamma_0(DM))^{D-new}
(+ the constant function at k = 2). Hence, for ell not dividing DM,
    charpoly(T_ell) = (x - ell - 1)^{[k=2]} * prod_{d | M} charpoly(T_ell | S_k^new(Gamma_0(D d)))^{sigma_0(M / d)},
and for ell || M (the classical U_ell; a newform of level D d with ell | d has U_ell = a_ell, a form of level D d with
ell not | d contributes x^2 - a_ell x + ell^{k-1}, twice-old multiplicity sigma_0(M/(d ell))):
    charpoly(U_ell) = (x - ell)^{[k=2]} * prod_{d | M, ell | d} cp(U_ell | new(Dd))^{sigma_0(M/d)}
                      * prod_{d | M/ell} det(x^2 - x T_ell + ell^{k-1} | new(Dd))^{sigma_0(M/(d ell))}.
Run from code/python:  python3 -m langlandscape.hacs_bridge.laneC.check_hj4b_mf
Writes code/results/laneC/hj4b_level_mfcheck.json.
"""

from __future__ import annotations

import json

from ... import results
from ...pari import get_pari


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def main() -> None:
    pari = get_pari()
    x = pari("x")
    src = results.repo_root() / "code" / "results" / "laneC" / "hj4b_level.json"
    R = json.loads(src.read_text())
    cache = {}

    def newmat(N, k, ell):
        key = (N, k, ell)
        if key not in cache:
            mf = pari.mfinit([N, k], 0)
            cache[key] = None if int(pari.mfdim(mf)) == 0 else pari.mfheckemat(mf, ell)
        return cache[key]

    def cp(M):
        return pari.Pol(1) if M is None else pari.charpoly(M)

    cells = []
    with results.Timer() as t:
        for c in R["data"]["levels"]:
            if c["N1"] != 1 or c["rank"] == 0:
                continue
            D, M, k = c["D"], c["N0"], c["k"]
            per = {}
            for name, txt in c["charpoly"].items():
                ell = int(name[1:])
                ours = pari.Pol(list(reversed(json.loads(txt))))
                if name[0] == "T":
                    exp = (x - ell - 1) if k == 2 else pari.Pol(1)
                    for d in divisors(M):
                        exp *= cp(newmat(D * d, k, ell)) ** len(divisors(M // d))
                else:  # U_ell
                    if (M // ell) % ell == 0:
                        per[name] = "skipped (ell^2 | M)"
                        continue
                    exp = (x - ell) if k == 2 else pari.Pol(1)
                    for d in divisors(M):
                        if d % ell == 0:
                            exp *= cp(newmat(D * d, k, ell)) ** len(divisors(M // d))
                    for d in divisors(M // ell):
                        T = newmat(D * d, k, ell)
                        if T is None:
                            continue
                        n = int(pari.matsize(T)[0])
                        big = pari.matconcat(pari.matrix(2, 2, [T, -(ell ** (k - 1)) * pari.matid(n), pari.matid(n), 0 * pari.matid(n)]))
                        exp *= pari.charpoly(big) ** len(divisors(M // (d * ell)))
                per[name] = bool(ours == exp)
            cells.append({"D": D, "M": M, "k": k, "ops": per,
                          "all_equal": all(v is True for v in per.values() if not isinstance(v, str))})
    n_ok = sum(c["all_equal"] for c in cells)
    n_ops = sum(1 for c in cells for v in c["ops"].values() if not isinstance(v, str))
    n_ops_ok = sum(1 for c in cells for v in c["ops"].values() if v is True)
    data = {"source": "code/results/laneC/hj4b_level.json", "source_commit": R["provenance"]["commit"], "cells": cells,
            "cells_equal": n_ok, "cells_total": len(cells), "ops_equal": n_ops_ok, "ops_total": n_ops,
            "rule": __doc__.split("Run from")[0].strip()}
    results.write("laneC/hj4b_level_mfcheck.json", data, script="code/python/langlandscape/hacs_bridge/laneC/check_hj4b_mf.py",
                  params={"source_commit": R["provenance"]["commit"]}, runtime_s=t.seconds,
                  notes="HJ-4b: native Sym^n Brandt char-polys at U_0(M) vs PARI (JL with oldforms); tag computed")
    print(f"cells {n_ok}/{len(cells)}, operators {n_ops_ok}/{n_ops}")
    for c in cells:
        if not c["all_equal"]:
            print("MISMATCH", c)


if __name__ == "__main__":
    main()
