# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-4a audit m3: orbit congruence indices on the native intrinsic Sym^n Brandt lattice (jl_brandtsym_dump record).

For a record (default code/results/laneC/records/D13_M1_k8.json) and T = T_p (default p = 2, which has squarefree
char-poly there): for each Q-irreducible factor g of chi = charpoly(T), L_g = ker_Z g(T), L_g^c = ker_Z (chi/g)(T)
(PARI matkerint, saturated), and the index [L : L_g + L_g^c] = |det(L_g | L_g^c)| (factored). Lane B's HJ-6b found the
odd congruence 37 at D = 13, k = 8 between x - 10 and x^2 + 19x + 6 on its (hull) lattice; this reproduces it on ours.
Run from code/python:  python3 -m langlandscape.hacs_bridge.laneC.check_hj4_congruence [record.json] [p]
Writes code/results/laneC/hj4_congruence.json.
"""

from __future__ import annotations

import json
import pathlib
import sys

from ... import results
from ...pari import get_pari


def orbit_indices(pari, F):
    n = len(F)
    M = pari.matrix(n, n, [int(x) for r in F for x in r])
    cp = pari.charpoly(M)
    fa = pari.factor(cp)
    out = []
    for i in range(int(pari.matsize(fa)[0])):
        g = fa[i, 0]
        assert int(fa[i, 1]) == 1, "char-poly not squarefree; use another operator"
        h = cp / g
        Kg = pari.matkerint(pari.subst(g, "x", M))
        Kh = pari.matkerint(pari.subst(h, "x", M))
        d = abs(pari.matdet(pari.concat(Kg, Kh)))
        out.append({"orbit": str(g), "index": str(d), "index_factored": str(pari.factor(d)) if d > 1 else "1"})
    return str(cp), out


def main() -> None:
    root = results.repo_root()
    rec = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else root / "code/results/laneC/records/D13_M1_k8.json"
    p = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    R = json.loads(rec.read_text())
    fb = R["data"]["free_block_z"]
    pari = get_pari()
    with results.Timer() as t:
        cp, orbs = orbit_indices(pari, fb["F"][fb["ops"].index(p)])
    data = {"record": str(rec.relative_to(root)) if rec.is_relative_to(root) else str(rec), "record_commit": R["provenance"]["commit"],
            "D": fb["D"], "k": fb["k"], "operator": f"T_{p}", "charpoly": cp, "orbits": orbs,
            "lattice": fb["basis_rule"], "tag": "computed"}
    results.write("laneC/hj4_congruence.json", data, script="code/python/langlandscape/hacs_bridge/laneC/check_hj4_congruence.py",
                  params={"record": data["record"], "p": p}, runtime_s=t.seconds,
                  notes="HJ-4a audit m3: orbit congruence indices [L : L_g + L_g^c] on the intrinsic lattice (PARI matkerint)")
    for o in orbs:
        print(o["orbit"], o["index_factored"])


if __name__ == "__main__":
    main()
