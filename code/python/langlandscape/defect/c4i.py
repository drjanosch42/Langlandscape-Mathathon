# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C2: regression of seed C4(i): ``v(h) = v(c_q)`` over classical ``S_k(Gamma_0(qM))``.

Tex: ``plan/staged/stage-06-integral-defect.tex`` (``def:s06-rings``, ``thm:s06-E``, remark ``rem:s06-minus1``(d)).
Here ``h = eta(S, lam) / eta(S', lam')`` (principal ideals), so ``v(h) = ord eta - ord eta_new`` at the place ``v`` of
``O`` over ``m``, and ``c_q = lam(b)``.  Thm E(iii): equality when ``O`` is a DVR (and ``eta`` is the base-changed congruence
ideal, as in :func:`.congruence.eta`); in the Eisenstein case ``(h) >= c_q`` i.e. ``v(h) <= v(c)`` is tested.

Cases: ``q in {2, 3, 5}``, ``N = qM <= 70`` with ``q || N``, even ``k in [2, 16]`` with ``S_k(N)`` and ``S_k(M)`` non-zero; for each
case all primes ``p`` with ``T/(a+b)`` of ``p``-power order, all maximal ideals ``m | p`` in the support of ``a + b``, all
orbits ``f`` of newforms of *exact* level ``N`` through ``m``.  A row is *in scope* if ``p >= 5``, ``p`` prime to ``N``,
``q != +-1 mod p`` (this is (H0)+(H0^-)); out-of-scope rows are recorded too.  Status: *computed*.
"""

from __future__ import annotations

import time

from ..pari import get_pari
from . import hecke_alg as ha
from .congruence import Character, defect
from .hecke_alg import HeckeAlgebra, local_length, maximal_ideals

QS = (2, 3, 5)
NMAX, KMAX = 70, 16
MAX_DIM = 60          # dim S_k(Gamma_0(N)) bound (C1: > 100 scales badly; lowered after timing, see results notes)


def cases(nmax: int = NMAX, kmax: int = KMAX) -> list[dict]:
    P = get_pari()
    out = []
    for q in QS:
        for N in range(q, nmax + 1, q):
            if (N // q) % q == 0:
                continue
            for k in range(2, kmax + 1, 2):
                d = int(P(f"mfdim([{N},{k}],1)"))
                do = int(P(f"mfdim([{N // q},{k}],1)"))
                if d > 0 and do > 0:
                    out.append({"q": q, "N": N, "k": k, "dim": d, "dim_old_M": do})
    return out


def _is_eisenstein(m, N: int, k: int, p: int) -> bool:
    """``T_l = 1 + l^{k-1} mod p`` for every generator ``l`` with ``l`` prime to ``N p`` (reducible residual rep)."""
    tested = 0
    for g, v in m.values.items():
        if not g.startswith("T"):
            continue
        l = int(g[1:])
        if N % l == 0 or l == p:
            continue
        tested += 1
        if (v - 1 - pow(l, k - 1, p)) % p != 0:
            return False
    return tested > 0


def run_case(c: dict) -> dict:
    q, N, k = c["q"], c["N"], c["k"]
    t0 = time.perf_counter()
    D = ha.mf_qnew_qold(N, k, q)
    reps = {"new": D["new"], "old": D["old"]}
    reps.update({f"f{i}": o["rep"] for i, o in enumerate(D["orbits"])})
    T = HeckeAlgebra(D["full"], reps)
    a, b = T.kernel_of_rep("new"), T.kernel_of_rep("old")
    ab = a + b
    rows = []
    divs, _ = ab.divisors_in(T.whole())
    primes = _primes_of(divs)
    for p in primes:
        for m in maximal_ideals(T, p):
            if not local_length(T.whole(), ab, m):
                continue
            for i in range(len(D["orbits"])):
                chi = Character.from_rep(T, f"f{i}")
                try:
                    chi.place(m)
                except ValueError:
                    continue
                r = defect(T, chi, m)
                o = r["ord"]
                vh = o["eta"] - o["eta_new"]
                eis = _is_eisenstein(m, N, k, p)
                in_scope = p >= 5 and N % p != 0 and (q - 1) % p != 0 and (q + 1) % p != 0
                rows.append({"p": p, "orbit": i, "orbit_degree": D["orbits"][i].get("degree", chi.O.d), "O_rank": chi.O.d,
                             "m": r["m"], "eisenstein": eis, "in_scope": in_scope,
                             "v_h": _f(vh), "v_c": _f(o["c"]), "v_eta": _f(o["eta"]), "v_eta_new": _f(o["eta_new"]),
                             "gorenstein_S_m": r["gorenstein"]["S_m"]["gorenstein"],
                             "O_v_dvr": bool(r["place"].get("dvr")),
                             "equal": vh == o["c"], "h_contains_c": vh <= o["c"]})
    return {**c, "primes": primes, "rows": rows, "seconds": round(time.perf_counter() - t0, 2)}


def _f(x):
    return x if isinstance(x, int) else str(x)


def _primes_of(divs) -> list[int]:
    P = get_pari()
    ps = set()
    for x in divs:
        x = abs(int(x))
        if x > 1:
            ps.update(int(pp) for pp in P.factor(x)[0])
    return sorted(ps)


def summarise(results: list[dict]) -> dict:
    rows = [dict(r, q=c["q"], N=c["N"], k=c["k"]) for c in results for r in c.get("rows", [])]
    ins = [r for r in rows if r["in_scope"] and not r["eisenstein"]]
    eis = [r for r in rows if r["eisenstein"]]
    return {"cases_run": len(results), "rows": len(rows),
            "in_scope_non_eisenstein": {"n": len(ins), "equal": sum(r["equal"] for r in ins),
                                        "violations": [_key(r) for r in ins if not r["equal"]],
                                        "n_gorenstein": sum(r["gorenstein_S_m"] for r in ins),
                                        "n_dvr": sum(r["O_v_dvr"] for r in ins)},
            "eisenstein": {"n": len(eis), "h_contains_c": sum(r["h_contains_c"] for r in eis),
                           "equal": sum(r["equal"] for r in eis),
                           "dvr_n": sum(r["O_v_dvr"] for r in eis),
                           "dvr_h_contains_c": sum(r["h_contains_c"] for r in eis if r["O_v_dvr"]),
                           "violations_dvr": [_key(r) for r in eis if r["O_v_dvr"] and not r["h_contains_c"]],
                           "violations_non_dvr": [_key(r) for r in eis if not r["O_v_dvr"] and not r["h_contains_c"]],
                           "in_scope_n": sum(r["in_scope"] for r in eis),
                           "in_scope_h_contains_c": sum(r["h_contains_c"] for r in eis if r["in_scope"])},
            "out_of_scope_non_eisenstein": {"n": sum(1 for r in rows if not r["in_scope"] and not r["eisenstein"]),
                                            "equal": sum(r["equal"] for r in rows if not r["in_scope"] and not r["eisenstein"])}}


def _key(r: dict) -> dict:
    return {k: r[k] for k in ("q", "N", "k", "p", "orbit", "v_h", "v_c", "gorenstein_S_m", "O_v_dvr")}


def main(max_dim: int = MAX_DIM, budget_s: float = 900.0) -> None:  # pragma: no cover - script entry point
    """Write ``code/results/s06/C4i.json``; cases in order of increasing dimension, stopping at ``budget_s``."""
    from .. import results
    from cypari2.handle_error import PariError
    allc = sorted(cases(), key=lambda c: (c["dim"], c["q"], c["N"], c["k"]))
    done, skipped = [], []
    t_start = time.perf_counter()
    with results.Timer() as tm:
        for c in allc:
            if c["dim"] > max_dim:
                skipped.append({**c, "reason": f"dim > {max_dim} (C1 scaling)"})
            elif (time.perf_counter() - t_start) > budget_s:
                skipped.append({**c, "reason": "time budget"})
            else:
                try:
                    done.append(run_case(c))
                except (PariError, MemoryError) as e:  # pragma: no cover
                    skipped.append({**c, "reason": f"{type(e).__name__}: {str(e)[:80]}"})
                print(c, len(done[-1]["rows"]) if done and done[-1]["N"] == c["N"] and done[-1]["k"] == c["k"] else "-",
                      flush=True)
    data = {"summary": summarise(done), "n_cases_total": len(allc), "n_cases_run": len(done), "skipped": skipped,
            "cases": done}
    path = results.write("s06/C4i.json", data, script="code/python/langlandscape/defect/c4i.py",
                         params={"q": list(QS), "N_max": NMAX, "k_max": KMAX, "max_dim": max_dim, "budget_s": budget_s},
                         runtime_s=round(tm.seconds, 3),
                         notes="S06-C2 seed C4(i) regression; h = eta/eta_new, orbits of exact level N; computed")
    print(path, data["summary"])


def resummarise() -> None:  # pragma: no cover - script entry point
    """Recompute ``summary`` of the existing ``C4i.json`` from its rows (no recomputation of the cases)."""
    import json
    from .. import results
    path = results.repo_root() / "code" / "results" / "s06" / "C4i.json"
    d = json.loads(path.read_text())
    d["data"]["summary"] = summarise(d["data"]["cases"])
    d["provenance"]["notes"] += "; summary re-derived from the stored rows by c4i.resummarise()"
    path.write_text(json.dumps(d, indent=1, sort_keys=True) + "\n")


if __name__ == "__main__":  # pragma: no cover
    import sys
    resummarise() if "--resummarise" in sys.argv else main()
