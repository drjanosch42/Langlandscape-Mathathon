# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Lane C, WP HJ-7a: compare the native C++ tree quotients (``jl_tree_dump``) with the stage-02/03 reference files.

Runs the standalone binary ``jl_tree_dump`` (``code/hacs/src/hacs/Registry/JL/quat/tools/jl_tree_dump.cpp``; build line in
``quat/README.md``), reads its JSON (schema ``langlandscape_tree/v1``), and compares it cell by cell with
``code/results/s02/{T2,T3,H_Vk,validation}.json`` and ``code/results/s03/{T1,T2,T6}.json``.  It recomputes nothing: every
number in the output comes from the binary; this script only matches labels (vertex permutations, since the native class
order is not PARI's) and compares.  Writes ``code/results/laneC/hj7_tree_w2.json`` ({provenance, summary, cells}).

Matching rules.
* Graph data (s0, s1, per-vertex stabilisers, matrices on Z[X]^2) is compared up to a vertex permutation pi found by a
  colour-refinement + backtracking search (same pi on both vertex types, edge labels = edge stabilisers); multisets and
  scalar invariants are compared directly.
* Fractions are compared as fractions ("52/1" = "52").
* Fields that the native code does not compute (PARI ``mf`` dimension predictions, Hecke operators T_l with l != q on H_0,
  the global model mod a prime of K, the norm-trace check, weight k > 2) are listed per cell under ``not_reproduced`` with
  the reason; weight k > 2 cells are left to HJ-7b.

Run (from ``code/python``)::

    python3 -m langlandscape.hacs_bridge.laneC_hj7_compare --binary /path/to/jl_tree_dump
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import pathlib
import subprocess
import sys
import time
from collections import Counter
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[4]
RES = ROOT / "code" / "results"


# ---------------------------------------------------------------- helpers
def git_commit() -> str:
    try:
        c = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
        d = subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain"], capture_output=True, text=True).stdout
        return c + ("-dirty" if d.strip() else "")
    except OSError:
        return "unknown"


def sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def F(x) -> Fraction:
    return Fraction(str(x))


def load(rel: str) -> dict:
    return json.loads((RES / rel).read_text())


class Cmp:
    """Collects field comparisons of one cell."""

    def __init__(self, label: str, source: str):
        self.label, self.source = label, source
        self.fields: dict[str, bool] = {}
        self.diffs: dict[str, dict] = {}
        self.not_reproduced: dict[str, str] = {}

    def eq(self, name: str, ours, ref, conv=None):
        a, b = (conv(ours), conv(ref)) if conv else (ours, ref)
        ok = a == b
        self.fields[name] = ok
        if not ok:
            self.diffs[name] = {"ours": ours, "ref": ref}
        return ok

    def skip(self, name: str, why: str):
        self.not_reproduced[name] = why

    def out(self, extra: dict | None = None) -> dict:
        subst = [k for k in self.fields if not non_substantive(k)]
        d = {"label": self.label, "source": self.source, "match": all(self.fields.values()) and bool(self.fields),
             "n_fields": len(self.fields), "n_fields_matched": sum(self.fields.values()),
             "n_fields_substantive": len(subst), "n_fields_substantive_matched": sum(self.fields[k] for k in subst)}
        if self.diffs:
            d["diffs"] = self.diffs
        if self.not_reproduced:
            d["not_reproduced"] = self.not_reproduced
        if extra:
            d.update(extra)
        return d


# review m1-m3: fields that are inputs echoed back (D, q, p, m, level), hard-coded (ker_alpha_saturated), constant at k = 2
# (p_le_k_minus_2), or duplicates of another compared field (n_vertices = 2X, S_s_expected = X, T6 H0 = cohomological H0,
# the acceptance-row rank_H1 = the case's k2.rank_H1, rank_M_U/rank_M_Uprime = rank_C0/2, rank_C1).
NON_SUBSTANTIVE = {"D", "q", "p", "m", "level", "ribet_exact.ker_alpha_saturated", "k2.p_le_k_minus_2", "n_vertices",
                   "n_vertices_BG", "S_s_expected(=X_per_type)", "H0", "k2.rank_M_U", "k2.rank_M_Uprime", "present",
                   "acceptance.rank_H1"}


def non_substantive(name: str) -> bool:
    return name in NON_SUBSTANTIVE


def msort(x):
    return sorted(x)


# ---------------------------------------------------------------- graph isomorphism (vertex permutation)
def find_perm(X: int, ours: dict, ref: dict):
    """pi : our vertex -> ref vertex with stab/w preserved and the labelled edge multisets equal; None if none.

    ``ours``/``ref``: {"stab": [...], "w": [...], "edges": [(s0, s1, label), ...]}."""
    if X == 0:
        return []

    def mats(g):
        M = Counter()
        for a, b, lab in g["edges"]:
            M[(a, b, lab)] += 1
        return M

    Mo, Mr = mats(ours), mats(ref)

    def refine(g, M):
        col = [(g["stab"][v], g["w"][v]) for v in range(X)]
        for _ in range(X + 1):
            sig = []
            for v in range(X):
                out = Counter()
                for (a, b, lab), n in M.items():
                    if a == v:
                        out[("o", col[b], lab)] += n
                    if b == v:
                        out[("i", col[a], lab)] += n
                sig.append((col[v], tuple(sorted(out.items()))))
            keys = {s: i for i, s in enumerate(sorted(set(sig)))}
            new = [keys[s] for s in sig]
            if len(set(new)) == len(set(col)):
                return [str(s) for s in sig]
            col = new
        return [str(c) for c in col]

    co, cr = refine(ours, Mo), refine(ref, Mr)
    if Counter(co) != Counter(cr):
        return None
    # adjacency (undirected) and per-vertex incident labelled edges
    def nbrs(M):
        nb = [set() for _ in range(X)]
        inc = [dict() for _ in range(X)]
        for (a, b, lab), n in M.items():
            nb[a].add(b)
            nb[b].add(a)
            inc[a][(a, b, lab)] = n
            inc[b][(a, b, lab)] = n
        return nb, inc

    nbo, inco = nbrs(Mo)
    nbr, incr = nbrs(Mr)
    # BFS order from a vertex of the rarest colour (connected graphs; other components appended)
    start = min(range(X), key=lambda v: sum(1 for c in co if c == co[v]))
    order, seen = [], set()
    for s in [start] + list(range(X)):
        if s in seen:
            continue
        seen.add(s)
        queue = [s]
        while queue:
            v = queue.pop(0)
            order.append(v)
            for u in sorted(nbo[v]):
                if u not in seen:
                    seen.add(u)
                    queue.append(u)
    pi = [-1] * X
    used = [False] * X

    def consistent(v):
        k_o = 0
        for (a, b, lab), n in inco[v].items():
            if pi[a] >= 0 and pi[b] >= 0:
                if Mr.get((pi[a], pi[b], lab), 0) != n:
                    return False
                k_o += n
        k_r = sum(n for (a, b, lab), n in incr[pi[v]].items() if used[a] and used[b])
        return k_o == k_r

    def cands(v):
        anchor = next((u for u in nbo[v] if pi[u] >= 0), None)
        pool = range(X) if anchor is None else sorted(nbr[pi[anchor]])
        return [r for r in pool if not used[r] and cr[r] == co[v]]

    def bt(i):
        if i == X:
            return Counter({(pi[a], pi[b], lab): n for (a, b, lab), n in Mo.items()}) == Mr
        v = order[i]
        for r in cands(v):
            if True:
                pi[v], used[r] = r, True
                if consistent(v) and bt(i + 1):
                    return True
                pi[v], used[r] = -1, False
        return False

    sys.setrecursionlimit(10000)
    return list(pi) if bt(0) else None


def perm2(M, pi, X):
    """Permute a 2X x 2X matrix on Z[X]^2 (ours) to the reference labelling."""
    n = 2 * X
    idx = [0] * n
    for v in range(X):
        idx[v] = pi[v]
        idx[X + v] = X + pi[v]
    R = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            R[idx[i]][idx[j]] = M[i][j]
    return R


def perm1(M, pi):
    X = len(pi)
    R = [[0] * X for _ in range(X)]
    for i in range(X):
        for j in range(X):
            R[pi[i]][pi[j]] = M[i][j]
    return R


def permvec2(v, pi, X):
    R = [0] * (2 * X)
    for i in range(X):
        R[pi[i]] = v[i]
        R[X + pi[i]] = v[X + i]
    return R


def graph_of(c, stab_key="stab_v", w_key="w_v"):
    return {"stab": c[stab_key], "w": c[w_key],
            "edges": [(a, b, s) for a, b, s in zip(c["s0"], c["s1"], c["stab_e"])]}


# ---------------------------------------------------------------- per file
def cmp_validation(ours: list[dict]) -> list[dict]:
    ref = load("s02/validation.json")["data"]["cases"]
    idx = {(c["D"], c["q"], c["level"]["N1"], c["level"]["N0"]): c for c in ours}
    out = []
    for r in ref:
        key = (r["D"], r["q"], r["level"]["N1"], r["level"]["N0"])
        cm = Cmp(f"D={key[0]} q={key[1]} N1={key[2]} N0={key[3]}", "s02/validation.json")
        o = idx.get(key)
        if o is None:
            cm.eq("present", False, True)
            out.append(cm.out())
            continue
        for f in ("X", "E", "rk_H1", "rk_boundary", "rk_H1_formula", "connected", "fibre_sums", "mass", "rk_H1_ok",
                  "all_pass"):
            cm.eq(f, o["rank_boundary"] if f == "rk_boundary" else o[f], r[f])
        cm.eq("vertex_mass", o["vertex_mass"], r["vertex_mass"], F)
        cm.eq("edge_mass", o["edge_mass"], r["edge_mass"], F)
        out.append(cm.out())
    return out


def cmp_T2_s02(ours: list[dict]) -> list[dict]:
    ref = load("s02/T2.json")["data"]
    out = []
    for o in ours:
        key = f"B{o['D']}_q{o['q']}"
        r = ref[key]
        cm = Cmp(key, "s02/T2.json")
        for f, of in (("D", "D"), ("q", "q"), ("X_per_type", "X"), ("n_edges", "E"), ("components", "components"),
                      ("rank_boundary", "rank_boundary"), ("rk_H1", "rk_H1"), ("rk_H1_formula", "rk_H1_formula"),
                      ("minus_one_in_U", "minus_one_in_U"), ("level", "level_str")):
            cm.eq(f, o[of], r[f])
        cm.eq("n_vertices", 2 * o["X"], r["n_vertices"])
        cm.eq("vertex_mass", o["vertex_mass"], r["vertex_mass"], F)
        cm.eq("edge_mass", o["edge_mass"], r["edge_mass"], F)
        cm.eq("stab_v_multiset", msort(o["stab_v"]), r["stab_v_multiset"])
        cm.eq("stab_e_multiset", msort(o["stab_e"]), r["stab_e_multiset"])
        rg = {"stab": [v["stab"] for v in r["vertices"]], "w": [v["w"] for v in r["vertices"]],
              "edges": [(e["s0"], e["s1"], e["stab"]) for e in r["edges"]]}
        pi = find_perm(o["X"], graph_of(o), rg)
        cm.eq("graph_isomorphic(vertices, edges, edge_multiplicities)", pi is not None, True)
        out.append(cm.out({"vertex_perm_ours_to_ref": pi}))
    return out


def cmp_T3(ours: list[dict]) -> list[dict]:
    ref = load("s02/T3.json")["data"]
    out = []
    for o in ours:
        key = f"s{o['s']}"
        r = ref[key]
        cm = Cmp(f"D=3 q=2 U1(5^{o['s']})", "s02/T3.json")
        for f, of in (("D", "D"), ("q", "q"), ("X_per_type", "X"), ("n_edges", "E"), ("components", "components"),
                      ("rank_boundary", "rank_boundary"), ("rk_H1", "rk_H1"), ("rk_H1_formula", "rk_H1_formula"),
                      ("minus_one_in_U", "minus_one_in_U"), ("level", "level_str")):
            cm.eq(f, o[of], r[f])
        cm.eq("n_vertices", 2 * o["X"], r["n_vertices"])
        cm.eq("S_s_expected(=X_per_type)", o["X"], r["S_s_expected"])
        cm.eq("vertex_mass", o["vertex_mass"], r["vertex_mass"], F)
        cm.eq("edge_mass", o["edge_mass"], r["edge_mass"], F)
        cm.eq("stab_v_multiset", msort(o["stab_v"]), r["stab_v_multiset"])
        cm.eq("stab_e_multiset", msort(o["stab_e"]), r["stab_e_multiset"])
        pi = None
        if "edges" in r:
            rg = {"stab": [v["stab"] for v in r["vertices"]], "w": [v["w"] for v in r["vertices"]],
                  "edges": [(e["s0"], e["s1"], e["stab"]) for e in r["edges"]]}
            pi = find_perm(o["X"], graph_of(o), rg)
            cm.eq("graph_isomorphic(vertices, edges, edge_multiplicities)", pi is not None, True)
        else:
            cm.skip("vertices/edges", "the reference stores the s = 3 graph as a summary only (no edge list)")
        out.append(cm.out({"vertex_perm_found": pi is not None} if pi is not None else None))
    return out


HVK_NOT = {
    "pred_rank_H1_JL / pred_rank_M_U / pred_rank_M_Uprime": "PARI mfdim dimension predictions (modular-forms side), not a "
                                                            "graph quantity; outside the native tree module",
    "rank_d_Fell / global_model / ell": "Gross's global model mod a prime of K (Python second model); the native code "
                                        "computes rank_Q(d) exactly instead (rank_d_Q, compared with rank_d_certified)",
    "norm_trace": "twoterm.LocalModel.norm_trace_check (Sym^n norm/trace idempotents, n = 0, 2, 4): weight k, HJ-7b",
    "k = 3..10": "weight k > 2 (Sym^{k-2} coefficients): HJ-7b",
}


def cmp_HVk(ours: list[dict]) -> list[dict]:
    ref = load("s02/H_Vk.json")["data"]["cases"]
    idx = {(c["D"], c["q"], c["level"]["N1"], c["level"]["N0"]): c for c in ours}
    out = []
    for r in ref:
        key = (r["D"], r["q"], r["N1"], r["N0"])
        o = idx[key]
        cm = Cmp(f"D={key[0]} q={key[1]} N1={key[2]} N0={key[3]} p={r['p']} m={r['m']} k=2", "s02/H_Vk.json")
        for f in ("X", "E", "components", "free", "minus_one_in_U"):
            cm.eq(f, o[f], r[f])
        cm.eq("p", o["p"], r["p"])
        cm.eq("m", o["m"], r["m"])
        cm.eq("level", o["level_str"], r["level"])
        cm.eq("stab_v_multiset", msort(o["stab_v"]), msort(r["stab_v"]))
        cm.eq("stab_e_multiset", msort(o["stab_e"]), msort(r["stab_e"]))
        rk, ok2 = r["k"]["2"], o["k2"]
        for f in ("rank_C0", "rank_C1", "rank_M_U", "rank_M_Uprime", "rank_d_Qp_lower", "rank_H1_Zp_upper",
                  "rank_H0_Zp_upper", "rank_Hco0_Zp_upper", "H0_p_part_exact", "p_le_k_minus_2", "pred_free_rank_H1"):
            cm.eq(f"k2.{f}", ok2[f], rk[f])
        for f in ("elem_div_vals_d", "H0", "H1", "Hco0", "Hco1"):
            cm.eq(f"k2.{f}", msort(ok2[f]), msort(rk[f]))
        for f in ("rank_H1", "rank_H0"):
            if f in rk:
                cm.eq(f"k2.{f}", ok2[f], rk[f])
        if "rank_d_certified" in rk:
            cm.eq("k2.rank_d_Q = reference pinned rank of d", ok2["rank_d_Q"], rk["rank_d_certified"])
        for k, v in HVK_NOT.items():
            cm.skip(k, v)
        out.append(cm.out())
    # acceptance rows at k = 2
    acc = load("s02/H_Vk.json")["data"]["acceptance"]
    lv = {}
    for o in ours:
        lv[(o["D"], o["q"], o["level_str"])] = o
    for a in acc:
        if a["k"] != 2:
            continue
        o = lv[(a["D"], a["q"], a["level"])]
        cm = Cmp(f"acceptance D={a['D']} q={a['q']} {a['level']} k=2", "s02/H_Vk.json#acceptance")
        cm.eq("acceptance.rank_H1", o["k2"]["rank_H1"], a["rank_H1"])
        cm.skip("pred / pred_JL / ok", "pred_JL is a PARI mfdim prediction (not native); rank_H1 is compared")
        out.append(cm.out())
    return out


def cmp_T1(ours: list[dict]) -> list[dict]:
    ref = load("s03/T1.json")["data"]
    out = []
    for o in ours:
        r = ref[str(o["q"])]
        cm = Cmp(f"B_{o['q']} (D = q = {o['q']}, M = 1)", "s03/T1.json")
        for f in ("q", "h", "weights", "gammas", "n2", "n3", "mass_w_ok", "mass_gamma_ok", "phi_order", "phi_divisors",
                  "phi_cyclic", "num_q_minus_1_over_12", "phi_order_ok", "eisenstein", "eisenstein_all"):
            cm.eq(f, o[f], r[f])
        cm.eq("mass_w", o["mass_w"], r["mass_w"], F)
        out.append(cm.out())
    return out


def cmp_T2_s03(ours: list[dict]) -> list[dict]:
    ref = load("s03/T2.json")["data"]
    out = []
    for o in ours:
        key = f"B{o['D']}_q{o['q']}"
        r = ref[key]
        X = o["X"]
        cm = Cmp(key, "s03/T2.json")
        for f, of in (("D", "D"), ("q", "q"), ("X_per_type", "X"), ("n_edges_X_Uprime", "E"), ("rk_H1", "rk_H1")):
            cm.eq(f, o[of], r[f])
        cm.eq("n_vertices_BG", 2 * X, r["n_vertices_BG"])
        cm.eq("w_vertices_multiset", msort(o["w_v"]), msort(r["w_vertices"]))
        cm.eq("w_edges_multiset", msort(o["w_e"]), msort(r["w_edges"]))
        cm.eq("collapse_two_vertex_weights_multiset", msort(o["collapse_two_vertex_weights_sorted"]),
              msort(r["collapse_two_vertex_weights"]))
        # the reference edges carry w_e; vertex labels by w_v (stab not stored in this file)
        og = {"stab": o["w_v"], "w": o["w_v"], "edges": [(a, b, w) for a, b, w in zip(o["s0"], o["s1"], o["w_e"])]}
        rg = {"stab": r["w_vertices"], "w": r["w_vertices"],
              "edges": [(a, b, w) for a, b, w in zip(r["s0"], r["s1"], r["w_edges"])]}
        pi = find_perm(X, og, rg)
        cm.eq("graph_isomorphic(s0, s1, w)", pi is not None, True)
        for blk in ("lem_bip", "ribet_exact", "phi_comb_BG", "phi_comb_collapsed", "phi_comb_BG_unweighted", "sign_check"):
            for f, v in r[blk].items():
                if f == "interpretation":
                    continue
                cm.eq(f"{blk}.{f}", o[blk][f], v)
        cm.eq("phi_collapsed_order", int(o["phi_collapsed_order"]), r["phi_collapsed_order"])
        cm.eq("T_q_eigenvalues", o["T_q_eigenvalues"], r["T_q_eigenvalues"])
        cm.eq("cusp_det_q1sq_minus_lam_sq", msort(o["cusp_det_q1sq_minus_lam_sq"]), msort(r["cusp_det_q1sq_minus_lam_sq"]))
        hb = o["hecke_block"]
        cm.eq("hecke.Hprime_equals_HT", hb["Hprime_equals_HT"], r["hecke"]["Hprime_equals_HT"])
        if pi is not None:
            for f in ("H", "Hprime", "H_transpose"):
                cm.eq(f"hecke.{f}", perm1(hb[f], pi), r["hecke"][f])
        for tag in ("weighted", "unweighted"):
            a, ra = o[f"alpha_alphadag_{tag}"], r[f"alpha_alphadag_{tag}"]
            for f in ("rank_matrix", "free_rank", "torsion_order", "divisors_gt1", "rank_Q", "index_on_ker_eps",
                      "coker_on_quotient_by_Eis_saturation", "coker_W_to_Wdual_order"):
                cm.eq(f"alpha_alphadag_{tag}.{f}", int(a[f]) if f in ("torsion_order", "index_on_ker_eps",
                      "coker_on_quotient_by_Eis_saturation", "coker_W_to_Wdual_order") else
                      ([int(x) for x in a[f]] if f == "divisors_gt1" else a[f]), ra[f])
            if pi is not None:
                cm.eq(f"alpha_alphadag_{tag}.matrix", perm2(a["matrix"], pi, X), ra["matrix"])
                cm.eq(f"alpha_alphadag_{tag}.eisenstein_vector", permvec2(a["eisenstein_vector"], pi, X),
                      ra["eisenstein_vector"])
                cm.eq(f"alpha_alphadag_{tag}_RibetSign.matrix", perm2(o[f"alpha_alphadag_{tag}_RibetSign"]["matrix"], pi, X),
                      r[f"alpha_alphadag_{tag}_RibetSign"]["matrix"])
        cm.skip("s0 / s1 / w_vertices / w_edges (as ordered lists)", "class order differs from PARI's; compared up to the "
                "vertex permutation found (graph_isomorphic) and as multisets")
        cm.skip("acceptance_note", "prose")
        extra = {"vertex_perm_ours_to_ref": pi,
                 "NEW_cuspidal_coker_weighted": o["alpha_alphadag_weighted"]["cuspidal_coker"],
                 "NEW_ihara": o["ihara"]}
        out.append(cm.out(extra))
    return out


T6_NOT = {
    "hecke (T_l, S_l, exponents, diamond)": "Hecke operators T_l (l != q) and S_l acting on H_0 = coker alpha: outside the "
                                            "HJ-7a weight-2 tree module (the exponents are only observable at k > 2)",
    "hecke_vs_mf": "comparison with PARI mf charpolys (modular-forms side)",
    "V_U1_coinvariants / eps_* / shapiro_equivariance / tau_transport": "the map epsilon to V_{U^1_p} and the Shapiro model "
                                                                        "of ihara.py; the native U_1(p) level is built "
                                                                        "directly (no Shapiro); H_0 and the ranks are compared",
}


def cmp_T6(ours: list[dict]) -> list[dict]:
    ref = load("s03/T6.json")["data"]["cases"]
    out = []
    for o in ours:
        lvl = o["level_T6"]
        r = next(c for c in ref if c["k"] == 2 and c["level"] == lvl and c["p"] == o["p"] and c["m"] == o["m"])
        cm = Cmp(f"B_3 q=2 {lvl} p={o['p']} m={o['m']} k=2", "s03/T6.json")
        cm.eq("H0", msort(o["H0_cohomological"]), msort(r["H0"]))
        cm.eq("conventions.cohomological.H0", msort(o["H0_cohomological"]), msort(r["conventions"]["cohomological"]["H0"]))
        cm.eq("conventions.homological.H0", msort(o["H0_homological"]), msort(r["conventions"]["homological"]["H0"]))
        if "rank_P" in r:
            cm.eq("rank_P", o["rank_P"], r["rank_P"])
            cm.eq("rank_edge_module", o["rank_edge_module"], r["rank_edge_module"])
        for k, v in T6_NOT.items():
            cm.skip(k, v)
        out.append(cm.out())
    return out


# ---------------------------------------------------------------- main
BUILD_CMD = None


def main(argv=None) -> int:
    global BUILD_CMD
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--dump", default=None, help="write the raw native dump here as well")
    ap.add_argument("--out", default=str(RES / "laneC" / "hj7_tree_w2.json"))
    ap.add_argument("--build-cmd", default=None, help="the build command, recorded in the provenance (review m5)")
    a = ap.parse_args(argv)
    BUILD_CMD = a.build_cmd
    binp = pathlib.Path(a.binary).resolve()
    t0 = time.time()
    p = subprocess.run([str(binp)], capture_output=True, text=True, check=True)
    runtime = time.time() - t0
    nat = json.loads(p.stdout)
    if a.dump:
        pathlib.Path(a.dump).write_text(p.stdout)
    S = nat["suites"]
    groups = {
        "s02/validation.json": cmp_validation(S["s02_validation"]),
        "s02/T2.json": cmp_T2_s02(S["s02_T2"]),
        "s02/T3.json": cmp_T3(S["s02_T3"]),
        "s02/H_Vk.json": cmp_HVk(S["s02_HVk2"]),
        "s03/T1.json": cmp_T1(S["s03_T1"]),
        "s03/T2.json": cmp_T2_s03(S["s03_T2"]),
        "s03/T6.json": cmp_T6(S["s03_T6k2"]),
    }
    # cells out of reach
    hvk = load("s02/H_Vk.json")["data"]
    t6 = load("s03/T6.json")["data"]["cases"]
    out_of_reach = {
        "s02/H_Vk.json": {"cells": sum(1 for c in hvk["cases"] for k in c["k"] if k != "2"),
                          "acceptance_rows": sum(1 for x in hvk["acceptance"] if x["k"] != 2),
                          "reason": "weight k = 3..10 (Sym^{k-2} coefficients over Z/p^m): HJ-7b"},
        "s03/T6.json": {"cells": sum(1 for c in t6 if c["k"] != 2),
                        "reason": "weight k = 3..14 (V_k over Z/p^m, Hecke exponents): HJ-7b"},
    }
    summary = {}
    for g, cells in groups.items():
        summary[g] = {"cells_compared": len(cells), "cells_matched": sum(c["match"] for c in cells),
                      "fields_compared": sum(c["n_fields"] for c in cells),
                      "fields_matched": sum(c["n_fields_matched"] for c in cells),
                      "fields_substantive_compared": sum(c["n_fields_substantive"] for c in cells),
                      "fields_substantive_matched": sum(c["n_fields_substantive_matched"] for c in cells),
                      "mismatched_cells": [c["label"] for c in cells if not c["match"]]}
        if g in out_of_reach:
            summary[g]["not_in_reach"] = out_of_reach[g]
    b11 = next(c for c in S["s03_T2"] if c["D"] == 11 and c["q"] == 2)
    headline = {
        "cell": "B_11 (D = 11), q = 2, U = O^x",
        "graph": {"X": b11["X"], "E": b11["E"], "stab_v": b11["stab_v"], "stab_e": b11["stab_e"], "s0": b11["s0"],
                  "s1": b11["s1"], "T_q": b11["hecke"]},
        "coker_alpha_alphadag_weighted_on_cuspidal_part": b11["alpha_alphadag_weighted"]["cuspidal_coker"],
        "coker_alpha_alphadag_weighted_literal": {"free_rank": b11["alpha_alphadag_weighted"]["free_rank"],
                                                  "torsion": b11["alpha_alphadag_weighted"]["divisors_gt1"]},
        "phi_comb_collapsed": b11["phi_comb_collapsed"],
        "ihara": b11["ihara"],
        "status": "computed (HACS-native C++, hacs_jl::build_tree + tree2)",
    }
    doc = {
        "provenance": {
            "script": "code/python/langlandscape/hacs_bridge/laneC_hj7_compare.py",
            "tool": "code/hacs/src/hacs/Registry/JL/quat/tools/jl_tree_dump.cpp (standalone g++ -O2 build)",
            "binary": str(binp), "binary_sha256": sha256(binp), "commit": git_commit(),
            "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
            "runtime_s": round(runtime, 3), "native_suite_seconds": nat.get("suite_seconds"),
            "params": {"suites": list(S.keys())},
            "references": list(groups.keys()),
            "build_cmd": BUILD_CMD,
            "notes": {"s03/T1.json": "the T1 suite tests the class sets (weights, mass, Phi of the two-vertex DR graph, "
                                     "Eisenstein check with Brandt T_l), not the tree quotient (review m7)",
                      "fields_substantive": "excludes echoed inputs (D, q, p, m, level), the hard-coded "
                                            "ker_alpha_saturated, p_le_k_minus_2 at k = 2 and duplicated fields "
                                            "(review m1-m3)"},
            "status": "computed (native); compared against the stage-02/03 Python results (checked where match = true)",
        },
        "headline": headline,
        "summary": summary,
        "cells": groups,
    }
    outp = pathlib.Path(a.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(doc, indent=1, sort_keys=False) + "\n")
    for g, s in summary.items():
        print(f"{g}: {s['cells_matched']}/{s['cells_compared']} cells, {s['fields_matched']}/{s['fields_compared']} fields"
              f" ({s['fields_substantive_matched']}/{s['fields_substantive_compared']} substantive);"
              f" mismatched: {s['mismatched_cells'][:6]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
