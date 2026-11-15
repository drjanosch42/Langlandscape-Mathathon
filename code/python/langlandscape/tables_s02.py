"""S02-C3: tables T2 (H02.3) and T3 (H02.4) from the tree-quotient builder ``tree.build``.

``rk H_1`` is computed independently of the formula ``|E|-2|X|+1`` as ``E - rank_Q(boundary)`` where the boundary
``Z^E -> Z^{2X}`` is ``e -> -[(s0 e,0)] + [(s1 e,1)]``.  Run ``python3 -m langlandscape.tables_s02``.
"""

from __future__ import annotations

from fractions import Fraction

from . import results, tree

T2_CASES = [(2, 7), (2, 13), (11, 2)]       # (D, q)
T2_EXPECT = {(2, 7): (1, 2), (2, 13): (2, 3), (11, 2): (0, 3)}  # (rk H1, |E|)
T3_D, T3_Q, T3_N = 3, 2, 5


def rank_Q(rows: list[dict[int, int]], ncols: int) -> int:
    """Rank over Q of a sparse matrix given as list of {col: value} rows (exact, Fraction elimination)."""
    piv: dict[int, dict[int, Fraction]] = {}
    r = 0
    for row in rows:
        v = {c: Fraction(a) for c, a in row.items() if a}
        while v:
            c = min(v)
            if c not in piv:
                piv[c] = v
                r += 1
                break
            p = piv[c]
            f = v[c] / p[c]
            for k, a in p.items():
                nv = v.get(k, 0) - f * a
                if nv:
                    v[k] = nv
                else:
                    v.pop(k, None)
    return r


def boundary_rank(T) -> int:
    """Rank of ``d : Z^E -> Z^{2X}`` (columns = edges); vertex ``(x,0)`` is index x, ``(x,1)`` is ``X + x``."""
    rows = [{T.X + b: 1, a: -1} for a, b in zip(T.s0, T.s1)]  # one row per edge (transpose, same rank)
    return rank_Q(rows, 2 * T.X)


def summarize(T, full: bool = True) -> dict:
    X, E = T.X, T.E
    rk_d = boundary_rank(T)
    comps = T.components()
    d = {
        "D": T.D, "q": T.q, "level": str(T.level), "X_per_type": X, "n_vertices": 2 * X, "n_edges": E,
        "components": comps, "rank_boundary": rk_d, "rk_H1": E - rk_d, "rk_H1_formula": E - 2 * X + 1,
        "minus_one_in_U": T.minus_one_in_U,
        "vertex_mass": sum(Fraction(1, v.stab) for v in T.vertices0),
        "edge_mass": sum(Fraction(1, e.stab) for e in T.edges),
        "stab_v_multiset": sorted(T.stab_v), "stab_e_multiset": sorted(T.stab_e),
    }
    if full:
        d["vertices"] = [
            {"name": f"x{i}", "type0": f"a{i}", "type1": f"b{i}", "class": v.c, "stab": v.stab, "w": v.w}
            for i, v in enumerate(T.vertices0)
        ]
        d["edges"] = [
            {"name": f"e{i}", "stab": e.stab, "s0": T.s0[i], "s1": T.s1[i],
             "from": f"a{T.s0[i]}", "to": f"b{T.s1[i]}"}
            for i, e in enumerate(T.edges)
        ]
        pairs: dict[str, int] = {}
        for a, b in zip(T.s0, T.s1):
            k = f"a{a}-b{b}"
            pairs[k] = pairs.get(k, 0) + 1
        d["edge_multiplicities"] = pairs
    return d


def t2() -> dict:
    out = {}
    for D, q in T2_CASES:
        T = tree.build(D, q)
        out[f"B{D}_q{q}"] = summarize(T)
    return out


def t3(smax: int = 3) -> dict:
    out = {}
    for s in range(1, smax + 1):
        T = tree.build(T3_D, T3_Q, tree.Level.U1(T3_N ** s))
        d = summarize(T, full=(s <= 2))
        if s == 1:
            d["self_contained_graph"] = {
                "description": "BG(U_1(5),2) for B_3: bipartite, a_i = (x_i,0), b_i = (x_i,1), edge e_k: a_{s0} -> b_{s1}",
                "vertices_type0": [f"a{i}" for i in range(T.X)],
                "vertices_type1": [f"b{i}" for i in range(T.X)],
                "edges": [[f"a{a}", f"b{b}"] for a, b in zip(T.s0, T.s1)],
                "edge_multiplicities": d["edge_multiplicities"],
                "genus": d["rk_H1"],
            }
        d["S_s_expected"] = 2 * 25 ** (s - 1)
        out[f"s{s}"] = d
    return out


def main() -> None:
    with results.Timer() as t:
        a = t2()
    results.write("s02/T2.json", a, script="langlandscape.tables_s02", params={"cases": T2_CASES},
                  runtime_s=t.seconds, notes="H02.3: rk H1 = E - rank(boundary) over Q")
    with results.Timer() as t:
        b = t3()
    results.write("s02/T3.json", b, script="langlandscape.tables_s02",
                  params={"D": T3_D, "q": T3_Q, "level": "U_1(5^s)", "s": [1, 2, 3]},
                  runtime_s=t.seconds, notes="H02.4; s=3 summary only; s=1 entry has self_contained_graph")
    for k, v in {**a, **b}.items():
        print(k, v["X_per_type"], v["n_edges"], v["rk_H1"])


if __name__ == "__main__":
    main()
