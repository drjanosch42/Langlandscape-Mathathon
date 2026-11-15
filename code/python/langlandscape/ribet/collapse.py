# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C3 (T2): collapse of the stage-02 quotient graphs BG(O^x, q) onto the two-vertex DR graph (thm:s03-ribet).

Tex: ``mathematics/chapters/s03/3-ribet.tex`` (``lem:s03-bip``, ``thm:s03-ribet``, sign table) and ``4-ihara.tex`` (C1).

Setup.  ``BG = BG(U, q)`` with ``U = Ohat^x`` (stage 02, :func:`langlandscape.tree.build`): vertices ``(x,0),(x,1)`` for
``x in X(U)``, edges ``E = X(U')`` with ``s0, s1 : E -> X``, oriented 0 -> 1.  ``alpha = (-s0_*, s1_*) : Z[E] -> Z[X]^2``
(= ``boundary`` of :mod:`ribet.graphs`, rows ordered ``(V0, V1)``).  Weights: ``w_x`` (vertex), ``w_e`` (edge); ``w_e | w_{s_j e}``.

``alpha^dagger`` is the adjoint for the weighted pairings ``<x,x> = w_x`` on ``Z[X]`` and ``<e,e> = w_e`` on ``Z[E]``:
``alpha^dagger f = sum_e (<f, alpha e>/w_e) e``, so ``alpha alpha^dagger f = sum_e <f, alpha e> / w_e * alpha e``.  Its matrix
on ``Z[X]^2`` (``<f,alpha e>`` carries the weight of the vertex of ``f``) is, with ``H[x][x'] = sum_{e: x->x'} w_x/w_e``
(= ``TreeQuotient.hecke_matrix``, the Brandt matrix ``T_q``) and ``H'[x][x'] = sum_{e: x->x'} w_{x'}/w_e``::

    alpha alpha^dagger = [[ (q+1) I,  -H'  ],
                          [  -H^T,  (q+1) I ]]        (weighted)

(the diagonal blocks are ``w_x sum_{s_j e = x} 1/w_e = q+1``); unweighted (all weights 1): ``[[diag(deg0), -A],[-A^T, diag(deg1)]]``
with ``A`` the adjacency matrix.  Ribet's sign ``(s0_*, s1_*)`` gives ``+H', +H^T`` in the off-diagonal blocks.

``coker`` of a singular integer matrix is ``Z^r (+) torsion``; we report rank and torsion order (product of the nonzero
elementary divisors).  Run ``python3 -m langlandscape.ribet.collapse`` from ``code/python`` -> ``code/results/s03/T2.json``.
"""

from __future__ import annotations

from math import prod

from .. import pari as _pari
from .. import results, tree
from . import graphs as G

CASES = [(2, 7), (2, 13), (11, 2)]  # (D, q)


def _mat(rows, nr, nc):
    return G._mat(rows, nr, nc)


def rank_Q(rows, nr, nc) -> int:
    if nr == 0 or nc == 0:
        return 0
    return int(_pari.get_pari().matrank(_mat(rows, nr, nc)))


def snf(rows, nr, nc) -> list:
    """All elementary divisors (nonzero), ascending."""
    return G.smith_divisors(rows, nr, nc)


def graph_of(T, weighted: bool = True) -> G.WGraph:
    """Bipartite WGraph of BG(U,q): V0 = 0..X-1, V1 = X..2X-1; edge weights ``w_e`` (or 1)."""
    w = tuple(T.w_e) if weighted else None
    return G.bipartite(T.X, T.X, list(T.s0), list(T.s1), w)


def alpha_matrix(T) -> list:
    """``alpha`` as a ``2X x E`` integer matrix: column e = ``-[s0 e]_0 + [s1 e]_1``."""
    X, E = T.X, T.E
    M = [[0] * E for _ in range(2 * X)]
    for e in range(E):
        M[T.s0[e]][e] -= 1
        M[X + T.s1[e]][e] += 1
    return M


def alpha_alphadag(T, weighted: bool = True, sign: int = 1) -> list:
    """Matrix of ``alpha alpha^dagger`` on ``Z[X]^2`` (rows/cols ``(V0,V1)``); ``sign=-1`` gives Ribet's ``(s0_*,s1_*)``."""
    X, E = T.X, T.E
    wx = list(T.w_v) if weighted else [1] * X
    we = list(T.w_e) if weighted else [1] * E
    M = [[0] * (2 * X) for _ in range(2 * X)]
    for e in range(E):
        a, b = T.s0[e], T.s1[e]
        # alpha e = -[a]_0 + [b]_1 ; contribution of basis vector f=[y]_j: <f, alpha e>/w_e * alpha e
        for (j, y, sy) in ((0, a, -1), (1, b, 1)):
            wy = wx[y]
            assert wy % we[e] == 0
            c = (wy // we[e]) * sy
            col = j * X + y
            M[a][col] += c * (-1)
            M[X + b][col] += c * 1
    if sign == -1:  # flip off-diagonal blocks (Ribet): conjugate by diag(-1, 1)
        for i in range(2 * X):
            for k in range(2 * X):
                if (i < X) != (k < X):
                    M[i][k] = -M[i][k]
    return M


def coker_info(M, n) -> dict:
    d = snf(M, n, n)
    return {"rank_matrix": len(d), "free_rank": n - len(d), "torsion_order": prod(d) if d else 1,
            "divisors_gt1": [x for x in d if x != 1]}


def hecke_blocks(T) -> dict:
    X = T.X
    H = T.hecke_matrix()
    Hp = [[0] * X for _ in range(X)]
    for e in range(T.E):
        Hp[T.s0[e]][T.s1[e]] += T.w_v[T.s1[e]] // T.w_e[e]
    HT = [[H[j][i] for j in range(X)] for i in range(X)]
    return {"H": H, "Hprime": Hp, "H_transpose": HT, "Hprime_equals_HT": Hp == HT}


def eigenvalues_H(H) -> list:
    """Eigenvalues of the integer matrix H via PARI charpoly roots (exact integers expected for these cases)."""
    pari = _pari.get_pari()
    n = len(H)
    cp = pari.charpoly(_mat(H, n, n))
    roots = pari.nfroots(None, cp)
    return sorted(int(r) for r in roots)


def collapse_case(D: int, q: int) -> dict:
    T = tree.build(D, q)
    X, E = T.X, T.E
    Gw, Gu = graph_of(T, True), graph_of(T, False)
    n0 = X
    G2 = G.collapse(Gw, n0)
    chk = G.check_bip(X, X, list(T.s0), list(T.s1))
    # Ribet sequence 0 -> H1 -> Z[E] --alpha--> Z[X]^2 --eps--> Z -> 0, eps(f0,f1) = deg f0 + deg f1
    A = alpha_matrix(T)
    dA = snf(A, 2 * X, E)
    rkA = len(dA)
    H1 = G.X_basis(Gw)
    eps_kills = all(sum(A[i][e] for i in range(2 * X)) == 0 for e in range(E))
    coker_alpha_torsion_free = all(x == 1 for x in dA)  # Z^{2X}/im alpha has torsion = prod of divisors > 1
    exact = {
        "ker_alpha_rank": E - rkA, "rk_H1": len(H1), "rk_H1_formula": E - 2 * X + 1,
        "alpha_injective_mod_H1": (E - rkA) == len(H1),
        "rank_alpha": rkA, "coker_alpha_rank": 2 * X - rkA, "coker_alpha_torsion_free": coker_alpha_torsion_free,
        "eps_kills_im_alpha": eps_kills, "coker_alpha_iso_Z": (2 * X - rkA == 1) and coker_alpha_torsion_free,
        "ker_alpha_saturated": True,  # ker is X_basis (matkerint), saturated by construction
    }
    hb = hecke_blocks(T)
    out = {
        "D": D, "q": q, "X_per_type": X, "n_edges_X_Uprime": E, "n_vertices_BG": 2 * X, "rk_H1": len(H1),
        "w_vertices": list(T.w_v), "w_edges": list(T.w_e), "s0": list(T.s0), "s1": list(T.s1),
        "collapse_two_vertex_weights": list(G2.w),
        "lem_bip": chk, "ribet_exact": exact,
        "phi_comb_BG": G.phi_comb(Gw), "phi_comb_collapsed": G.phi_comb(G2),
        "phi_comb_BG_unweighted": G.phi_comb(Gu),
        "hecke": hb, "T_q_eigenvalues": eigenvalues_H(hb["H"]),
    }
    n = 2 * X
    for tag, wt in (("weighted", True), ("unweighted", False)):
        M = alpha_alphadag(T, wt)
        out[f"alpha_alphadag_{tag}"] = {"matrix": M, **coker_info(M, n), "rank_Q": rank_Q(M, n, n)}
        out[f"alpha_alphadag_{tag}_RibetSign"] = {"matrix": alpha_alphadag(T, wt, -1)}
    Mw = alpha_alphadag(T, True)
    out["sign_check"] = {
        "diag_blocks_are_q_plus_1": all(Mw[i][i] == q + 1 for i in range(n)),
        "offdiag_upper_is_minus_Hprime": all(Mw[i][X + k] == -hb["Hprime"][i][k] for i in range(X) for k in range(X)),
        "offdiag_lower_is_minus_HT": all(Mw[X + i][k] == -hb["H_transpose"][i][k] for i in range(X) for k in range(X)),
        "offdiag_entries_nonpositive": all(Mw[i][k] <= 0 for i in range(n) for k in range(n) if (i < X) != (k < X)),
        "interpretation": "offdiag blocks of alpha alpha^dagger for alpha=(-s0*,s1*) are -T_q (-H', -H^T); Ribet's (s0*,s1*) gives +T_q",
    }
    # alpha alpha^dagger restricted to ker eps = {deg f0 + deg f1 = 0} (rank 2X-1, contains im alpha): index of its image
    for tag, wt in (("weighted", True), ("unweighted", False)):
        M = alpha_alphadag(T, wt)
        K = [[(1 if j == i else 0) - (1 if j == n - 1 else 0) for j in range(n)] for i in range(n - 1)]  # basis of ker eps
        cols = [[sum(M[r][c] * k[c] for c in range(n)) for r in range(n)] for k in K]  # M k_i
        # coordinates in basis K of a vector v with sum 0: first n-1 entries
        R = [[cols[i][r] for i in range(n - 1)] for r in range(n - 1)]
        d = snf(R, n - 1, n - 1) if n > 1 else []
        out[f"alpha_alphadag_{tag}"]["index_on_ker_eps"] = prod(d) if len(d) == n - 1 else 0
    # cuspidal (non-Eisenstein) T_q eigenvalues: (q+1)^2 - lam^2 is the determinant of alpha alpha^dagger on that eigenspace
    lam = [x for x in out["T_q_eigenvalues"] if x != q + 1]
    out["cusp_det_q1sq_minus_lam_sq"] = [(q + 1) ** 2 - x * x for x in lam]
    # (b) Eisenstein vector v = ker alpha^dagger (f0 = f1 = L/w_x, primitive); coker on the quotient Z[X]^2/Z v, and the
    # form b(f,g) = <alpha alpha^dagger f, g>_w on W = weighted-orthogonal complement of v (= ker eps), coker W -> W^vee
    from math import gcd, lcm
    for tag, wt in (("weighted", True), ("unweighted", False)):
        M = alpha_alphadag(T, wt)
        w = list(T.w_v) if wt else [1] * X
        Lm = lcm(*w)
        v = [Lm // x for x in w] * 2
        g0 = gcd(*v)
        v = [x // g0 for x in v]
        assert all(sum(M[r][c] * v[c] for c in range(n)) == 0 for r in range(n))
        d = snf([M[r] + [v[r]] for r in range(n)], n, n + 1)
        K = [[(1 if j == i else 0) - (1 if j == n - 1 else 0) for j in range(n)] for i in range(n - 1)]
        W2 = w + w
        assert all(sum(W2[c] * v[c] * k[c] for c in range(n)) == 0 for k in K)  # W = ker eps
        Bf = [[sum(W2[r] * ka[r] * sum(M[r][c] * kb[c] for c in range(n)) for r in range(n)) for kb in K] for ka in K]
        db = snf(Bf, n - 1, n - 1)
        out[f"alpha_alphadag_{tag}"].update({
            "eisenstein_vector": v, "coker_on_quotient_by_Eis_saturation": prod(d),
            "coker_W_to_Wdual_order": prod(db) if len(db) == n - 1 else 0})
    out["acceptance_note"] = (
        "Literal coker(alpha alpha^dagger) on Z[X]^2 is Z + Z/3 (weighted) and Z (unweighted) for B11,q=2, not 5. "
        "The plan's 5 is realised only as (a) det of alpha alpha^dagger on the cuspidal T_q-eigenspace (q+1)^2 - lambda^2 = 9-4 = 5 "
        "and as |Phi^comb| of the collapsed two-vertex graph (weights 2,1,1). The other readings do NOT give 5: coker on the quotient "
        "by the Eisenstein saturation = 30 (weighted) / 4 (unweighted); coker of W -> W^vee on the weighted-orthogonal complement "
        "W = ker eps = 1800 (weighted) / 16 (unweighted). Flagged for prop:s03-LRdef / WP M2 to pin down the intended object."
    ) if (D, q) == (11, 2) else None
    out["phi_collapsed_order"] = out["phi_comb_collapsed"]["order"]
    return out


def main() -> None:
    with results.Timer() as t:
        data = {f"B{D}_q{q}": collapse_case(D, q) for D, q in CASES}
    results.write("s03/T2.json", data, script="langlandscape.ribet.collapse", params={"cases": CASES},
                  runtime_s=t.seconds, notes="S03-C3: collapse of BG(Ohat^x,q); alpha alpha^dagger weighted/unweighted; sign check")
    for k, v in data.items():
        print(k, v["n_edges_X_Uprime"], v["rk_H1"], v["T_q_eigenvalues"], v["alpha_alphadag_weighted"]["torsion_order"],
              v["alpha_alphadag_unweighted"]["torsion_order"], v["phi_comb_collapsed"]["order"])


if __name__ == "__main__":
    main()
