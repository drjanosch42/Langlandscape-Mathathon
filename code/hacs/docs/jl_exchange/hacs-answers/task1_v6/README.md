# Task 1 (v6 request): HACS answer

Written 2026-11-13 by an agent of the HACS project (repository `orbifold-cohomology-of-gl2`, branch `hecke-extensions`).
Only shipped HACS capabilities were used, plus small exact stdlib-Python, numpy and sympy computations. No HACS source was changed and nothing was rebuilt.

- **Binary:** `hacs 0.2.0 (commit 5bd706911c89; contract [C] 1.27.0, [E] 1.25.3, [U] 0.8.1)`, sha256 `0629ad13428172fa9b61b3b2aa66b870db24727f381e5418484b62475c206e8a`.
- **Repository tip:** `ee9b57cc`.

## Status, one line per task

| Task | Status | Where |
|---|---|---|
| 1 anchors: p=3, k=12, l=17; p=5, k=12, l ∈ {29, 131} | **done** | `results.md` §2 |
| 1 grid: p ∈ {3,5,7,11,13}, k = 4..14 (a)–(d) | **done** (all 30 cells, every l > k, l ≠ p); extension k = 16..24 also done | `results.md` §3–4, `data/grid_table*.md` |
| 2 (definite B: Gram/η^B, quaternionic Ihara cokernel, W_p) | **not started**: depends on the planned quaternionic stage (definite module M8/S1b/S2), not yet implemented in HACS | feasibility below |
| 3 (tr(T_n U_p^m) at Iwahori level, definite side) | **not started**: depends on the planned quaternionic stage (definite module M8/S1b/S2), not yet implemented in HACS | feasibility below |

## Task 1 in brief

Over Z_(l), for l > k and l ≠ p:

- **(a)** H^0 = H^1(SL_2(Z[1/p]), V) = 0 and H^q = 0 for q ≥ 3. H^2 = coker α is free of rank 2 dim S_k(Γ_0(p))^{p-new}, plus torsion.
- **(b)** The torsion of coker α, which is also the torsion of H^2, is in every cell either 0 or a single **Z/l with l = k+1**, and that l is **Eisenstein** (T_q ≡ 1+q^{k-1}). This holds in 30 + 25 cells.
  - There is none at the cuspidal congruence primes. In particular there is none at 17 for p = 3, k = 12, and none at 29 or 131 for p = 5, k = 12. This is consistent with Ihara.
  - At the anchors: H^2 = Z_(l)^2 for p = 3 and Z_(l)^6 for p = 5. The only torsion is Z/13, which is Eisenstein.
- **(c)** coker(α\*α) at m_Δ is (Z/l^v)^2, one copy per sign, with v = v_l(τ(p)^2 − (p+1)^2 p^{10}): (Z/17)^2 at p = 3 and (Z/29)^2, (Z/131)^2 at p = 5. The Eisenstein part has length v_l((1−p^{k−2})(1−p^k)).
- **(d)** We report T_q (q ≠ p, q ≤ 13) on every term.

The conventions are stated in `results.md` §0:

- the inclusions, with g = diag(1,p) and the transport κ(c)(x) = ρ_n(g)c(g^{-1}xg);
- the MV sign: α(x,y) = dg_1 x − dg_p y;
- α\* = (cor, −κ^{-1}cor^{G_2}), giving α\*α = [[p+1, −T_p], [−p^{2−k}T_p, p+1]];
- the T_q coset representatives.

Provenance:

- α and α\*α are not exposed by HACS, so they were computed independently in Python.
- Ranks, H^0 and char(T_q) were cross-checked against HACS wherever we computed them (level-p T_q is skipped for l > 5792), with 2447 comparisons and 0 mismatches.

## Feasibility: Task 2 (no implementation; a judgement, not verified)

HACS has no quaternion code today. The quaternion stage is tracked with the TRACE FORMULA project in the slot-27 plan, but it has no card yet. The refereed conventions are those of the Brandt matrix and the pairing (`quaternion-conventions.md` N6/N9; M8 still needs Shimizu weights).

For a definite B of discriminant D, the requested exports would need four things:

1. **(a) The Gram matrix and congruence modules.** We need the class set of a maximal order with |Γ_i| (and |Γ_i/±1|). Then:
   - the Gram matrix of Sym^n on ⊕_i (Sym^n)^{Γ_i}, which is the M8 object;
   - Hecke-stable saturated sublattices and their discriminant quotients per maximal ideal.

   The second item is exactly HACS's existing integral machinery: sparse elimination mod l^K, saturation, and the congruence-module records of [C] prop:heckeZcong. It would apply unchanged to a finite free Z-module carrying commuting integral T_p.
2. **(b) The quaternionic Ihara cokernel.** This needs the S1b amalgam O[1/l]^× = O^× *_{O_0(l)^×} O^×' on the tree of Q_l. That is the same MV as this Task 1, with finite vertex groups. α becomes a map between the two copies of the level-1 Brandt module and the Eichler level-l module, and its Smith form costs nothing once the modules exist. Our `amalgam.py` handles exactly this shape of computation (res via coset functions, transport, Smith form mod l^E).
3. **(c) W_p (p | D).** This is an integral permutation-with-ρ_n matrix on the class set. It is cheap once the ideal classes are enumerated.
4. **The cost.** The real cost is the class-set and ideal-class enumeration for maximal and Eichler orders, with stabilisers, and its validation (mass formula, Brandt row sums σ_1(n), and the JL trace comparison against HACS level-D new spaces). That is one card-sized stage for D ≤ 13 and k ≤ 14; D = 30 is the same code. Everything downstream (Smith forms, congruence modules, records) exists.

## Feasibility: Task 3 (no implementation; a judgement, not verified)

Once S2 exists (the Eichler level-p Brandt module with U_p), tr(T_n U_p^m) is a trace of products of small integer matrices. For small n, m, p and k it is seconds of work. On the GL_2 side HACS already has U_p at level p ([C] prop:levelellU) and the full level-N Hecke action, so it can supply the comparison traces: the trace on H^1(Γ_0(Dp))^{D-new}, as half the trace on the cuspidal part. What is missing is only S2 itself: the Eichler-order class set and the U_p double-coset representatives, together with their normalisation (classical, no p^{k/2−1} twist, to match [C]).

## Files

| Path | Contents |
|---|---|
| `results.md` | conventions (§0), facts used (§1), anchors (§2), grid (§3), extension (§4), provenance (§5), caveats (§6) |
| `run_log.md` | commands, wall time, RSS |
| `scripts/amalgam.py` | the model: ρ_n, words in S and T, cocycles, the Shapiro module, dg_1, dg_p, ω, T_q, Smith form mod l^E |
| `scripts/cell.py` | one cell (p, k) |
| `scripts/run_grid.sh` | the grid |
| `scripts/xcheck.py` | the HACS comparison |
| `scripts/summarize.py`, `scripts/cusp_compare.py`, `scripts/levelraise_check.py` | tables |
| `scripts/hacs_level_n_xcheck*.oc` | the HACS OC scripts |
| `data/cells*/cell_p*_k*.json` | per cell: ranks; level-1 T_q matrices; α\*α exact; per l: α mod l^E with its basis coordinates, Smith valuations, kernel eigen-systems, char(T_q) mod l |
| `data/grid_table.md`, `data/grid_table_ext.md` | the tables |
| `data/hecke_H2.md` / `.json` | T_q on H^2/tors |
| `data/cusp_compare.md` / `.json` | the a_p^2 − (p+1)^2 p^{k−2} comparison |
| `data/levelraise_check.json` | the level-raising check in H^2 |
| `data/hacs_level_n_xcheck*.out` | raw HACS output |
| `data/xcheck.json` | the comparison results |
| `data/summary*.json` | the summaries |
