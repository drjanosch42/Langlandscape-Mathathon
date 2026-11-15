# HACS answers for the Jacquet-Langlands feasibility project

Written 2026-11-13 by an agent of the HACS project (repository `orbifold-cohomology-of-gl2`, branch `hecke-extensions`).
Only shipped HACS capabilities were used: no HACS source was changed, nothing was rebuilt.

- **Binary:** `hacs 0.2.0 (commit 5bd706911c89; contract [C] 1.27.0, [E] 1.25.3, [U] 0.8.1)`, the slot-27 reference build,
  sha256 `0629ad13428172fa9b61b3b2aa66b870db24727f381e5418484b62475c206e8a`
- **Repository tip when the work was done:** `8f5e0fa1` (the binary was built from `5bd70691`).

## Status, one line per task

| Task | Status | Where |
|---|---|---|
| 0(i) anchor: D = 3, k = 12, l = 17 | **done**. C_T(3-old, 3-new) at 17 is **Z/17**: certified by HACS, with a one-line index argument. Eigenvalues mod 17 and the Jordan structure of U_3 are in the results. | `task0_inscope/results.md` §1 |
| 0(i) grid: D in {3,5,7,11,13}, k = 4..14 | **partial**. All 30 cells were computed over Z. For the old-versus-new congruence module of the *anemic* Hecke algebra we give an exact upper bound at every prime. At k = 12 every prime l > k with l ∤ D is settled exactly as Z/l, with a certified lower bound read from the HACS records. For k ≠ 12 in the range there are no old cusp forms, so only Eisenstein-versus-new congruences exist; for those we give the upper bound, and HACS's certified Eisenstein C_T where its record has one. With U_D included (the full algebra) the congruence module over Z is computed **only** at the anchor. | `results.md` §2 |
| 0(ii) p-ordinarity and ordinary ranks | **partial**. Δ and g are classified for p = 5, 7, 11, 13. Ordinary ranks at level 3 for k ≤ 62 come from exact char_Z(T_p); at level 3p we use Hida's stabilisation theorem (cited, not computed). The mod-17 persistence test along k = 12 + (p-1)j: we have a certified "no" at k = 16, 18, 20 and 22, and a necessary-condition "yes" at k = 24. U_p at level 3p^r is **not** reachable with shipped HACS. | `results.md` §3 |
| 1 (v6 request): SL_2(Z[1/p]) amalgam, Mayer-Vietoris with Sym^{k-2} | **done** (anchors + grid p <= 13, k = 4..14; extension k <= 24); Tasks 2, 3 of v6: not started (feasibility only) | `task1_v6/README.md` |
| A-D (GL_2(B), Spin(4,1) = Sp(1,1)) | **withdrawn: feasibility only** (below) | this file |

## Feasibility: the withdrawn new-group tasks (no implementation; a judgement, not verified)

HACS is built around one fixed cell model: the 7-vertex triangulation of a fundamental domain of SL_2(Z) on the upper
half-plane, together with its 8 + 23 gluing/stabiliser relations ([C] def:model7, def:model7rel). On top of that model sit
three things:

- Shapiro induction, which reaches the finite-index subgroups Γ_0(N), Γ_1(N) and (Γ_0(N), χ) ([C] def:levelNmodel, sec:nebentypus).
- Hecke operators, either through τ-chain data on that model ([C] def:hecke) or through the Manin-Merel Heilbronn matrices ([C] prop:heilbronn).
- Exact or modular linear algebra on top of these.

The arithmetic groups of the withdrawn tasks are not commensurable with SL_2(Z), so Shapiro induction does not reach them:

- GL_2(R) for an order R in a quaternion algebra B acts on hyperbolic 5-space (SL_2(H) ≅ Spin(5,1)).
- Γ ⊂ Sp(1,1) ≅ Spin(4,1) acts on hyperbolic 4-space.

Some HACS layers are model-agnostic and would carry over:

- the equivariant cochain complex of a finite complex K with a relation set (pairs of simplices and a group element) and a local system;
- the sparse mod-l / Z/l^k elimination, and the integral descent machinery (fracture square, CRT over l);
- the record and certificate formats.

A port would need new work in four places:

1. **A Γ-cell model.** This means a fundamental domain, or a Γ-equivariant retract (well-rounded/Voronoi-type, or a Ford domain), for the action on H^5 or H^4. It must come with:
   - exact face pairings;
   - finite cell stabilisers. Quaternion units bring finite subgroups beyond orders 4 and 6, so the "6 invertible" hypothesis of the current comparison theorems would have to become "the stabiliser orders are invertible".
   - The cell counts are probably in the hundreds to low thousands for small discriminants. That is not verified; it is extrapolated from published Bianchi/Swan-type computations in dimension 3.
2. **Integral matrices of the coefficient systems.** These are algebraic representations of GL_2(B ⊗ R) ≅ GL_4-type groups, realised over a splitting field or at primes l where B splits.
3. **Hecke operators.** We would need double-coset representatives in the commensurator and a cellular τ-type datum, or a Heilbronn-type formula. Both are model-specific in HACS and would have to be redone. This is the costliest part.
4. **Validation oracles.** For example Jacquet-Langlands transfers to GL_2 or Sp_4 forms computed elsewhere.

Once a model exists, the linear algebra is small (number of cells × representation dimension), so arithmetic is not the bottleneck; the geometry is.

Rough cost by analogy with the project's own history (the SL_2(Z) model, its level-N layer and the Hecke layer each took several
multi-week slots): a cell model with validated H^* is a multi-slot project, and Hecke operators are a comparable second project.
This is an order-of-magnitude estimate, not a plan.

## Files

`task0_inscope/results.md` (the answers), `run_log.md` (commands, wall, RSS), `data/` (raw HACS outputs as JSON per cell,
`grid_table.md`, `congruence_modules.json`, `record_lower_bounds.json`, `ordinary_family.json`, `family_charpolys.txt`, anchor raw
outputs), `scripts/` (the OC scripts and the Python drivers/analysis; Python 3.10 + sympy 1.14 for exact linear algebra and factoring
checks only).
