# Resolution of the S01-M7 audit (`2026-11-14_s01.md`) — S01-M8

CLOSED = applied as proposed; DEFERRED = left for the stage master. No `\label` added or removed.

- M7.1 CLOSED: `2-mass.tex` thm (b) and `4-hecke.tex` interface box now state `2 Σ_{X_B(U')} 1/w = [U:U'] Σ_{X_B(U)} 1/w` (with `\lean{massW_level_change_two}` in (b)).
- M7.2 CLOSED: `1-classsets.tex`, example `U_0(q)U` only when `-1 ∈ U`.
- M7.3 CLOSED: `6-targets.tex`, stale `\sttoprove` replaced by pointer to `lem:s01-Upconv` / `rem:s01-Upconv`, S01-C6.
- M7.4 CLOSED: `s01.tex`, skeleton sentence deleted.
- M7.5 CLOSED: `1-classsets.tex`, `Δ_s` defined for `s ≥ 1`.
- M7.6 CLOSED: `1-classsets.tex`, compactness of `U·⟨δ_d⟩` argued via open subgroup of compact group.
- M7.7 CLOSED: `1-classsets.tex`, `K_1(p)` replaced by `ι_p(U_p) ⊆ ι_p(U_{1,p})`; table header now mentions `d ≡ 1`.
- M7.8 CLOSED: `1-classsets.tex`, hat notation defined at the end of `def:s01-B`.
- M7.9 CLOSED: `2-mass.tex`, `p ∤ D` added to (d).
- M7.10 CLOSED: `2-mass.tex`, class number formula marked "for `D` prime and level 1".
- M7.11 CLOSED: `3-brandt.tex`, `ν_V` formula corrected (`x_p^{-1}γx_p`, sum over `Γ_x/(Γ_x∩{±1})`).
- M7.12 CLOSED: `3-brandt.tex`, example with `ε/ε' = 1` (`D=2`, `U_0(3)`) appended.
- M7.13 CLOSED: `4-hecke.tex`, auxiliary prime `q` introduced at `ℓ ∤ DMpq`.
- M7.14 CLOSED: `4-hecke.tex`, `x ↦ η_p·f(xη_p)`.
- M7.15 CLOSED: `4-hecke.tex`, hypothesis `U^{(p)} = U_1(M)` added at both places.
- M7.16 DEFERRED (stage master, after C-track merge): status upgrade to `\stcomp` citing `up.json`.
- M7.17 CLOSED: `4-hecke.tex` `rem:s01-diamond`, Buzzard citation reworded (`\stknown`, compare; precise comparison in `lem:s01-Upconv`(a)).
- M7.18 CLOSED: `5-conventions.tex`, left/right cosets swapped to the correct terminology; `p^n` factor added in the Buzzard remark.
- M7.19 DEFERRED (stage master, after C-track merge): C6 result `\stcomp`.
- M7.20 CLOSED: `5-conventions.tex`, diamonds at primes dividing `M` trivial.
- M7.21 DEFERRED (stage master): `\leanplanned` -> `\stformal` needs the merged sorry-free Lean declaration list.
- M7.22 CLOSED: `preamble.tex`, `\lit` typesets in `\ttfamily` with `\hyphenchar\font=`\-` (stems break at hyphens and underscores; interface unchanged; overfull boxes 34 -> 14). The 4 `\textlangle` bibliography warnings are harmless and left (`references.bib` not in scope).

S01-M9 (deferred items):
- M7.16 CLOSED: `4-hecke.tex` both places now `\stcomp` (S01-C5, `code/results/s01/up.json`, $B_3$, $p=5$, $s=1,2$; $U_5$ on $S_1$ has eigenvalues $5,1$).
- M7.19 CLOSED: `5-conventions.tex` C6 result `\stcomp` (`code/results/s01/up_mf.json`): $N_{U_p}$ on $\mathbb Q[S_s]$ = $a_5$ on $S_2(3\cdot5^s,\chi)^{3\text{-new}}$ plus 5 on the Nrd line, $s=1$ (level 15, dim $2=1+1$), $s=2$ (level 75, dim $50=1+49$); $N_{U_p}\leftrightarrow U_5$, adelic $\langle d\rangle$ = classical $\langle d\rangle^{-1}$, $U'_p$ = adjoint $U_5^*$.
- M7.21 CLOSED: all 17 `\leanplanned` markers (in 1-classsets, 3-brandt, 4-hecke, 5-conventions, 6-targets) switched to `\stformal`; every `\lean{}` name checked against `lean/Langlandscape/Langlandscape/**`: all exist, no name mismatches. `Hyp.JLClassical`, `Hyp.LambdaJL` exist as schematic interfaces (text kept saying so). No `\leanplanned` remains.
