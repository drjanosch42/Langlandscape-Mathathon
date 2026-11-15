<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# S03-M7: second reader / WP audit of S03-M4 (exponent chain) and of the S03-M5 normalisation table

- **Targets:** `mathematics/chapters/s03/4-ihara.tex` (M4: `ss:s03-conv` (C1)–(C6), (R1)–(R4), `lem:s03-unfold`,
  `lem:s03-adjoint`, `thm:s03-iharaH0`, `rem:s03-pm`, exponent table, `cor:s03-eis`, `rem:s03-T6`, (D1)–(D4));
  `mathematics/chapters/s03/5-amalgam.tex` (M5: `prop:s03-PsiPsi` and its normalisation table).
- **Checked against:** `def:s01-hecke`, `prop:s01-adjoint`, `rem:s01-nu-hecke`, `prop:s01-relations`, `def:s01-pairingV`,
  `lem:s01-dictionary` (`mathematics/chapters/s01/{3-brandt,4-hecke,5-conventions}.tex`); `def:s02-Mhom`, `prop:s02-Mhomprops`,
  `prop:s02-coh`, `def:s02-indef` (Hecke action, `if:s02-indef`), `prop:s02-quot`(c) (`mathematics/chapters/s02/{2-quotient,3-cohomology}.tex`);
  `plan/implementation/stage-03.md` §0.2 item 8; `plan/staged/stage-03-ribet-ihara.tex`; [DT94] pp. 439–446; the remote package
  report `agents/messages/fabian/20261114-200940Z_abhijit_p3-s03-math-report.md` (its claims were checked, not trusted).
- **Date:** 2026-11-14. **sha:** 7ac603f. (The worktree HEAD is b25c187. `4-ihara.tex` and `5-amalgam.tex` are unchanged
  between the two; `3-ribet.tex` (M3 fix) has changed. `cor:s03-ihara`(ii′), which M4 uses in (a4), was read at HEAD.)
- **Method:** every step was recomputed from the definitions, not from the M4/M5 text. Scratch checks (sympy, kept outside the repo):
  (i) the Ψ*Ψ matrix identities (`α'^{-1}=q^{-1}α'^ι`, `γ₁α'γ₂^{-1}=α'^ι`, the scalar `λ` acting on Sym^{k−2} as `λ^{k−2}`,
  `α'^{-1}Γα' ∩ Γ`); (ii) the Z_p-coinvariants `(Sym^{k−2}Z_p^2)_{SL₂(Z_p)}` for p∈{5,7}, k≤2p+2, via Smith normal form;
  (iii) the mod-p coinvariants under SL₂(F_p) and under the upper unipotent group (U₁(p)-level), with the characters of `diag(t,1)` on
  them, for n=k−2≤4p−1. Result (ii) agrees with stage 02's `code/results/s02/H_Vk.json` (`H0`: Z/5 at p=5, k=10; 0 for 3≤k≤10 at p=7).

---

## (R1) — CONFIRMED
`4-ihara.tex:71-75`. For g supported away from p, the cohomological operator of `def:s01-hecke`, `(T_g f)(x)=Σ g_{i,p} f(xg_i)`,
has all g_{i,p}=1 (the representatives factor, `4-hecke.tex` "Factorisation"). So it is (C4). An independent recomputation of `ε∘S_ℓ`
gives `f(xz_ℓ)=f(xy)=y_p^{-1}f(x)`, with `y=ℓ^{-1}z_ℓ∈U`, `y_p^{-1}` the scalar ℓ, and `det=ℓ²`. This yields `[ℓ²]`, which equals
`ℓ^{k−2}` on V_k by `eq:s01-Vk`. This matches `prop:s01-relations`(a) at level `U₀(M)·GL₂(Z_p)`.

## (R2) — CONFIRMED
`4-ihara.tex:76-82`. The trivial-coefficient statements (`prop:s01-adjoint`(a)–(c), `rem:s01-nu-hecke`) are quoted correctly.
Consistency with the Gross factor was recomputed. Put `Θ(h)(x):=τ(x)^n β_n(h(x),·)`, a map from `S(U,V_k)` to `S(U,V_k^∨)`. It is
U-equivariant by `def:s01-pairingV`(i) and (C5), and `⟨f,h⟩_k=⟨f,Θh⟩_U`. Since `τ(xg_i)=ℓ^{-m}τ(x)`, one gets
`T_gΘ=ℓ^{-mn}ΘT_g`. Lemma `lem:s03-adjoint`(c) then gives `⟨T_gf,h⟩_k=ℓ^{mn}⟨f,T_{g^{-1}}h⟩_k=r_g^n⟨f,T_{g^{-1}}h⟩_k`. This is
exactly `lem:s01-dictionary`(d), so the two statements are consistent, as claimed.

## (R3) — CONFIRMED (one omission, see M7.3)
`4-ihara.tex:83-91`. Checked:
- ∂=(−s_{0*},s_{1*}) with 0→1 orientation (`prop:s02-coh`(b)) agrees with (C1).
- `ν∂ν'^{-1}=(−tr₀,tr₁)=α` follows from `prop:s02-Mhomprops`(d).
- The homological operator `[x]⊗v↦Σ[xg_i]⊗v` is well defined on `Z[B^×\B̂^×]⊗_{Z[U]}V` (recomputed: `ug_i=g_{σ(i)}u_i` with
  `u_{i,p}=u_p`).
- Under ν that operator is `T_{g^{-1}}`, which is proved in `def:s02-indef` (`3-cohomology.tex:389-395`).
- Hence the exponent in the normative homological convention is −1 (recomputed through thm (b) applied to g^{-1}).

Omission: (R3) does not record what the normative convention does to S_ℓ. Its S_ℓ is ℓ^{2−k}, not the classical ℓ^{k−2} (M7.3).

## thm:s03-iharaH0(b) — CONFIRMED (one missing hypothesis, see M7.4)
`4-ihara.tex:169-174`, proof `224-236`. Recomputed independently:
- `τ(xug)=ℓ^{-m}τ(x)` (C5), so `[cτ(x)]=[ℓ^m][cτ(xug)]`.
- `y↦F_c(yg)` is right W-invariant, because `g^{-1}Wg⊆U` and F_c is right U-invariant (a1).
- Unfolding over W, transport `[y]↦[yg]` from X_B(W) to X_B(W'), and reverse unfolding over `W'=U∩g^{-1}Ug` give
  `ε∘T_g=[U:W'][ℓ^m]∘ε`.
- `[U:W']=deg(Ug^{-1}U)=deg(UgU)` (`lem:s03-adjoint`(d); the unimodularity argument via `Δ=δ∘det`, with δ trivial on squares and on
  Z_ℓ^×, is correct).

So T_ℓ↦(1+ℓ)[ℓ] and S_ℓ↦[ℓ]², with exponent +1. Toy check: for V=Z_p with U_p acting through χ∘det, the function
`f(x)=χ(τ(x))^{-1}` lies in S(U,V) and `T_ℓf=(1+ℓ)χ(ℓ)f`, again exponent +1. The duality cross-check (`241-244`: the transpose of [t]
on V^* is [t]^{-1} on V) was also recomputed and is right. Parts (a1)–(a4) and the unfolding lemma were re-derived and are correct.
Two details hold as written: ε uses `[qτ(x)]` on the f₁-summand because `τ(xα^{-1})=qτ(x)`, and in (a4)
`⟨v,[t]^{-1}φ⟩=φ([t]v̄)`.

## rem:s03-pm — CONFIRMED for the mathematics; the T6 testability sentence is wrong (M7.1, M7.2)
`4-ihara.tex:246-266`. Checked:
- `T_{g^{-1}}=S_ℓ^{-1}T_ℓ` acts on coker α as `(1+ℓ)[ℓ]^{-1}`, both via (b) for g^{-1} and as `[ℓ]^{-2}(1+ℓ)[ℓ]`.
- The ν-transport of the homological operator is right.
- The dual presentation is right: the transpose of T_ℓ on `H^0(V^∨)` is the adjoint's action on H_0.
- The DT formula on p. 446 is quoted correctly, and `‖det g‖^{2−k}=r_g^{k−2}` agrees with `lem:s01-dictionary`(d).

The closing claims (`252-253`, "HACS test T6 should confirm this for both normalisations") and the "Consistency" argument (`262-264`) are
**not discriminating in any computable case at maximal level at p**. See M7.1 and M7.2.

## Ψ*Ψ table (prop:s03-PsiPsi, 5-amalgam.tex:116-163) — CONFIRMED (no correction to stage-03.md §0.2.8)
Recomputed:
- The cocycle formulas agree: `c=c_{α'^{-1}}`, because `(c_gz)(h')=g z(g^{-1}h'g)` with g=α'^{-1} is the `(cz)(γ')` of `5-amalgam.tex:59`.
- (1,2) entry: `−cor^Γ_{Γ₀(Mq)}res^{Γ'}_{Γ₀(Mq)}c`. Since `res^{Γ'}c=c_{α'^{-1}}res^Γ_{α'Γ₀α'^{-1}}` and `Γ∩α'Γα'^{-1}={q∣b}=α'Γ₀(Mq)α'^{-1}`
  (sympy: `α'^{-1}Aα'=[[a,b/q],[qc,d]]`), this is `−T_{α'^{-1}}`.
- (2,1) entry: `−c_{α'}cor^{Γ'}res^Γ=−cor^Γ_{α'Γ₀α'^{-1}}c_{α'}res^Γ_{Γ₀}=−T_{α'}`.
- `α'^{-1}=q^{-1}α'^ι` and `γ₁α'γ₂^{-1}=α'^ι` with `aq−bM=1` (sympy: identity holds, both dets 1, both in Γ₀(M)). The scalar q^{-1}
  acts on Sym^{k−2} as q^{2−k}. Hence `T_{α'^{-1}}=q^{2−k}T_{α'^ι}=q^{2−k}T_{α'}`.
- So **the (1,2) entry carries q^{2−k}**: `Ψ*Ψ=[[q+1,−q^{2−k}T_q],[−T_q,q+1]]`, with `T_q=T_{α'}` acting through the integral α'. This is
  exactly §0.2.8, with the α'^{-1} argument as stated there.
- The seed matrix arises from Γ''=α'Γα'^{-1} and c_{α'} (rechecked).
- The two choices are conjugate by `diag(1,q^{k−2})`, so the cokernels are isomorphic.
- Passing to V^∨≅V⊗det^{2−k} (valid since l>k−2) rescales T_{α'} by q^{2−k} and T_{α'^{-1}} by q^{k−2}, so det is unchanged.

The table is consistent with (D4) and with `if:s03-amalgam`. The identification "T_{α'} = classical T_q" is correctly marked \stsketch.
Independently, a right-action (Hida/adjugate) operator for ΓαΓ, converted to a left action, is q^{k−2}·T_{α^{-1}}=T_α. That is
consistent with the claim, but C5/H1 should still confirm it numerically at k≥4.

---

## Further findings on M4

- **M7.1, major, `4-ihara.tex:309-311` (rem:s03-T6(c)).**
  - *Problem:* the prediction "H₀=0 for k≤p+1, an explicit Eisenstein action T_ℓ=(1+ℓ)[ℓ] for p+3≤k≤2p" is wrong in substance. Computed
    for p∈{5,7}:
    - `(Sym^{k−2}Z_p²)_{SL₂(Z_p)}` is 0 for every 3≤k≤2p+2 except k=2p, where it is Z/p.
    - Mod p, `(Sym^nF_p²)_{SL₂(F_p)}≠0` only for (p−1)∣n (n≤4p−1), and there it is one-dimensional with `diag(t,1)` acting
      trivially.

    So for p+3≤k<2p there is nothing to test. At k=2p the action is T_ℓ≡1+ℓ, and [ℓ]≡[ℓ]^{-1} mod p. This agrees with stage 02's
    `H_Vk.json`.
  - *Required fix:* replace (c) by "computed (S03-M7, to be reproduced by S03-C4): at U_p=GL₂(Z_p), H₀(Γ_U,V_k)⊗F_p≠0 only if
    (p−1)∣(k−2), and then the Z_p^×-action is trivial mod p". State the U₁(p)-level prediction (b) as the real test.
- **M7.2, minor, `4-ihara.tex:252-253` and proof `262-264` (rem:s03-pm).**
  - *Problem:* the sentence "HACS test T6 should confirm this for both normalisations" cannot be met at maximal level. Exponents +1 and
    −1 give the same operator whenever [ℓ]²=1 on H₀. By M7.1 this is the case in every non-zero maximal-level instance, and there
    `ℓ^{2(k−2)}−1` kills H₀ = Z/p, so the "Consistency" argument is vacuous exactly where it would apply.
  - *Required fix:* say that the exponent is proved by (b) and is only testable at U₁(p^s)-level, on a [·]-eigenline t↦t^a with
    2a≢0 mod (p−1). Mod-p data (S03-M7 scratch): p=5, k∈{7,9,11,12,...}; p=7, k∈{9,10,12,13,...}. Hand the concrete cases to S03-C4/T6.
- **M7.3, major, `4-ihara.tex:83-90` (R3), exponent table `268-278`, `if:s03-ihara:334`, (D1) `343-344`.**
  - *Problem:* the normative homological convention of `if:s02-indef` is non-classical in S_ℓ, and M4 never says so. Recomputed:
    `[xz_ℓ]⊗v=[xy]⊗v=[x]⊗y_pv` with `y_p=ℓ^{-1}` scalar. So S_ℓ^{hom}=ℓ^{2−k} on `S(U,V_k)_*`, and under ν it is `T_{z_ℓ^{-1}}=S_ℓ^{-1}`.
    In general the normative operators are the classical S_ℓ^{-1} and S_ℓ^{-1}T_ℓ, not S_ℓ and T_ℓ. M4 says both "only +1 is consistent
    with the classical S_ℓ" (`252`) and "the normative convention ... exponent −1" (`86-89`) without spelling out this consequence.
    Downstream comparisons with classical eigenvalues (HACS a_ℓ, S_ℓ=ℓ^{k−2}, stage 04/06) can silently pick up S_ℓ^{-1} twists.
  - *Required fix:*
    1. Add a column "S_ℓ on H₀" to the exponent table: [ℓ]² (= ℓ^{k−2} if U_p ⊇ scalars) cohomological; [ℓ]^{-2} (= ℓ^{2−k})
       homological.
    2. Add one sentence to (R3): in the normative convention, T_ℓ, S_ℓ act as the classical S_ℓ^{-1}T_ℓ, S_ℓ^{-1}, so classical
       comparisons must apply T↦T^† first.
    3. Raise this with the stage master as an interface note for stage 02/04 (no change to s02 in this WP).
- **M7.4, minor, `4-ihara.tex:169` (thm (b) statement) and `186`, `224`.**
  - *Problem:* the proof uses representatives of U/(U∩gUg^{-1}) with u_p=1 ("the groups agree away from the support of g") and
    `prop:s02-quot`(c). Both need U=U_ℓ×U^{(ℓ)}, which `prop:s02-quot`(c) states as an explicit hypothesis. The standing hypotheses
    (`97-100`) only give factorisation at p and q-admissibility. `lem:s03-adjoint`(c) does state it (`126`).
  - *Required fix:* add "and U=U_ℓ×U^{(ℓ)} (true for standard levels)" to (b), or to the standing hypotheses.
- **M7.5, minor, `4-ihara.tex:349-352` (D4) vs `5-amalgam.tex:207-211` (if:s03-amalgam).**
  - *Problem:* (D4) says the matrix "is exported only up to the choice between T'_q and T''_q". The interface exports the fixed matrix
    `[[q+1,−q^{2−k}T_q],[−T_q,q+1]]`.
  - *Required fix:* reword (D4): the fixed matrix is exported (normalisation §0.2.8), and stage 06 should still use only det and coker.
- **M7.6, minor, `4-ihara.tex:91`, `174` (\provisional F9 notes).**
  - *Problem:* these are stage-tex carry-overs whose content is now settled by the exponent table.
  - *Required fix:* resolve or remove them in the fix round, per the chapter-audit rules.

## Further findings on M5

- **M7.7, minor, `5-amalgam.tex:120`.**
  - *Problem:* "T'_q and T''_q are the double-coset operators of Γα'Γ, acting on V through α'^{-1} resp. α'" is inaccurate. T'_q=T_{α'^{-1}}
    is the operator of the double coset Γα'^{-1}Γ = q^{-1}·Γα'Γ, not of Γα'Γ.
  - *Required fix:* "T'_q is the operator of Γα'^{-1}Γ=q^{-1}Γα'^ιΓ (acting through its elements), T''_q that of Γα'Γ".
- **M7.8, minor, `5-amalgam.tex:121-123` (statement of prop:s03-PsiPsi).**
  - *Problem:* the proposition statement stays noncommittal ("which one is which depends on ..."), while the acceptance asks for the
    table to be stated once and equal to §0.2.8.
  - *Required fix:* state the fixed result in the proposition, `T'_q=q^{2−k}T_q, T''_q=T_q` for V=Sym^{k−2} (column). Move the "other
    choice" sentence into the remark after the table.

**Counts:** critical 0, major 2 (M7.1, M7.3), minor 6 (M7.2, M7.4–M7.8).
