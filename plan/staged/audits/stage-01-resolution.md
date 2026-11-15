# Stage 01: resolution of the Muse audit

| F | Title | Verdict | Reason | Change |
|---|---|---|---|---|
| F1 | `8` in unit orders | PARTIALLY CONFIRMED | Voight Thm 11.5.14 (p.176): order 8 is the Lipschitz order, non-maximal, only D=2. `O_x` is maximal, so `{2,4,6,12,24}`. Muse's claim that 8 arises for non-squarefree Eichler levels / `U_0(N)` is false (`Γ_x` is always inside a maximal-order unit group). "Divides 24" unaffected. | `prop:s01-finite` statement and import remark corrected |
| F2 | det step in Lemma stab (b) | PARTIALLY CONFIRMED | Not a gap: eigenvalue 1 is a root of `X^2-tX+1` (already used), giving `t≡2`. Muse's derivation via `a≡1` is unnecessary. One clarifying clause added. | `lem:s01-stab` proof (b) |
| F3 | `-1` hypothesis for `ν∘π_*` | CONFIRMED | Re-derived: `tr(w_{x'}1_{x'})=w_{x'}[Γ_x:Γ_{x'}]1_x`, equals `w_x 1_x` iff `-1∈U'` or `-1∉U`; hypothesis missing in Prop (c) statement and in interfaces. Muse's fix is wrong in two details: the case `U=Ô^×`, `U'=U_1(N)` is the *failing* one, and the factor is `tr∘ν'=2ν∘π_*` (not `ν∘π_*=2tr∘ν'`). | `prop:s01-adjoint`(c), `if:s01-brandt`, `if:s01-mass` |
| F4 | `N_{U_p}`, index claims | PARTIALLY CONFIRMED | No error; deviation (iii) already recorded. Muse's index `[K_s:K_{s+1}]=p^3` is wrong (it is `p^2`); the stage's "size `p^3`" (=`p·p^2`) is right. Added the explicit computation. | `lem:s01-Up` proof |
| F5 | `Q_p` vs `Z_p` scope of dictionary | PARTIALLY CONFIRMED | Already stated in Remark and R5; but not in Dependencies/L4. Added scope sentence and L4 caveat (not for `U_p`). No interface content change. | Dependencies, Lean L4 |
| F6 | status split of `\|S_s\|` | REJECTED | Statuses are already separated in Thm mass (c) second half / (d); the proposed split mislabels them. `if:s01-mass` "including" is a stated strengthening. | no change |
| F7 | citations | REJECTED | No defect claimed ("no fix needed"); spot-checks of Voight pages fine. | no change |
| F8 | feasibility; `s≥1` bound in L3 | CONFIRMED (trivial) | Assessment fine; `s≥1` note added to L3. | Lean L3 |

Total 8; confirmed 2 (F3, F8); partially 4 (F1, F2, F4, F5); rejected 2 (F6, F7).
Overall: moderately useful: one real issue (F3), one real imprecision (F1), but several wrong supporting computations (F1, F3, F4); verify before applying.
Interface deviations: none new (F3 adds a hypothesis to existing statements; noted in the text).
