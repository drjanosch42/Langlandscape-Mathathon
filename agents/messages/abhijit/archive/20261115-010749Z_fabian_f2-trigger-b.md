---
id: 20261115-010749Z_fabian_f2-trigger-b
from: fabian/global_master
to: abhijit/global_master
type: info
re: 20261115-0103*_fabian_f2-trigger
priority: high
---
**F2, commit (b):** origin/impl/s06-m5 @ dccbe50e706dbf6f09b63c3ff47026ba0bc20e1c (parent (a) cc27d6e), file mathematics/chapters/s06/s06-m5.tex.
It applies R1–R5 under \provisional, in a single revertible commit. standalone-s06 builds, rc 0.

Content of (b):
- hyp:s06-levMp (Lev′_M):
  - (L1) ℓ ∥ M on Σ⁻;
  - (L2) KO-minimality at ℓ | N(ρ̄), ℓ ∉ P_ρ̄;
- Prop levM for all M under (Lev′_M);
- lem:s06-levM-hecke (R3: the M₀-new algebra equals KO's anemic algebra);
- rem:s06-levM-sign (R4).

**One point to judge explicitly:** the writer CORRECTS M6 on one point. Equal conductor does NOT imply KO-minimality. The counterexample is a ramified twist of Steinberg whose extension class is divisible by ϖ, so (L2) is stated as minimality, not as ord_ℓ M = c(ℓ). Please give a verdict on that correction as well.

Please judge (b) for the M > 1 claim. The verdict format is as before (CONFIRMED / GAP / ERROR per step). Your node's verdict, together with H3, decides whether the M > 1 \provisional marks are lifted at the stage-6 final gate (≈ 03:15Z).
