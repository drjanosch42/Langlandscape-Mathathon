/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Admissible
import Langlandscape.Hyp.RamNrdSurjDischarge

/-!
# The `Hyp.RamNrdSurj` consumers with the registered hypothesis discharged (submission bundle)

`Hyp.RamNrdSurj d` (`lem:s01-nrd`, ramified part) is discharged by `Langlandscape.Hyp.ramNrdSurj_holds d`
(`Hyp/RamNrdSurjDischarge.lean`). The consumers keep the explicit argument `hram`; this file plugs the discharge in.

Covered (each declaration is named `<name>_uncond`, in the namespace of the original):
* `Quat/LevelNrd.lean` (`lem:s01-nrd`): `nrdSurj_Ohat`, `nrdSurj_U0`, `nrdSurj_U1`, `nrdSurj_Utower`;
* `Tree/Admissible.lean` (`def:s02-GU`): `isQAdmissible_Ohat`, `isQAdmissible_U0`, `isQAdmissible_U1`,
  `isQAdmissible_Utower`.

The `Hyp.PadicOrdDecomp` consumers already have their `_uncond` twins in `Ordinary/TowerUncond.lean`.

## Status

*formalized*, free of registered hypotheses: no `Hyp.*` argument remains; the remaining explicit hypotheses
(coprimality `hN`, `hqN : ¬ q ∣ N`) are unchanged.
-/

set_option autoImplicit false

namespace Langlandscape.Quat

variable {d : DefiniteData}

/-- `lem:s01-nrd` (`s01-nrd`): form of `nrdSurj_Ohat` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (none) are unchanged:
`nrd(Ô^×) ⊇ Ẑ^×`. -/
theorem nrdSurj_Ohat_uncond : NrdSurj d d.Ohat :=
  nrdSurj_Ohat (Hyp.ramNrdSurj_holds d)

/-- `lem:s01-nrd` (`s01-nrd`): form of `nrdSurj_U0` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (the coprimality `hN`) are unchanged:
`nrd(U_0(N)) ⊇ Ẑ^×`. -/
theorem nrdSurj_U0_uncond (N : ℕ) (hN : N.Coprime d.D) : NrdSurj d (d.U0 N hN) :=
  nrdSurj_U0 (Hyp.ramNrdSurj_holds d) N hN

/-- `lem:s01-nrd` (`s01-nrd`): form of `nrdSurj_U1` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (the coprimality `hN`) are unchanged:
`nrd(U_1(N)) ⊇ Ẑ^×`. -/
theorem nrdSurj_U1_uncond (N : ℕ) (hN : N.Coprime d.D) : NrdSurj d (d.U1 N hN) :=
  nrdSurj_U1 (Hyp.ramNrdSurj_holds d) N hN

/-- `lem:s01-nrd` (`s01-nrd`): form of `nrdSurj_Utower` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (the coprimality `hN`) are unchanged:
`nrd(U_s) ⊇ Ẑ^×` for the tower `U_s = U_1(M p^s)`. -/
theorem nrdSurj_Utower_uncond (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D) :
    NrdSurj d (d.Utower M p s hN) :=
  nrdSurj_Utower (Hyp.ramNrdSurj_holds d) M p s hN

end Langlandscape.Quat

namespace Langlandscape.Tree

open Langlandscape.Quat

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}

/-- `def:s02-GU` (`s02-GU`): form of `isQAdmissible_Ohat` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (none) are unchanged:
`Ô^×` is `q`-admissible. -/
theorem isQAdmissible_Ohat_uncond : IsQAdmissible d q hq d.Ohat :=
  isQAdmissible_Ohat (Langlandscape.Hyp.ramNrdSurj_holds d)

/-- `def:s02-GU` (`s02-GU`): form of `isQAdmissible_U0` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (`hqN : ¬ q ∣ N`) are unchanged:
`U_0(N)` is `q`-admissible for `q ∤ N`. -/
theorem isQAdmissible_U0_uncond {N : ℕ} {hN : N.Coprime d.D} (hqN : ¬ q ∣ N) :
    IsQAdmissible d q hq (d.U0 N hN) :=
  isQAdmissible_U0 (Langlandscape.Hyp.ramNrdSurj_holds d) hqN

/-- `def:s02-GU` (`s02-GU`): form of `isQAdmissible_U1` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (`hqN : ¬ q ∣ N`) are unchanged:
`U_1(N)` is `q`-admissible for `q ∤ N`. -/
theorem isQAdmissible_U1_uncond {N : ℕ} {hN : N.Coprime d.D} (hqN : ¬ q ∣ N) :
    IsQAdmissible d q hq (d.U1 N hN) :=
  isQAdmissible_U1 (Langlandscape.Hyp.ramNrdSurj_holds d) hqN

/-- `def:s02-GU` (`s02-GU`): form of `isQAdmissible_Utower` with the registered hypothesis
`Hyp.RamNrdSurj` discharged by `Hyp.ramNrdSurj_holds`;
the remaining explicit hypotheses (`hqN : ¬ q ∣ M p^s`) are unchanged:
the tower level `U_s = U_1(M p^s)` is `q`-admissible for `q ∤ M p^s`. -/
theorem isQAdmissible_Utower_uncond {M p s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hqN : ¬ q ∣ M * p ^ s) :
    IsQAdmissible d q hq (d.Utower M p s hN) :=
  isQAdmissible_Utower (Langlandscape.Hyp.ramNrdSurj_holds d) hqN

end Langlandscape.Tree
