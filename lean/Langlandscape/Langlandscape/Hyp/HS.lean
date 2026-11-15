/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Basic

/-!
# Hypothesis `HS`: the Hasse–Schilling norm theorem for definite `B` (S02-L4a)

`mathematics/chapters/s02/1-tree.tex`, `lem:s02-normone`(b): `Nrd(B^×) = ℚ_{>0}`.
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`. The inclusion `Nrd(B^×) ⊆ ℚ_{>0}` is not part of the hypothesis
(it holds because `B` is definite, import `nrd_definite`).

Status: *cited* (Voight, Main Thm. 14.7.4; Vignéras III.4.1); not formalized.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat

/-- `lem:s02-normone`(b) input (Hasse–Schilling): every positive rational is the reduced norm of a unit of the
definite algebra `B`. Source: Voight, *Quaternion algebras*, Main Thm. 14.7.4; Vignéras, Ch. III, Thm. 4.1. Cited;
discharge plan: Hasse–Schilling (post-hackathon). -/
def HS (d : DefiniteData) : Prop :=
  ∀ r : ℚ, 0 < r → ∃ γ : (QuatAlg ℚ d.a d.b)ˣ, GL2TF.Quat.nrd (γ : QuatAlg ℚ d.a d.b) = r

end Langlandscape.Hyp
