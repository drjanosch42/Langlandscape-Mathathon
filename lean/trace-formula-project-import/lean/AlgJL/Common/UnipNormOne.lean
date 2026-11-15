import AlgJL.Meta.Tag
import AlgJL.VolI.P0.TopGroups
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-!
# `n(u) ∈ G(𝔸)^1` (B-only plumbing of `vol2/ch-03-kernel.tex`)

`u ↦ n(u) ∈ G(𝔸)^1`, moved unchanged (name, namespace, body) out of `GL2TF.VolII.KernelClasses` in M8 (G0-U1, the
CuspDefs split) so that the kernel-import-free module `GL2TF.VolI.P2.CuspDefs` (the constant term and `L²_cusp`) can use
it. Its imports lie in the import closure of `VolII.KernelClasses`, which imports this module. Owner: L2.
-/

open Matrix.GeneralLinearGroup

namespace GL2TF

namespace KerAux

theorem upperRightHom_mem_normOne (u : Adele) : upperRightHom u ∈ normOneGroup := by
  show ideleNorm (Matrix.GeneralLinearGroup.det (upperRightHom u)) = 1
  have hn : Matrix.GeneralLinearGroup.det (upperRightHom u) = 1 := by
    apply Units.ext; simp [Matrix.GeneralLinearGroup.det]
  rw [hn, map_one]

end KerAux

/-- `u ↦ n(u) ∈ G(𝔸)^1` (B-only plumbing). -/
@[tf_aux "II.kernel.def:unip-norm-one"]
noncomputable def unipNormOne (u : Adele) : normOneGroup :=
  ⟨upperRightHom u, KerAux.upperRightHom_mem_normOne u⟩

end GL2TF
