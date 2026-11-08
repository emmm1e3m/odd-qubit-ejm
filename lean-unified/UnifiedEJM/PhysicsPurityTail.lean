import UnifiedEJM.Multipartite
import UnifiedEJM.Phase
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix WithLp
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace UnifiedEJM.PurityTail

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- 迹为一的正矩阵的每个本征值不超过一。 -/
theorem density_le_one (R : Matrix α α ℂ) (hR : R.PosSemidef)
    (htr : R.trace = 1) : R ≤ 1 := by
  have hs : ∑ i, hR.1.eigenvalues i = 1 := by
    have := congrArg Complex.re (hR.1.trace_eq_sum_eigenvalues.symm.trans htr)
    simpa using this
  have he (i : α) : hR.1.eigenvalues i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hR.eigenvalues_nonneg j) (Finset.mem_univ i)
  rw [Matrix.le_iff, hR.1.spectral_theorem]
  let U : Matrix α α ℂ := hR.1.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hd : (Matrix.diagonal (fun i => (1 : ℂ) - (hR.1.eigenvalues i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℂ) ≤ 1 - (hR.1.eigenvalues i : ℂ)
      exact_mod_cast sub_nonneg.mpr (he i))
  have hh := hd.mul_mul_conjTranspose_same U
  convert hh using 1
  rw [show Matrix.diagonal (fun i => (1 : ℂ) - (hR.1.eigenvalues i : ℂ)) =
      1 - Matrix.diagonal (Complex.ofReal ∘ hR.1.eigenvalues) by
    rw [← Matrix.diagonal_sub, ← Matrix.diagonal_one]
    rfl]
  simp only [mul_sub, sub_mul, mul_one, hu, Unitary.conjStarAlgAut_apply]
  rfl

/-- 两个真实归一化约化态之和减去单位阵是收缩算符。 -/
theorem centered_sum_norm_le_one [Nonempty α] (R T : Matrix α α ℂ)
    (hR : R.PosSemidef) (hT : T.PosSemidef)
    (hr : R.trace = 1) (ht : T.trace = 1) : ‖R + T - 1‖ ≤ 1 := by
  have hlo : (-1 : Matrix α α ℂ) ≤ R + T - 1 := by
    have := add_nonneg hR.nonneg hT.nonneg
    simpa using sub_le_sub_right this 1
  have hhi : R + T - 1 ≤ (1 : Matrix α α ℂ) := by
    have := add_le_add (density_le_one R hR hr) (density_le_one T hT ht)
    simpa using sub_le_sub_right this 1
  have hh : IsSelfAdjoint (R + T - 1) := hR.1.add hT.1 |>.sub (by simp [IsSelfAdjoint])
  simpa using hh.norm_le_max_of_le_of_le hlo hhi

end UnifiedEJM.PurityTail
