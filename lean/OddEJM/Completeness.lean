import OddEJM.Orthonormal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OddEJM
open scoped BigOperators

/-- 实际测量态的秩一投影之和为恒等矩阵，故这些列给出完整投影测量。 -/
theorem measurement_complete {n : ℕ} (hn : 0 < n) (t : ℝ) (z w : Bits n) :
    (∑ label, measurement n t label z * star (measurement n t label w)) =
      if z = w then 1 else 0 := by
  let M : Matrix (Bits n) (Bits n) ℂ := Matrix.of (fun x label => measurement n t label x)
  have hcol : M.conjTranspose * M = 1 := by
    ext k l
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, M, Matrix.of_apply, inner]
      using measurement_orthonormal hn t k l
  have hrow : M * M.conjTranspose = 1 := mul_eq_one_comm.mp hcol
  have h := congrArg (fun A : Matrix (Bits n) (Bits n) ℂ => A z w) hrow
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, M, Matrix.of_apply] using h

end OddEJM


