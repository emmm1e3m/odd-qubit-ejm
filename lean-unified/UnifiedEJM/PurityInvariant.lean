import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

open scoped Matrix
noncomputable section

namespace UnifiedEJM.PurityInvariant
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- 真实纯态系数矩阵的约化纯度。 -/
def purity (A : Matrix m n ℂ) : ℂ := Matrix.trace ((A*Aᴴ)*(A*Aᴴ))

/-- 任意有限维二分系统的局域酉保持约化纯度。 -/
theorem purity_local_unitary (A : Matrix m n ℂ) (U : Matrix m m ℂ)
    (V : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    purity (U * A * Vᴴ) = purity A := by
  have hr : (U*A*Vᴴ)*(U*A*Vᴴ)ᴴ = U*(A*Aᴴ)*Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      _ = U * A * (Vᴴ * V) * Aᴴ * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (A*Aᴴ) * Uᴴ := by rw [hV]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  unfold purity
  rw [hr]
  have hsq : (U*(A*Aᴴ)*Uᴴ)*(U*(A*Aᴴ)*Uᴴ) = U*((A*Aᴴ)*(A*Aᴴ))*Uᴴ := by
    calc
      _ = U*(A*Aᴴ)*(Uᴴ*U)*(A*Aᴴ)*Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  rw [hsq,Matrix.trace_mul_cycle,hU,Matrix.one_mul]

/-- 纯态的互补两侧约化纯度相同。 -/
theorem purity_transpose (A : Matrix m n ℂ) : purity Aᵀ = purity A := by
  unfold purity
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.conjTranspose_transpose,Matrix.transpose_conjTranspose]
  change Matrix.trace (Aᴴ * A * (Aᴴ * A)) = Matrix.trace (A * Aᴴ * (A * Aᴴ))
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle Aᴴ (A * Aᴴ) A

end UnifiedEJM.PurityInvariant

