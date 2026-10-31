import UnifiedEJM.ThreeQubit
import Mathlib.LinearAlgebra.Matrix.Block

set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace UnifiedEJM.ThreeQubit
private def lower : Matrix (Fin 7) (Fin 7) ℝ := ![![1, 0, 0, 0, 0, 0, 0], ![1/2, 1, 0, 0, 0, 0, 0], ![1/2, 0, 1, 0, 0, 0, 0], ![1/2, 1, 0, 1, 0, 0, 0], ![1, -1, 0, -3/4, 1, 0, 0], ![1/2, 0, 1, 0, 0, 1, 0], ![0, 2, 1, 9/4, -3, 2, 1]]
private def upper : Matrix (Fin 7) (Fin 7) ℝ := ![![-2, -2, 0, 1, 1, 0, 2], ![0, -1, 0, -3/2, 3/2, 2, -1], ![0, 0, -1, -1/2, 1/2, 0, 0], ![0, 0, 0, 2, -2, -2, 2], ![0, 0, 0, 0, -1, 1/2, 1/2], ![0, 0, 0, 0, 0, 1, -1], ![0, 0, 0, 0, 0, 0, 1]]
private def perm : Equiv.Perm (Fin 7) := Equiv.swap 3 4 * Equiv.swap 4 5
private lemma lu_factorization : jacobianMatrix.submatrix perm id = lower * upper := by
  ext i j
  change jacobianMatrix ((Equiv.swap 3 4) ((Equiv.swap 4 5) i)) j =
    ∑ k : Fin 7, lower i k * upper k j
  fin_cases i <;> fin_cases j <;>
    norm_num [jacobianMatrix, lower, upper, perm, Matrix.submatrix_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, Equiv.swap_apply_def]
private lemma lower_triangular : lower.IsLowerTriangular := by
  intro i j h
  change i < j at h
  fin_cases i <;> fin_cases j <;> norm_num [lower] at *
private lemma upper_triangular : upper.IsUpperTriangular := by
  intro i j h
  change j < i at h
  fin_cases i <;> fin_cases j <;> norm_num [upper] at *
/-- 论文中4DF(0)的7阶子式精确为4。 -/
theorem jacobian_determinant : jacobianMatrix.det = 4 := by
  have h := congrArg Matrix.det lu_factorization
  rw [Matrix.det_permute, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular lower lower_triangular,
    Matrix.det_of_isUpperTriangular upper_triangular] at h
  norm_num [perm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap,
    lower, upper, Fin.prod_univ_succ] at h
  exact h
/-- 真实残差导数矩阵的行列式。 -/
theorem derivative_determinant : ((1/4:ℝ) • jacobianMatrix).det = 1/4096 := by
  rw [Matrix.det_smul, jacobian_determinant]
  norm_num
end UnifiedEJM.ThreeQubit

