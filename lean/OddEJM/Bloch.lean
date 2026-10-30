import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

namespace OddEJM.Geometry

open Complex

/-- 标准 Pauli 展开得到的实际 2×2 复密度矩阵表达式。 -/
noncomputable def blochMatrix (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + (z : ℂ)) / 2, ((x : ℂ) - I * y) / 2;
    ((x : ℂ) + I * y) / 2, (1 - (z : ℂ)) / 2]

lemma bloch_trace (x y z : ℝ) : Matrix.trace (blochMatrix x y z) = 1 := by
  simp [Matrix.trace, Matrix.diag_apply, blochMatrix, Fin.sum_univ_two]
  ring

lemma bloch_purity (x y z : ℝ) :
    Matrix.trace (blochMatrix x y z * blochMatrix x y z) =
      (((1 + (x ^ 2 + y ^ 2 + z ^ 2)) / 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.diag_apply, blochMatrix, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

lemma bloch_det_shift (x y z ev : ℝ) :
    Matrix.det (blochMatrix x y z - (ev : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (((ev ^ 2 - ev + (1 - (x ^ 2 + y ^ 2 + z ^ 2)) / 4) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [blochMatrix, Matrix.sub_apply, Matrix.smul_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

lemma bloch_purity_of_radius (x y z r : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = r ^ 2) :
    Matrix.trace (blochMatrix x y z * blochMatrix x y z) =
      (((1 + r ^ 2) / 2 : ℝ) : ℂ) := by
  rw [bloch_purity, h]

lemma bloch_det_eigenvalue (x y z r ε : ℝ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = r ^ 2) (hε : ε ^ 2 = 1) :
    Matrix.det (blochMatrix x y z - (((1 + ε * r) / 2 : ℝ) : ℂ) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  rw [bloch_det_shift, h]
  have hr : ((1 + ε * r) / 2) ^ 2 - (1 + ε * r) / 2 + (1 - r ^ 2) / 4 = 0 := by
    nlinarith [hε]
  rw [hr]
  simp

lemma eigenvalues_in_unit_interval (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (1 - r) / 2 ∈ Set.Icc (0 : ℝ) 1 ∧ (1 + r) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hr with ⟨hl, hu⟩
  constructor <;> constructor <;> linarith

end OddEJM.Geometry




