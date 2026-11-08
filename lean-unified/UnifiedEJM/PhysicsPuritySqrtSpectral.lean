import UnifiedEJM.PhysicsPurityTail

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace UnifiedEJM.PurityTail

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Hermitian矩阵平方的迹等于实际本征值平方和。 -/
theorem trace_square_eq_sum_eigenvalue_sq (R : Matrix α α ℂ) (hR : R.IsHermitian) :
    (R * R).trace.re = ∑ i, (hR.eigenvalues i) ^ 2 := by
  let U : Matrix α α ℂ := hR.eigenvectorUnitary
  let D : Matrix α α ℂ := Matrix.diagonal (Complex.ofReal ∘ hR.eigenvalues)
  have hu : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hr : R = U * D * Uᴴ := by
    convert hR.spectral_theorem using 1 <;>
      simp only [Unitary.conjStarAlgAut_apply] <;> rfl
  have ht : (R * R).trace = ∑ i, (hR.eigenvalues i : ℂ) ^ 2 := by
    calc
      (R * R).trace = (U * (D * D) * Uᴴ).trace := by
        rw [hr]
        congr 1
        calc
          (U * D * Uᴴ) * (U * D * Uᴴ) = U * D * (Uᴴ * U) * D * Uᴴ := by
            simp only [Matrix.mul_assoc]
          _ = U * (D * D) * Uᴴ := by
            rw [hu]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (D * D).trace := by rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul]
      _ = _ := by simp [D, Matrix.diagonal_mul_diagonal, Function.comp_def, pow_two]
  have h := congrArg Complex.re ht
  simpa [pow_two, Complex.mul_re] using h

theorem trace_square_nonneg (R : Matrix α α ℂ) (hR : R.IsHermitian) :
    0 ≤ (R * R).trace.re := by
  rw [trace_square_eq_sum_eigenvalue_sq R hR]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- 正矩阵的最大谱值由纯度的平方根控制，无需迹范数理论。 -/
theorem density_le_sqrt_trace_square (R : Matrix α α ℂ) (hR : R.PosSemidef) :
    R ≤ (Real.sqrt (R * R).trace.re : ℂ) • (1 : Matrix α α ℂ) := by
  let r := Real.sqrt (R * R).trace.re
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = (R * R).trace.re :=
    Real.sq_sqrt (trace_square_nonneg R hR.1)
  have he (i : α) : hR.1.eigenvalues i ≤ r := by
    have hi : (hR.1.eigenvalues i) ^ 2 ≤ ∑ j, (hR.1.eigenvalues j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [← trace_square_eq_sum_eigenvalue_sq R hR.1] at hi
    nlinarith
  change R ≤ (r : ℂ) • (1 : Matrix α α ℂ)
  rw [Matrix.le_iff, hR.1.spectral_theorem]
  let U : Matrix α α ℂ := hR.1.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hd : (Matrix.diagonal
      (fun i => (r : ℂ) - (hR.1.eigenvalues i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℂ) ≤ (r : ℂ) - (hR.1.eigenvalues i : ℂ)
      exact_mod_cast sub_nonneg.mpr (he i))
  have hh := hd.mul_mul_conjTranspose_same U
  convert hh using 1
  rw [show Matrix.diagonal (fun i => (r : ℂ) - (hR.1.eigenvalues i : ℂ)) =
      (r : ℂ) • (1 : Matrix α α ℂ) -
        Matrix.diagonal (Complex.ofReal ∘ hR.1.eigenvalues) by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
    rfl]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hu,
    Unitary.conjStarAlgAut_apply]
  rfl

end UnifiedEJM.PurityTail
