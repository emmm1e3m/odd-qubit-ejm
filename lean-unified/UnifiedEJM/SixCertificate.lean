import UnifiedEJM.SixCoefficients
namespace UnifiedEJM.SixCertificate
open OddEJM Complex
open scoped BigOperators
noncomputable def colourSum (p : Fin 18) (phases : Fin 4 → ℂ) : ℂ :=
  ∑ z : Bits 6, character (decode6 (charCode p)) z *
    (phases (colour z) * star (phases (colour (z + decode6 (flipCode p)))))

lemma coeff_cast (p : Fin 18) (r s : Fin 4) :
    (coeff p r s : ℂ) = ∑ z : Bits 6,
      if colour z = r ∧ colour (z + decode6 (flipCode p)) = s
      then character (decode6 (charCode p)) z else 0 := by
  simp [coeff, Int.cast_sum, character]

/-- 按实际颜色归组的恒等式，将整数证书连接到任意复相位振幅。 -/
theorem colour_sum_eq_coeff (p : Fin 18) (phases : Fin 4 → ℂ) :
    colourSum p phases = ∑ r : Fin 4, ∑ s : Fin 4,
      (expectedCoeff p r s : ℂ) * phases r * star (phases s) := by
  have hc (z : Bits 6) :
      character (decode6 (charCode p)) z *
        (phases (colour z) * star (phases (colour (z + decode6 (flipCode p))))) =
      ∑ r : Fin 4, ∑ s : Fin 4,
        (if colour z = r ∧ colour (z + decode6 (flipCode p)) = s
         then character (decode6 (charCode p)) z else 0) * phases r * star (phases s) := by
    simp [ite_and, Finset.sum_ite_irrel, eq_comm, mul_assoc]
  unfold colourSum
  simp_rw [hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← coeff_cast, all_coefficients_checked]

/-- 任意背景相位的真实Pauli期望与字符和的严格桥接。 -/
theorem phase_background_sum {n : ℕ} (f : Vec n) (a b : Bits n) (c : ℂ) :
    pauliExpectation (fun z => I ^ weight z * f z) a b c =
      (c * star (I ^ weight a)) *
        ∑ z, character (a + b) z * (f z * star (f (z + a))) := by
  simp only [pauliExpectation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [star_mul]
  calc
    _ = c * (star (I ^ weight (z + a)) * I ^ weight z) * character b z *
      (f z * star (f (z + a))) := by ring
    _ = _ := by rw [weight_phase_ratio, character_add_left]; ring

end UnifiedEJM.SixCertificate



