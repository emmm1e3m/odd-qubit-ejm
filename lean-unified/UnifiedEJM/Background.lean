import UnifiedEJM.Phase
import OddEJM.WeightPhase
import OddEJM.FourWalsh

namespace UnifiedEJM
open OddEJM

open scoped BigOperators
open Complex

/-- 实际背景Pauli期望精确变成带相位的Boolean字符和。 -/
theorem background_pauli_sum {n : ℕ} (u c : ℂ) (a b : Bits n) :
    pauliExpectation (background u) a b c =
      (c * star (I ^ weight a)) *
        ∑ z, character (a + b) z *
          star (u ^ (Q20 (compress (z + a))).val) * u ^ (Q20 (compress z)).val := by
  simp only [pauliExpectation, background, q]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [star_mul]
  rw [show star (u ^ (Q20 (compress (z + a))).val) * star (I ^ weight (z + a)) * c *
        character b z * (I ^ weight z * u ^ (Q20 (compress z)).val) =
      c * (star (I ^ weight (z + a)) * I ^ weight z) *
        character b z * star (u ^ (Q20 (compress (z + a))).val) *
          u ^ (Q20 (compress z)).val by ring]
  rw [weight_phase_ratio, character_add_left]
  ring


theorem background_pauli_correlation {n : ℕ} (u c : ℂ) (a b : Bits n) :
    pauliExpectation (background u) a b c =
      (c * star (I ^ weight a)) *
        phaseCorrelation (fun z => Q20 (compress z)) (a + b) a u (star u) := by
  rw [background_pauli_sum]
  unfold phaseCorrelation
  apply congrArg (fun w : ℂ => (c * star (I ^ weight a)) * w)
  apply Finset.sum_congr rfl
  intro z _
  rw [star_pow]
  ring

theorem background_pauli_zero_classI {n : ℕ} (u c : ℂ) (a b : Bits n)
    (hh : a + b ≠ 0) (ha : dot (a + b) a = 1)
    (hQ : walsh (fun z : Bits n => Q20 (compress z)) (a + b) = 0) :
    pauliExpectation (background u) a b c = 0 := by
  rw [background_pauli_correlation,
    phaseCorrelation_zero_classI _ _ _ _ _ hh ha hQ, mul_zero]

theorem background_pauli_zero_classII {n : ℕ} (u c : ℂ) (a b : Bits n)
    (hh : a + b ≠ 0) (ha : dot (a + b) a = 0) (hu : u * star u = 1)
    (hQ : walsh (derivative (fun z : Bits n => Q20 (compress z)) a) (a + b) = 0) :
    pauliExpectation (background u) a b c = 0 := by
  rw [background_pauli_correlation,
    phaseCorrelation_zero_classII _ _ _ _ _ hh ha hu hQ, mul_zero]

end UnifiedEJM
