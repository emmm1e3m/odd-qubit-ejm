import OddEJM.WeightPhase
import OddEJM.FourWalsh

namespace OddEJM

open scoped BigOperators
open Complex

theorem background_pauli_correlation {n : ℕ} (u c : ℂ) (a b : Bits n) :
    pauliExpectation (background u) a b c =
      (c * star (I ^ weight a)) *
        phaseCorrelation (fun z => Q (compress z)) (a + b) a u (star u) := by
  rw [background_pauli_sum]
  unfold phaseCorrelation
  apply congrArg (fun w : ℂ => (c * star (I ^ weight a)) * w)
  apply Finset.sum_congr rfl
  intro z _
  rw [star_pow]
  ring

theorem background_pauli_zero_classI {n : ℕ} (u c : ℂ) (a b : Bits n)
    (hh : a + b ≠ 0) (ha : dot (a + b) a = 1)
    (hQ : walsh (fun z : Bits n => Q (compress z)) (a + b) = 0) :
    pauliExpectation (background u) a b c = 0 := by
  rw [background_pauli_correlation,
    phaseCorrelation_zero_classI _ _ _ _ _ hh ha hQ, mul_zero]

theorem background_pauli_zero_classII {n : ℕ} (u c : ℂ) (a b : Bits n)
    (hh : a + b ≠ 0) (ha : dot (a + b) a = 0) (hu : u * star u = 1)
    (hQ : walsh (derivative (fun z : Bits n => Q (compress z)) a) (a + b) = 0) :
    pauliExpectation (background u) a b c = 0 := by
  rw [background_pauli_correlation,
    phaseCorrelation_zero_classII _ _ _ _ _ hh ha hu hQ, mul_zero]

end OddEJM
