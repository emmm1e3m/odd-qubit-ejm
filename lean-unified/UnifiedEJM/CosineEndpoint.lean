import UnifiedEJM.EvenLow
import UnifiedEJM.StabilizerMarginal
import UnifiedEJM.PhysicsCircuit

noncomputable section
open scoped BigOperators Matrix
open Complex OddEJM OddEJM.CircuitPauli
open UnifiedEJM.EvenWalsh UnifiedEJM.StabilizerMarginal

namespace UnifiedEJM.CosineEndpoint

/-- 完整物理相位在正端点的全零串修正恰好消失。 -/
theorem diagonal_endpoint (n : ℕ) :
    EvenFamily.diagonal n (Real.pi/2) 0 =
      fun z => -I * (I ^ weight z * I ^ (qA z).val) := by
  funext z
  simp only [EvenFamily.diagonal, PhysicsEndpoint.positive_angle, anglePhase_zero]
  rw [EvenRaw.raw_eq_corrected qA UnifiedEJM.q I 1 (qA_zero n) (q_zero n)]
  simp [EvenRaw.corrected, EvenRaw.background]

/-- 真实归一化输入的任意Pauli期望化为AND相位字符和。 -/
theorem input_expectation (n : ℕ) (a b : Bits n) (c : ℂ) :
    pauliExpectation (fun z => normFactor n * EvenFamily.diagonal n (Real.pi/2) 0 z)
      a b c = (star (normFactor n) * normFactor n) *
        (c * star (I ^ weight a)) *
        ∑ z, character (a+b) z * (I ^ (qA z).val * star (I ^ (qA (z+a)).val)) := by
  rw [diagonal_endpoint, UnifiedEJM.pauliExpectation_scale,
    UnifiedEJM.pauliExpectation_scale]
  have hi : star (-I) * (-I) = (1:ℂ) := by simp
  rw [hi, one_mul]
  rw [EvenRaw.phase_background_sum]
  ring

theorem correlation_free_zero {n : ℕ} (a h : Bits n) (j : Fin n)
    (hj : ¬ InE n j.val) (hh : h j = 1) :
    (∑ z, character h z * (I ^ (qA z).val * star (I ^ (qA (z+a)).val))) = 0 := by
  apply weighted_character_zero h (unitBit n j.val)
  · simpa only [dot_unitBit] using hh
  · intro z
    have he := ezero_unit (n:=n) j.val hj
    rw [qA_add z _ he]
    rw [show z + unitBit n j.val + a = (z+a) + unitBit n j.val by abel]
    rw [qA_add (z+a) _ he]

theorem correlation_free {n : ℕ} (a : Bits n) (ha : EZero a) :
    (∑ z : Bits n, I ^ (qA z).val * star (I ^ (qA (z+a)).val)) = (2:ℂ)^n := by
  simp only [qA_add _ _ ha]
  have h (z : Bits n) : I ^ (qA z).val * star (I ^ (qA z).val) = 1 := by
    rcases OddEJM.bit_cases (qA z) with hh | hh <;>
      simp [hh, ZMod.val_one_eq_one_mod]
  simp only [h]
  simp [Fintype.card_fun]

theorem seed_yz {n : ℕ} (hn : 2 ≤ n) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (unitBit n 0) (unitBit n 0 + unitBit n 1) I = 1 := by
  change pauliExpectation (circuit _) _ _ _ = _
  rw [circuit_expectation (by omega) _ _ _ _ _ _ _ (PhysicsEndpoint.yz_pullback hn _),
    input_expectation, bits_add_self]
  simp only [character_zero_local, one_mul]
  rw [correlation_free _ (ezero_unit 0 (by simp [InE])),
    MaskFacts.weight_unit 0 (by omega)]
  simpa using normFactor_card n

end UnifiedEJM.CosineEndpoint
