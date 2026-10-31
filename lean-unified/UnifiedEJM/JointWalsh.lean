import UnifiedEJM.EvenWalsh
import OddEJM.FourWalsh
import OddEJM.WeightPhase
import UnifiedEJM.Walsh
import UnifiedEJM.Masks

namespace UnifiedEJM.EvenWalsh
open OddEJM
open scoped BigOperators

/-- 联合背景的实际相位相关和，尚未乘拉回 Pauli 的常相位。 -/
def jointCorrelation {n : ℕ} (h a : Bits n) (u v : ℂ) : ℂ :=
  ∑ z, character h z *
    (u ^ (qA z).val * star (u ^ (qA (z+a)).val)) *
      qPhasePair v (compress z) (compress (z+a))

def jointBackground {n : ℕ} (u v : ℂ) (z : Bits n) : ℂ :=
  Complex.I ^ weight z * u ^ (qA z).val * v ^ (UnifiedEJM.q z).val

/-- 真实联合背景的 Pauli 期望，与字符归约严格对应。 -/
theorem jointBackground_expectation {n : ℕ} (u v c : ℂ) (a b : Bits n) :
    pauliExpectation (jointBackground u v) a b c =
      (c * star (Complex.I ^ weight a)) * jointCorrelation (a+b) a u v := by
  unfold pauliExpectation jointBackground jointCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [star_mul, qPhasePair, UnifiedEJM.q]
  have hr := weight_phase_ratio a z
  calc
    _ = c * (star (Complex.I ^ weight (z+a)) * Complex.I ^ weight z) * character b z *
        (u ^ (qA z).val * star (u ^ (qA (z+a)).val)) *
        (v ^ (Q20 (compress z)).val * star (v ^ (Q20 (compress (z+a))).val)) := by ring
    _ = _ := by rw [hr, character_add_left]; ring

def negativeSum {n : ℕ} (h a : Bits n) (G : Bits 5 → Bits 5 → ℂ) : ℂ :=
  ∑ z, character h z * (if EZero (z+a) then G (compress z) (compress (z+a)) else 0)

theorem negativeSum_translate {n : ℕ} (h a : Bits n) (G : Bits 5 → Bits 5 → ℂ) :
    negativeSum h a G = character h a * positiveSum h a (fun v w => G w v) := by
  unfold negativeSum positiveSum
  calc
    _ = ∑ z, character h (z+a) *
        (if EZero (z+a+a) then G (compress (z+a)) (compress (z+a+a)) else 0) :=
      (Equiv.sum_comp (Equiv.addRight a)
        (fun z => character h z *
          (if EZero (z+a) then G (compress z) (compress (z+a)) else 0))).symm
    _ = character h a * ∑ z, character h z *
        (if EZero z then G (compress (z+a)) (compress z) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [add_assoc, bits_add_self, add_zero, character_add]
      ring

theorem qPhasePair_swap (u : ℂ) (v w : Bits 5) :
    qPhasePair u w v = qPhasePair (star u) v w := by
  simp only [qPhasePair, star_pow, star_star]
  ring

theorem negativeSum_phase {n : ℕ} (h a : Bits n) (u : ℂ) :
    negativeSum h a (qPhasePair u) = character h a * positiveSum h a (qPhasePair (star u)) := by
  rw [negativeSum_translate]
  have heq : (fun v w => qPhasePair u w v) = qPhasePair (star u) := by
    funext v w
    exact qPhasePair_swap u v w
  rw [heq]

theorem jointCorrelation_decompose {n : ℕ} (h a : Bits n) (u v : ℂ)
    (ha : ¬ EZero a) :
    jointCorrelation h a u v = phaseCorrelation UnifiedEJM.q h a v (star v) +
      (u-1) * positiveSum h a (qPhasePair v) +
      (star u-1) * negativeSum h a (qPhasePair v) := by
  unfold jointCorrelation phaseCorrelation positiveSum negativeSum
  have hp (z : Bits n) :
      character h z * (u ^ (qA z).val * star (u ^ (qA (z+a)).val)) *
          qPhasePair v (compress z) (compress (z+a)) =
      character h z * v ^ (UnifiedEJM.q z).val * (star v) ^ (UnifiedEJM.q (z+a)).val +
      (u-1) * (character h z *
        (if EZero z then qPhasePair v (compress z) (compress (z+a)) else 0)) +
      (star u-1) * (character h z *
        (if EZero (z+a) then qPhasePair v (compress z) (compress (z+a)) else 0)) := by
    by_cases hz : EZero z
    · have hza := not_ezero_translated a z ha hz
      simp only [qA, if_pos hz, if_neg hza, qPhasePair, UnifiedEJM.q, star_pow]
      norm_num [show (1:Bit).val=1 by decide]
      ring
    · by_cases hza : EZero (z+a)
      · simp only [qA, if_neg hz, if_pos hza, qPhasePair, UnifiedEJM.q, star_pow]
        norm_num [show (1:Bit).val=1 by decide]
        ring
      · simp [qA, hz, hza, qPhasePair, UnifiedEJM.q, star_pow, mul_assoc]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem jointCorrelation_classI {n : ℕ} (h a : Bits n) (u v : ℂ)
    (hu : u * star u = 1) (ha : EZero a) :
    jointCorrelation h a u v = phaseCorrelation UnifiedEJM.q h a v (star v) := by
  unfold jointCorrelation phaseCorrelation
  apply Finset.sum_congr rfl
  intro z _
  rw [qA_add z a ha]
  have hp (k : ℕ) : u^k * star (u^k) = 1 := by
    rw [star_pow, ← mul_pow, hu, one_pow]
  rw [hp]
  simp [qPhasePair, UnifiedEJM.q, star_pow, mul_assoc]

theorem jointCorrelation_classII_zero {n : ℕ} (h a : Bits n) (u v : ℂ)
    (ha : ¬ EZero a)
    (hbase : phaseCorrelation UnifiedEJM.q h a v (star v) = 0)
    (hp : positiveSum h a (qPhasePair v) = 0)
    (hm : positiveSum h a (qPhasePair (star v)) = 0) :
    jointCorrelation h a u v = 0 := by
  rw [jointCorrelation_decompose h a u v ha, negativeSum_phase, hbase, hp, hm]
  ring

theorem joint_internalX_zero {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u v : ℂ) (hv : v * star v = 1)
    (hbase : phaseCorrelation UnifiedEJM.q (adjacentMask n j) (adjacentMask n j)
      v (star v) = 0) :
    jointCorrelation (adjacentMask n j) (adjacentMask n j) u v = 0 := by
  apply jointCorrelation_classII_zero _ _ u v
  · exact not_ezero_adjacent (by omega) he j hj hjn
  · exact hbase
  · exact positiveSum_X hn he j hj hjn v hv
  · exact positiveSum_X hn he j hj hjn (star v) (by simpa [mul_comm] using hv)

theorem joint_internalY_zero {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u v : ℂ) (hv : v * star v = 1)
    (hbase : phaseCorrelation UnifiedEJM.q (internalYCharacter n j) (internalYMask n j)
      v (star v) = 0) :
    jointCorrelation (internalYCharacter n j) (internalYMask n j) u v = 0 := by
  apply jointCorrelation_classII_zero _ _ u v
  · exact not_ezero_internalY (by omega) he j hj hjn
  · exact hbase
  · exact positiveSum_Y hn he j hj hjn v hv
  · exact positiveSum_Y hn he j hj hjn (star v) (by simpa [mul_comm] using hv)

/-- 每一内部物理 X 的联合背景零，无剩余单核假设。 -/
theorem joint_internalX_zero_closed {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u v : ℂ) (hv : v * star v = 1) :
    jointCorrelation (adjacentMask n j) (adjacentMask n j) u v = 0 := by
  apply joint_internalX_zero hn he j hj hjn u v hv
  have hf := UnifiedEJM.MaskFacts.internalX (show 5 ≤ n by omega) j hj hjn
  apply phaseCorrelation_zero_classII
  · simpa only [add_zero] using hf.hh
  · simpa only [add_zero] using hf.hd
  · exact hv
  · exact UnifiedEJM.walsh_DQ_X (by omega) j hj hjn

/-- 每一内部物理 Y 的联合背景零，无剩余单核假设。 -/
theorem joint_internalY_zero_closed {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u v : ℂ) (hv : v * star v = 1) :
    jointCorrelation (internalYCharacter n j) (internalYMask n j) u v = 0 := by
  apply joint_internalY_zero hn he j hj hjn u v hv
  have hf := UnifiedEJM.MaskFacts.internalY (show 5 ≤ n by omega) j hj hjn
  have hh := UnifiedEJM.MaskFacts.h_internalY j hj hjn
  apply phaseCorrelation_zero_classII
  · simpa only [hh] using hf.hh
  · simpa only [hh] using hf.hd
  · exact hv
  · exact UnifiedEJM.walsh_DQ_Y (by omega) j hj hjn

theorem ezero_first {n : ℕ} : EZero (unitBit n 0) := by
  apply ezero_unit; simp [InE]

theorem ezero_penultimate {n : ℕ} : EZero (unitBit n (n-2)) := by
  apply ezero_unit; simp [InE]

theorem joint_classI_zero {n : ℕ} (h a : Bits n) (u v : ℂ)
    (hu : u * star u = 1) (ha : EZero a)
    (hh : h ≠ 0) (hd : dot h a = 1) (hQ : walsh UnifiedEJM.q h = 0) :
    jointCorrelation h a u v = 0 := by
  rw [jointCorrelation_classI h a u v hu ha]
  exact phaseCorrelation_zero_classI _ _ _ _ _ hh hd hQ

theorem joint_firstX_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    jointCorrelation (unitBit n 0) (unitBit n 0) u v = 0 := by
  have hf := UnifiedEJM.MaskFacts.firstX hn
  apply joint_classI_zero _ _ u v hu ezero_first
  · simpa only [add_zero] using hf.hh
  · simpa only [add_zero] using hf.hd
  · exact UnifiedEJM.walsh_Q_first hn

theorem joint_lastX_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    jointCorrelation (unitBit n (n-2) + unitBit n (n-1)) (unitBit n (n-2)) u v = 0 := by
  have hf := UnifiedEJM.MaskFacts.lastX hn
  apply joint_classI_zero _ _ u v hu ezero_penultimate hf.hh hf.hd
  rw [UnifiedEJM.MaskFacts.h_lastX (by omega)]
  exact UnifiedEJM.walsh_Q_tail hn (n-2) (by omega)

theorem joint_firstY_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    jointCorrelation (tailMask n 1) (unitBit n 0 + unitBit n (n-1)) u v = 0 := by
  have hf := UnifiedEJM.MaskFacts.firstY hn
  have hh := UnifiedEJM.MaskFacts.h_firstY (show 2 ≤ n by omega)
  apply joint_classI_zero _ _ u v hu (ezero_add ezero_first (ezero_last (by omega)))
  · simpa only [hh] using hf.hh
  · simpa only [hh] using hf.hd
  · exact UnifiedEJM.walsh_Q_tail hn 1 (by omega)

theorem joint_lastY_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    jointCorrelation (unitBit n (n-2)) (unitBit n (n-1) + unitBit n (n-2)) u v = 0 := by
  have hf := UnifiedEJM.MaskFacts.lastY hn
  apply joint_classI_zero _ _ u v hu (ezero_add (ezero_last (by omega)) ezero_penultimate)
  · simpa only [UnifiedEJM.MaskFacts.h_lastY] using hf.hh
  · simpa only [UnifiedEJM.MaskFacts.h_lastY] using hf.hd
  · exact UnifiedEJM.walsh_Q_penultimate hn

theorem joint_localZ_zero {n : ℕ} (hn : 5 ≤ n) (j : ℕ) (hj : j < n)
    (u v : ℂ) (hu : u * star u = 1) :
    jointCorrelation (tailMask n j) (unitBit n (n-1)) u v = 0 := by
  have hf := UnifiedEJM.MaskFacts.localZ hn j hj
  have hh := UnifiedEJM.MaskFacts.h_localZ j hj
  apply joint_classI_zero _ _ u v hu (ezero_last (by omega))
  · simpa only [hh] using hf.hh
  · simpa only [hh] using hf.hd
  · exact UnifiedEJM.walsh_Q_tail hn j hj

theorem qA_of_ezero {n : ℕ} {a : Bits n} (ha : EZero a) : qA a = 1 := by simp [qA, ha]

theorem background_firstX_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    pauliExpectation (jointBackground u v) (unitBit n 0) 0 1 = 0 := by
  rw [jointBackground_expectation, add_zero, joint_firstX_zero hn u v hu, mul_zero]

theorem background_lastX_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    pauliExpectation (jointBackground u v) (unitBit n (n-2)) (unitBit n (n-1)) 1 = 0 := by
  rw [jointBackground_expectation, joint_lastX_zero hn u v hu, mul_zero]

theorem background_internalX_zero {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u v : ℂ) (hv : v * star v = 1) :
    pauliExpectation (jointBackground u v) (adjacentMask n j) 0 1 = 0 := by
  rw [jointBackground_expectation, add_zero, joint_internalX_zero_closed hn he j hj hjn u v hv,
    mul_zero]

theorem background_firstY_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    pauliExpectation (jointBackground u v) (unitBit n 0 + unitBit n (n-1))
      (UnifiedEJM.MaskFacts.cutTail n 0) Complex.I = 0 := by
  rw [jointBackground_expectation, UnifiedEJM.MaskFacts.h_firstY (by omega),
    joint_firstY_zero hn u v hu, mul_zero]

theorem background_lastY_zero {n : ℕ} (hn : 5 ≤ n) (u v : ℂ) (hu : u * star u = 1) :
    pauliExpectation (jointBackground u v) (unitBit n (n-1) + unitBit n (n-2))
      (unitBit n (n-1)) Complex.I = 0 := by
  rw [jointBackground_expectation, UnifiedEJM.MaskFacts.h_lastY,
    joint_lastY_zero hn u v hu, mul_zero]

theorem background_internalY_zero {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u v : ℂ) (hv : v * star v = 1) :
    pauliExpectation (jointBackground u v) (internalYMask n j)
      (UnifiedEJM.MaskFacts.cutTail n j) Complex.I = 0 := by
  rw [jointBackground_expectation, UnifiedEJM.MaskFacts.h_internalY j hj hjn,
    joint_internalY_zero_closed hn he j hj hjn u v hv, mul_zero]

theorem background_localZ_zero {n : ℕ} (hn : 5 ≤ n) (j : ℕ) (hj : j < n)
    (u v : ℂ) (hu : u * star u = 1) :
    pauliExpectation (jointBackground u v) (unitBit n (n-1))
      (UnifiedEJM.MaskFacts.cutTail n j) 1 = 0 := by
  rw [jointBackground_expectation, UnifiedEJM.MaskFacts.h_localZ j hj,
    joint_localZ_zero hn j hj u v hu, mul_zero]

end UnifiedEJM.EvenWalsh

