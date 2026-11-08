import UnifiedEJM.Multipartite
import UnifiedEJM.LocalExpectation
import Mathlib.Tactic

noncomputable section
open OddEJM Complex
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace UnifiedEJM.PurityTail

/-- 与完整物理种子使用同一个整体相位的归一化背景。 -/
def backgroundSeed (n : ℕ) (t : ℝ) : Vec n :=
  circuit (fun z => normFactor n * (-I * UnifiedEJM.background (anglePhase t) z))

def defectWeight (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

theorem background_phase_norm {n : ℕ} (t : ℝ) (z : Bits n) :
    ‖-I * UnifiedEJM.background (anglePhase t) z‖ = 1 := by
  simp [UnifiedEJM.background, norm_mul, norm_pow]

theorem background_phase_star_mul {n : ℕ} (t : ℝ) (z : Bits n) :
    star (-I * UnifiedEJM.background (anglePhase t) z) *
      (-I * UnifiedEJM.background (anglePhase t) z) = 1 := by
  simpa only [Complex.star_def, background_phase_norm, one_pow, ofReal_one] using
    Complex.conj_mul' (-I * UnifiedEJM.background (anglePhase t) z)

theorem backgroundSeed_normalized {n : ℕ} (hn : 0 < n) (t : ℝ) :
    OddEJM.inner (backgroundSeed n t) (backgroundSeed n t) = 1 :=
  Physical.seed_normalized hn _ (background_phase_star_mul t)

theorem actual_seed_normalized {n : ℕ} (hn : 0 < n) (t : ℝ) :
    OddEJM.inner (UnifiedEJM.seed n t) (UnifiedEJM.seed n t) = 1 :=
  Physical.seed_normalized hn _ (rawPhase_star_mul_self _ (anglePhase_norm t))

theorem normFactor_sq (n : ℕ) :
    star (normFactor n) * normFactor n = (defectWeight n : ℂ) := by
  have h := normFactor_card n
  have hp : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (mul_right_cancel₀ hp)
  rw [h]
  simp [defectWeight, ← mul_pow, hp]

theorem phase_overlap_point {n : ℕ} (t : ℝ) (z : Bits n) :
    star (-I * UnifiedEJM.background (anglePhase t) z) *
      UnifiedEJM.rawPhase (anglePhase t) z =
      1 + (I * star (anglePhase t) - 1) * deltaZero z := by
  by_cases hz : z = 0
  · subst z
    simp [deltaZero]
  · have hp := background_phase_star_mul t z
    simpa [UnifiedEJM.rawPhase, UnifiedEJM.background, deltaZero, hz, mul_assoc] using hp

/-- 原电路种子与背景的精确复重叠，含零串修正。 -/
theorem background_seed_overlap {n : ℕ} (hn : 0 < n) (t : ℝ) :
    OddEJM.inner (backgroundSeed n t) (UnifiedEJM.seed n t) =
      1 - (defectWeight n : ℂ) + (defectWeight n : ℂ) * I * star (anglePhase t) := by
  rw [backgroundSeed, UnifiedEJM.seed, circuit_inner hn]
  unfold OddEJM.inner
  have hh (z : Bits n) :
      star (normFactor n * (-I * UnifiedEJM.background (anglePhase t) z)) *
        (normFactor n * UnifiedEJM.rawPhase (anglePhase t) z) =
      (star (normFactor n) * normFactor n) *
        (1 + (I * star (anglePhase t) - 1) * deltaZero z) := by
    rw [← phase_overlap_point]
    simp only [star_mul]
    ring
  simp_rw [hh]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcard : (∑ _z : Bits n, (1 : ℂ)) = (2 : ℂ)^n := by
    simp [Fintype.card_fun]
  have hdelta : (∑ z : Bits n, deltaZero z) = 1 := by simp [deltaZero]
  rw [hcard, hdelta, mul_one, mul_add, normFactor_card, normFactor_sq]
  ring

theorem background_seed_overlap_re {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (OddEJM.inner (backgroundSeed n t) (UnifiedEJM.seed n t)).re =
      1 - defectWeight n + defectWeight n * Real.sin t := by
  rw [background_seed_overlap hn]
  simp [anglePhase, Complex.mul_re, Complex.exp_ofReal_mul_I_im]

theorem background_seed_overlap_normSq {n : ℕ} (hn : 0 < n) (t : ℝ) :
    Complex.normSq (OddEJM.inner (backgroundSeed n t) (UnifiedEJM.seed n t)) =
      1 - 2 * defectWeight n * (1 - defectWeight n) * (1 - Real.sin t) := by
  rw [background_seed_overlap hn]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.add_im, Complex.sub_im, Complex.one_im, mul_zero, zero_mul, sub_zero,
    add_zero, zero_add, mul_one, one_mul, zero_sub]
  simp only [anglePhase, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination (defectWeight n)^2 * (Real.sin_sq_add_cos_sq t)

theorem defectWeight_pos (n : ℕ) : 0 < defectWeight n := by
  unfold defectWeight
  positivity

theorem defectWeight_le {n k : ℕ} (hkn : k ≤ n) : defectWeight n ≤ defectWeight k := by
  exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) hkn

/-- n=10已经严格成立；保留(1-a)因子提供严格余量。 -/
theorem tail_scalar_lt_half {n : ℕ} (hn : 10 ≤ n) :
    (3 : ℝ)/8 + 4 * Real.sqrt (defectWeight n * (1 - defectWeight n)) < 1/2 := by
  have ha := defectWeight_pos n
  have hb : defectWeight n ≤ (1 : ℝ)/1024 := by
    have h := defectWeight_le hn
    norm_num [defectWeight] at h ⊢
    exact h
  have hc : 0 ≤ defectWeight n * (1 - defectWeight n) := mul_nonneg ha.le (by linarith)
  have hs := Real.sq_sqrt hc
  have hs0 := Real.sqrt_nonneg (defectWeight n * (1 - defectWeight n))
  have hsq : defectWeight n * (1 - defectWeight n) < (1 : ℝ)/1024 := by
    nlinarith [sq_pos_of_pos ha]
  nlinarith

end UnifiedEJM.PurityTail
