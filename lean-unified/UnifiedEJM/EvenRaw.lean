import UnifiedEJM.Core
import OddEJM.Defect
import OddEJM.LocalExpectation
import OddEJM.WeightPhase
import OddEJM.Orthonormal
import Mathlib.Tactic

namespace UnifiedEJM.EvenRaw
open OddEJM Complex
open scoped BigOperators

def background {n : ℕ} (qa qb : Bits n → Bit) (u v : ℂ) (z : Bits n) : ℂ :=
  I ^ weight z * u ^ (qa z).val * v ^ (qb z).val

def corrected {n : ℕ} (qa qb : Bits n → Bit) (u v : ℂ) (z : Bits n) : ℂ :=
  background qa qb u v z + (I - u * v) * deltaZero z

def raw {n : ℕ} (qa qb : Bits n → Bit) (u v : ℂ) (z : Bits n) : ℂ :=
  if z = 0 then 1 else -I * background qa qb u v z

@[simp] theorem raw_zero {n : ℕ} (qa qb : Bits n → Bit) (u v : ℂ) :
    raw qa qb u v 0 = 1 := by simp [raw]

theorem raw_norm {n : ℕ} (qa qb : Bits n → Bit) (u v : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (z : Bits n) : ‖raw qa qb u v z‖ = 1 := by
  by_cases hz : z = 0 <;> simp [raw, background, hz, norm_mul, norm_pow, hu, hv]

theorem raw_eq_corrected {n : ℕ} (qa qb : Bits n → Bit) (u v : ℂ)
    (ha0 : qa 0 = 1) (hb0 : qb 0 = 1) (z : Bits n) :
    raw qa qb u v z = -I * corrected qa qb u v z := by
  by_cases hz : z = 0
  · subst z
    simp [raw, corrected, background, deltaZero, ha0, hb0, ZMod.val_one_eq_one_mod]
  · simp [raw, corrected, deltaZero, hz]

/-- 任意背景相位的真实Pauli期望到字符和的桥。 -/
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

theorem raw_expectation {n : ℕ} (qa qb : Bits n → Bit) (u v c : ℂ) (a b : Bits n)
    (ha0 : qa 0 = 1) (hb0 : qb 0 = 1) (ha : a ≠ 0)
    (hc : c * character b a = star c) :
    pauliExpectation (raw qa qb u v) a b c =
      pauliExpectation (background qa qb u v) a b c +
      ((2 * (c * star (I ^ weight a) *
        star (u ^ (qa a).val * v ^ (qb a).val) * (I - u*v)).re : ℝ) : ℂ) := by
  have he : raw qa qb u v = fun z => -I * corrected qa qb u v z :=
    funext (raw_eq_corrected qa qb u v ha0 hb0)
  rw [he, pauliExpectation_scale]
  have hi : star (-I) * (-I) = 1 := by norm_num [Complex.star_def]
  rw [hi, one_mul]
  unfold corrected
  rw [pauliExpectation_add_delta_hermitian _ _ _ _ _ ha hc]
  congr 2
  congr 3
  simp only [background, star_mul]
  ring

lemma classI_cross (α β : ℝ) :
    (-I * star (anglePhase α) * (I - anglePhase α * anglePhase β)).re =
      Real.cos α - Real.sin β := by
  have hu := anglePhase_star_mul α
  have he : -I * star (anglePhase α) * (I - anglePhase α * anglePhase β) =
      star (anglePhase α) + I * anglePhase β := by
    calc
      _ = star (anglePhase α) * (-(I*I)) +
          I * (star (anglePhase α) * anglePhase α) * anglePhase β := by ring
      _ = _ := by rw [hu]; simp
  rw [he]
  simp [anglePhase, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, sub_eq_add_neg]

lemma classII_cross (α β : ℝ) :
    (-star (anglePhase β) * (I - anglePhase α * anglePhase β)).re =
      Real.cos α - Real.sin β := by
  have hv := anglePhase_star_mul β
  have he : -star (anglePhase β) * (I - anglePhase α * anglePhase β) =
      anglePhase α - I * star (anglePhase β) := by
    calc
      _ = anglePhase α * (star (anglePhase β) * anglePhase β) -
          I * star (anglePhase β) := by ring
      _ = _ := by rw [hv]; ring
  rw [he]
  simp [anglePhase, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, sub_eq_add_neg]

theorem raw_expectation_classI {n : ℕ} (qa qb : Bits n → Bit) (α β : ℝ)
    (a b : Bits n) (c : ℂ) (ha0 : qa 0 = 1) (hb0 : qb 0 = 1) (ha : a ≠ 0)
    (hc : c * character b a = star c)
    (hbg : pauliExpectation (background qa qb (anglePhase α) (anglePhase β)) a b c = 0)
    (hg : c * star (I ^ weight a) = -I) (hqa : qa a = 1) (hqb : qb a = 0) :
    pauliExpectation (raw qa qb (anglePhase α) (anglePhase β)) a b c =
      ((2 * (Real.cos α - Real.sin β) : ℝ) : ℂ) := by
  rw [raw_expectation qa qb _ _ _ _ _ ha0 hb0 ha hc, hbg, zero_add]
  simp only [hg, hqa, hqb, ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.one_mod,
    pow_zero, pow_one, mul_one]
  rw [classI_cross]

theorem raw_expectation_classII {n : ℕ} (qa qb : Bits n → Bit) (α β : ℝ)
    (a b : Bits n) (c : ℂ) (ha0 : qa 0 = 1) (hb0 : qb 0 = 1) (ha : a ≠ 0)
    (hc : c * character b a = star c)
    (hbg : pauliExpectation (background qa qb (anglePhase α) (anglePhase β)) a b c = 0)
    (hg : c * star (I ^ weight a) = -1) (hqa : qa a = 0) (hqb : qb a = 1) :
    pauliExpectation (raw qa qb (anglePhase α) (anglePhase β)) a b c =
      ((2 * (Real.cos α - Real.sin β) : ℝ) : ℂ) := by
  rw [raw_expectation qa qb _ _ _ _ _ ha0 hb0 ha hc, hbg, zero_add]
  simp only [hg, hqa, hqb, ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.one_mod,
    pow_zero, pow_one, one_mul, neg_one_mul]
  rw [classII_cross]

/-- 归一化后真实局部分量，适用于任意双参数。 -/
theorem normalized_expectation {n : ℕ} (hn : 0 < n) (f : Vec n)
    (a b : Bits n) (c : ℂ) (m : ℝ)
    (hraw : pauliExpectation f a b c = ((2 * m : ℝ) : ℂ)) :
    pauliExpectation (fun z => normFactor n * f z) a b c =
      ((m / (2 : ℝ) ^ (n - 1) : ℝ) : ℂ) := by
  rw [pauliExpectation_scale, hraw]
  have hp : (2 : ℂ) ^ n = (2 : ℂ) ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hc := normFactor_card n
  rw [hp] at hc
  have hd : (2 : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  apply (eq_div_iff hd).mpr
  calc
    _ = (star (normFactor n) * normFactor n * ((2 : ℂ) ^ (n - 1) * 2)) * (m : ℂ) := by ring
    _ = m := by rw [hc, one_mul]

end UnifiedEJM.EvenRaw

