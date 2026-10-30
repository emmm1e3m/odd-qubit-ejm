import OddEJM.Phase
import OddEJM.Defect
import Mathlib.Tactic.Ring

namespace OddEJM

open scoped BigOperators
open Complex

theorem pauliExpectation_scale {n : ℕ} (f : Vec n) (s : ℂ) (a b : Bits n) (c : ℂ) :
    pauliExpectation (fun z => s * f z) a b c =
      (star s * s) * pauliExpectation f a b c := by
  simp only [pauliExpectation, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem rawPhase_pauliExpectation {n : ℕ} (u c : ℂ) (a b : Bits n) :
    pauliExpectation (rawPhase u) a b c = pauliExpectation (corrected u) a b c := by
  have hf : rawPhase u = fun z : Bits n => -I * corrected u z :=
    funext (rawPhase_eq_negI_corrected u)
  rw [hf, pauliExpectation_scale]
  simp

theorem rawPhase_expectation_from_background {n : ℕ} (u c : ℂ) (a b : Bits n)
    (ha : a ≠ 0) (hc : c * character b a = star c)
    (hbg : pauliExpectation (background u) a b c = 0) :
    pauliExpectation (rawPhase u) a b c =
      ((2 * (c * star (I ^ weight a) * star (u ^ (Q (compress a)).val) * (I - u)).re : ℝ) : ℂ) := by
  rw [rawPhase_pauliExpectation]
  unfold corrected
  rw [pauliExpectation_add_delta_hermitian _ _ _ _ _ ha hc, hbg, zero_add]
  congr 3
  simp only [background, star_mul]
  ring

theorem anglePhase_star_mul (t : ℝ) : star (anglePhase t) * anglePhase t = 1 := by
  simpa only [Complex.star_def, anglePhase_norm, one_pow, ofReal_one] using
    Complex.conj_mul' (anglePhase t)

theorem classI_cross_re (t : ℝ) : (-I * (I - anglePhase t)).re = 1 - Real.sin t := by
  simp [anglePhase, Complex.mul_re, Complex.exp_ofReal_mul_I_im]

theorem classII_cross_re (t : ℝ) : (-star (anglePhase t) * (I - anglePhase t)).re =
    1 - Real.sin t := by
  have heq : -star (anglePhase t) * (I - anglePhase t) = 1 - I * star (anglePhase t) := by
    calc
      _ = star (anglePhase t) * anglePhase t - I * star (anglePhase t) := by ring
      _ = _ := by rw [anglePhase_star_mul]
  rw [heq]
  simp [anglePhase, Complex.mul_re, Complex.exp_ofReal_mul_I_im]

/-- 类别I的条件由具体拉回掩码证明；此处完成实际复期望的解析计算。 -/
theorem rawPhase_expectation_classI {n : ℕ} (t : ℝ) (c : ℂ) (a b : Bits n)
    (ha : a ≠ 0) (hc : c * character b a = star c)
    (hbg : pauliExpectation (background (anglePhase t)) a b c = 0)
    (hgamma : c * star (I ^ weight a) = -I) (hq : Q (compress a) = 0) :
    pauliExpectation (rawPhase (anglePhase t)) a b c = ((2 * (1 - Real.sin t) : ℝ) : ℂ) := by
  rw [rawPhase_expectation_from_background _ _ _ _ ha hc hbg]
  simp only [hgamma, hq, ZMod.val_zero, pow_zero, star_one, mul_one]
  rw [classI_cross_re]

/-- 类别II的条件由具体拉回掩码证明。 -/
theorem rawPhase_expectation_classII {n : ℕ} (t : ℝ) (c : ℂ) (a b : Bits n)
    (ha : a ≠ 0) (hc : c * character b a = star c)
    (hbg : pauliExpectation (background (anglePhase t)) a b c = 0)
    (hgamma : c * star (I ^ weight a) = -1) (hq : Q (compress a) = 1) :
    pauliExpectation (rawPhase (anglePhase t)) a b c = ((2 * (1 - Real.sin t) : ℝ) : ℂ) := by
  rw [rawPhase_expectation_from_background _ _ _ _ ha hc hbg]
  simp only [hgamma, hq, ZMod.val_one_eq_one_mod, Nat.one_mod, pow_one, neg_one_mul]
  rw [classII_cross_re]

end OddEJM
