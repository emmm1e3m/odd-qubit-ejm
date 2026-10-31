import UnifiedEJM.Core
import OddEJM.Phase
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace UnifiedEJM
open OddEJM

open scoped BigOperators
open Complex

private theorem phase_Q_zero : Q20 (0 : Bits 5) = 1 := by
  norm_num [Q]

@[simp] theorem background_zero (n : ℕ) (u : ℂ) : background u (0 : Bits n) = u := by
  simp [background, q, ZMod.val_one_eq_one_mod]

@[simp] theorem corrected_zero (n : ℕ) (u : ℂ) : corrected u (0 : Bits n) = I := by
  simp [corrected, deltaZero]

@[simp] theorem rawPhase_zero (n : ℕ) (u : ℂ) : rawPhase u (0 : Bits n) = 1 := by
  simp [rawPhase]

/-- 原始相位与背景加单点缺陷逐振幅完全相同。 -/
theorem rawPhase_eq_negI_corrected {n : ℕ} (u : ℂ) (z : Bits n) :
    rawPhase u z = -I * corrected u z := by
  by_cases hz : z = 0
  · subst z
    simp
  · simp [rawPhase, corrected, deltaZero, hz, background, mul_assoc]

theorem rawPhase_norm {n : ℕ} (u : ℂ) (hu : ‖u‖ = 1) (z : Bits n) :
    ‖rawPhase u z‖ = 1 := by
  by_cases hz : z = 0
  · simp [rawPhase, hz]
  · simp [rawPhase, hz, norm_pow, hu]

@[simp] theorem anglePhase_norm (t : ℝ) : ‖anglePhase t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I t

@[simp] theorem anglePhase_zero : anglePhase 0 = 1 := by
  simp [anglePhase]

theorem rawPhase_angle_norm {n : ℕ} (t : ℝ) (z : Bits n) :
    ‖rawPhase (anglePhase t) z‖ = 1 :=
  rawPhase_norm _ (anglePhase_norm t) z

theorem rawPhase_basepoint {n : ℕ} (z : Bits n) :
    rawPhase (anglePhase 0) z = if z = 0 then 1 else -I * I ^ weight z := by
  simp [rawPhase]

theorem weight_eq_zero_iff {n : ℕ} (z : Bits n) : weight z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext j
    have hj : (z j).val ≤ weight z :=
      Finset.single_le_sum (fun k _ => Nat.zero_le ((z k).val)) (Finset.mem_univ j)
    exact (ZMod.val_eq_zero _).mp (Nat.le_zero.mp (hj.trans_eq hz))
  · rintro rfl
    simp

theorem rawPhase_eq_weight_formula {n : ℕ} (u : ℂ) (z : Bits n) (hz : z ≠ 0) :
    rawPhase u z = I ^ (weight z - 1) * u ^ (phaseSupport z).val := by
  have hw : 1 ≤ weight z := Nat.one_le_iff_ne_zero.mpr ((weight_eq_zero_iff z).not.mpr hz)
  have hi : -I * I ^ weight z = I ^ (weight z - 1) := by
    calc
      -I * I ^ weight z = -I * (I ^ (weight z - 1) * I) := by
        rw [← pow_succ, Nat.sub_add_cancel hw]
      _ = (-I * I) * I ^ (weight z - 1) := by ring
      _ = I ^ (weight z - 1) := by simp
  simp [rawPhase, phaseSupport, hz, hi]

theorem rawPhase_star_mul_self {n : ℕ} (u : ℂ) (hu : ‖u‖ = 1) (z : Bits n) :
    star (rawPhase u z) * rawPhase u z = 1 := by
  simpa only [Complex.star_def, rawPhase_norm u hu z, one_pow, ofReal_one] using
    Complex.conj_mul' (rawPhase u z)


/-- 新核的完整相位仍从原基本对称相位逐输入出发。 -/
theorem rawPhase_eq_originalDiagonal {n : ℕ} (hn : 1 ≤ n) (u : ℂ) (z : Bits n) :
    rawPhase u z = originalDiagonal z * u ^ (phaseSupport z).val := by
  by_cases hz : z = 0
  · subst z
    simp [rawPhase, phaseSupport, originalDiagonal, originalExponent_zero hn]
  · rw [rawPhase_eq_weight_formula u z hz,
      originalDiagonal_eq_rawPhase_zero hn, OddEJM.rawPhase_eq_weight_formula _ z hz]
    simp

/-- 零参数逐列精确恢复指定 EJM。 -/
theorem measurement_basepoint_original {n : ℕ} (hn : 1 ≤ n) (label : Bits n) :
    measurement n 0 label =
      circuit (fun z => normFactor n * originalDiagonal z * character label z) := by
  unfold measurement
  congr 1
  funext z
  rw [rawPhase_eq_originalDiagonal hn]
  simp


/-- 位值表示与正文的单点减法完全一致。 -/
theorem phaseSupport_val {n : ℕ} (z : Bits n) :
    (phaseSupport z).val = (q z).val - (if z = 0 then 1 else 0) := by
  by_cases hz : z = 0
  · subst z
    simp only [phaseSupport, ite_true, ZMod.val_zero, q_zero, ZMod.val_one_eq_one_mod, Nat.one_mod, Nat.sub_self]
  · simp [phaseSupport, hz]

/-- 幂相位与论文中的实指数相位严格相同。 -/
theorem anglePhase_bit (t : ℝ) (b : Bit) :
    anglePhase t ^ b.val = Complex.exp (((t * (b.val : ℝ) : ℝ) : ℂ) * I) := by
  rcases bit_cases b with rfl | rfl <;> simp [anglePhase, ZMod.val_one_eq_one_mod]

theorem rawPhase_exp {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (z : Bits n) :
    rawPhase (anglePhase t) z = originalDiagonal z *
      Complex.exp (((t * ((phaseSupport z).val : ℝ) : ℝ) : ℂ) * I) := by
  rw [rawPhase_eq_originalDiagonal hn, anglePhase_bit]

end UnifiedEJM

