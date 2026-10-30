import OddEJM.Core
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OddEJM

open scoped BigOperators
open Complex

@[simp] theorem coord_zero (n j : ℕ) : coord (0 : Bits n) j = 0 := by
  simp [coord]

@[simp] theorem blockParity_zero (n p : ℕ) : blockParity (0 : Bits n) p = 0 := by
  simp [blockParity]

@[simp] theorem compress_zero (n : ℕ) : compress (0 : Bits n) = 0 := by
  ext j
  fin_cases j <;> simp [compress]

@[simp] theorem weight_zero (n : ℕ) : weight (0 : Bits n) = 0 := by
  simp [weight]

private theorem phase_Q_zero : Q (0 : Bits 5) = 1 := by
  norm_num [Q]

@[simp] theorem background_zero (n : ℕ) (u : ℂ) : background u (0 : Bits n) = u := by
  simp [background, phase_Q_zero, ZMod.val_one_eq_one_mod]

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

end OddEJM

