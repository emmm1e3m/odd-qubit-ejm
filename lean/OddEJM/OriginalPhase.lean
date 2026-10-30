import OddEJM.Phase
import OddEJM.Character
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/- 从真正的基本对称多项式和恢复原始 EJM 相位。 -/
namespace OddEJM

open scoped BigOperators
open Complex

/-- q 阶基本对称多项式，变量取布尔串的整数值。 -/
def elementarySymmetric {n : ℕ} (z : Bits n) (q : ℕ) : ℤ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard q,
    ∏ j ∈ s, ((z j).val : ℤ)

/-- 原文的 e₂−e₃+e₄−⋯，在取模4之前按整数精确定义。 -/
def originalExponent {n : ℕ} (z : Bits n) : ℤ :=
  ∑ q ∈ Finset.Icc 2 n, (-1 : ℤ) ^ q * elementarySymmetric z q

/-- 整数指数与模4指数定义同一个 i 的相位。 -/
noncomputable def originalDiagonal {n : ℕ} (z : Bits n) : ℂ := I ^ originalExponent z

@[simp] theorem elementarySymmetric_zero_degree {n : ℕ} (z : Bits n) :
    elementarySymmetric z 0 = 1 := by
  simp [elementarySymmetric]

@[simp] theorem elementarySymmetric_one_degree {n : ℕ} (z : Bits n) :
    elementarySymmetric z 1 = (weight z : ℤ) := by
  simp [elementarySymmetric, Finset.powersetCard_one, weight, Nat.cast_sum]

theorem alternating_elementary_sum {n : ℕ} (z : Bits n) :
    (∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q * elementarySymmetric z q) =
      ∏ j : Fin n, (1 - ((z j).val : ℤ)) := by
  have hprod := Finset.prod_one_add (f := fun j : Fin n => -((z j).val : ℤ)) Finset.univ
  rw [Finset.sum_powerset] at hprod
  simp only [Finset.card_univ, Fintype.card_fin] at hprod
  rw [show (∏ j : Fin n, (1 - ((z j).val : ℤ))) =
      ∏ j : Fin n, (1 + -((z j).val : ℤ)) by simp [sub_eq_add_neg]]
  rw [hprod]
  apply Finset.sum_congr rfl
  intro q _
  rw [elementarySymmetric, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_neg, (Finset.mem_powersetCard.mp hs).2]

theorem originalExponent_product_formula {n : ℕ} (hn : 1 ≤ n) (z : Bits n) :
    originalExponent z =
      (∏ j : Fin n, (1 - ((z j).val : ℤ))) - 1 + (weight z : ℤ) := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun q => (-1 : ℤ) ^ q * elementarySymmetric z q) (show 2 ≤ n + 1 by omega)
  have hinterval : Finset.Ico 2 (n + 1) = Finset.Icc 2 n := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hinterval, ← originalExponent, alternating_elementary_sum] at hsplit
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    elementarySymmetric_zero_degree, elementarySymmetric_one_degree, one_mul,
    neg_one_mul, zero_add] at hsplit
  linarith

theorem originalExponent_zero {n : ℕ} (hn : 1 ≤ n) :
    originalExponent (0 : Bits n) = 0 := by
  simp [originalExponent_product_formula hn]

theorem originalExponent_nonzero {n : ℕ} (hn : 1 ≤ n) (z : Bits n) (hz : z ≠ 0) :
    originalExponent z = (weight z : ℤ) - 1 := by
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra! hall
    apply hz
    ext j
    exact hall j
  have hj1 : z j = 1 := (bit_cases (z j)).resolve_left hj
  have hprod : (∏ j : Fin n, (1 - ((z j).val : ℤ))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj1, ZMod.val_one_eq_one_mod]
  rw [originalExponent_product_formula hn, hprod]
  ring

theorem originalExponent_eq_nat {n : ℕ} (hn : 1 ≤ n) (z : Bits n) :
    originalExponent z = (if z = 0 then 0 else (weight z - 1 : ℕ) : ℤ) := by
  by_cases hz : z = 0
  · subst z
    simp [originalExponent_zero hn]
  · have hw : 1 ≤ weight z := Nat.one_le_iff_ne_zero.mpr ((weight_eq_zero_iff z).not.mpr hz)
    rw [if_neg hz, originalExponent_nonzero hn z hz]
    exact (Nat.cast_sub hw).symm

theorem originalExponent_nonnegative {n : ℕ} (hn : 1 ≤ n) (z : Bits n) :
    0 ≤ originalExponent z := by
  rw [originalExponent_eq_nat hn]
  split_ifs <;> positivity

theorem originalDiagonal_eq_rawPhase_zero {n : ℕ} (hn : 1 ≤ n) (z : Bits n) :
    originalDiagonal z = rawPhase (anglePhase 0) z := by
  by_cases hz : z = 0
  · subst z
    simp [originalDiagonal, originalExponent_zero hn]
  · rw [originalDiagonal, originalExponent_eq_nat hn, if_neg hz, zpow_natCast,
      rawPhase_eq_weight_formula _ _ hz]
    simp

theorem originalDiagonal_mod_four {n : ℕ} (hn : 1 ≤ n) (z : Bits n) :
    originalDiagonal z = I ^ (originalExponent z % 4) := by
  unfold originalDiagonal
  rw [originalExponent_eq_nat hn]
  split_ifs
  · simp
  · rw [show (((weight z - 1 : ℕ) : ℤ) % 4) = (((weight z - 1) % 4 : ℕ) : ℤ) from
      (Int.natCast_mod _ _).symm]
    simp only [zpow_natCast]
    exact Complex.I_pow_eq_pow_mod _

/-- 整个参数族都等于原基本对称相位乘以支持上的可调相位。 -/
theorem rawPhase_eq_originalDiagonal {n : ℕ} (hn : 1 ≤ n) (u : ℂ) (z : Bits n) :
    rawPhase u z = originalDiagonal z * u ^ (phaseSupport z).val := by
  by_cases hz : z = 0
  · subst z
    simp [rawPhase, phaseSupport, originalDiagonal, originalExponent_zero hn]
  · rw [rawPhase_eq_weight_formula u z hz,
      originalDiagonal_eq_rawPhase_zero hn, rawPhase_eq_weight_formula _ z hz]
    simp

noncomputable def originalDiagonalAction {n : ℕ} (ψ : Vec n) : Vec n :=
  fun z => originalDiagonal z * ψ z

theorem originalDiagonalAction_eq_zero_phase {n : ℕ} (hn : 1 ≤ n) (ψ : Vec n) :
    originalDiagonalAction ψ = fun z => rawPhase (anglePhase 0) z * ψ z := by
  funext z
  rw [originalDiagonalAction, originalDiagonal_eq_rawPhase_zero hn]

/-- 原基本对称相位生成的每一列与当前构造在 t=0 时逐振幅相等。 -/
theorem measurement_basepoint_original {n : ℕ} (hn : 1 ≤ n) (label : Bits n) :
    measurement n 0 label =
      circuit (fun z => normFactor n * originalDiagonal z * character label z) := by
  unfold measurement
  congr 1
  funext z
  rw [originalDiagonal_eq_rawPhase_zero hn]

end OddEJM
