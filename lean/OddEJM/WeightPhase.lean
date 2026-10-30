import OddEJM.Character
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.NormNum

namespace OddEJM

open scoped BigOperators
open Complex

theorem bitSign_sum {α : Type*} (s : Finset α) (f : α → Bit) :
    bitSign (∑ j ∈ s, f j) = ∏ j ∈ s, bitSign (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp only [Finset.sum_insert hj, Finset.prod_insert hj, bitSign_add, ih]

theorem weight_phase_product {n : ℕ} (z : Bits n) :
    I ^ weight z = ∏ j, I ^ (z j).val :=
  (Finset.prod_pow_eq_pow_sum Finset.univ (fun j => (z j).val) I).symm

theorem bit_weight_phase_ratio (a z : Bit) :
    star (I ^ (z + a).val) * I ^ z.val =
      star (I ^ a.val) * bitSign (a * z) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases z with rfl | rfl <;>
    simp only [zero_add, add_zero, CharTwo.add_self_eq_zero, zero_mul, mul_zero, one_mul] <;>
    norm_num [bitSign, ZMod.val_one_eq_one_mod]

/-- 任意长度的乘积相位比，给出报告中的 `i^(-|a|) (-1)^(a·z)`。 -/
theorem weight_phase_ratio {n : ℕ} (a z : Bits n) :
    star (I ^ weight (z + a)) * I ^ weight z =
      star (I ^ weight a) * character a z := by
  simp_rw [weight_phase_product, star_prod]
  rw [← Finset.prod_mul_distrib]
  simp_rw [Pi.add_apply, bit_weight_phase_ratio]
  rw [Finset.prod_mul_distrib]
  rw [character, dot, bitSign_sum]

/-- 实际背景Pauli期望精确变成带相位的Boolean字符和。 -/
theorem background_pauli_sum {n : ℕ} (u c : ℂ) (a b : Bits n) :
    pauliExpectation (background u) a b c =
      (c * star (I ^ weight a)) *
        ∑ z, character (a + b) z *
          star (u ^ (Q (compress (z + a))).val) * u ^ (Q (compress z)).val := by
  simp only [pauliExpectation, background]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [star_mul]
  rw [show star (u ^ (Q (compress (z + a))).val) * star (I ^ weight (z + a)) * c *
        character b z * (I ^ weight z * u ^ (Q (compress z)).val) =
      c * (star (I ^ weight (z + a)) * I ^ weight z) *
        character b z * star (u ^ (Q (compress (z + a))).val) *
          u ^ (Q (compress z)).val by ring]
  rw [weight_phase_ratio, character_add_left]
  ring

end OddEJM
