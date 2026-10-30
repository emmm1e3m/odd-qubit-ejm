import OddEJM.Core
import Mathlib.Tactic.Ring

namespace OddEJM

open scoped BigOperators
open Complex

private theorem bits_neg_self {n : ℕ} (a : Bits n) : -a = a := by
  funext j
  exact ZMod.neg_eq_self_mod_two (a j)

private theorem bits_add_self {n : ℕ} (a : Bits n) : a + a = 0 := by
  funext j
  exact CharTwo.add_self_eq_zero (a j)

private theorem add_eq_zero_iff_eq {n : ℕ} (z a : Bits n) : z + a = 0 ↔ z = a := by
  rw [add_eq_zero_iff_eq_neg, bits_neg_self]

/-- 任意非零翻转下，单点缺陷的期望只有两个交叉项。 -/
theorem pauliExpectation_add_delta {n : ℕ} (f : Vec n) (d c : ℂ)
    (a b : Bits n) (ha : a ≠ 0) :
    pauliExpectation (fun z => f z + d * deltaZero z) a b c =
      pauliExpectation f a b c + star (f a) * c * d +
        star d * c * character b a * f a := by
  have hpoint (z : Bits n) :
      star (f (z + a) + d * deltaZero (z + a)) * c * character b z *
          (f z + d * deltaZero z) =
        star (f (z + a)) * c * character b z * f z +
          (if z = 0 then star (f a) * c * d else 0) +
          (if z = a then star d * c * character b a * f a else 0) := by
    by_cases hz : z = 0
    · subst z
      simp [deltaZero, ha, Ne.symm ha, character, dot, bitSign]
      ring
    · by_cases hza : z = a
      · subst z
        simp [deltaZero, ha, bits_add_self]
        ring
      · have hsum : z + a ≠ 0 := by
          exact fun h => hza ((add_eq_zero_iff_eq z a).mp h)
        simp [deltaZero, hz, hza, hsum]
  simp only [pauliExpectation]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib]
  simp

/-- 当Pauli相位满足自伴条件时，两个交叉项确为共轭对。 -/
theorem pauliExpectation_add_delta_hermitian {n : ℕ} (f : Vec n) (d c : ℂ)
    (a b : Bits n) (ha : a ≠ 0) (hc : c * character b a = star c) :
    pauliExpectation (fun z => f z + d * deltaZero z) a b c =
      pauliExpectation f a b c +
        ((2 * (star (f a) * c * d).re : ℝ) : ℂ) := by
  rw [pauliExpectation_add_delta f d c a b ha]
  have hcross : star d * c * character b a * f a = star (star (f a) * c * d) := by
    rw [show star d * c * character b a * f a = star d * (c * character b a) * f a by ring]
    rw [hc]
    simp only [star_mul, star_star]
    ring
  rw [hcross, add_assoc]
  congr 1
  exact Complex.add_conj _

end OddEJM
