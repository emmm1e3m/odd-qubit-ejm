import OddEJM.Character

/- 从真实相位乘积到 Walsh 条件的有限和桥梁；u、v 可任意。 -/
namespace OddEJM

open scoped BigOperators

def phaseCorrelation {n : ℕ} (Q : Bits n → Bit) (h a : Bits n) (u v : ℂ) : ℂ :=
  ∑ z, character h z * u ^ (Q z).val * v ^ (Q (z + a)).val

theorem phase_product_expansion (u v : ℂ) (a b : Bit) :
    4 * (u ^ a.val * v ^ b.val) =
      (1 + u) * (1 + v) +
      (1 - u) * (1 + v) * bitSign a +
      (1 + u) * (1 - v) * bitSign b +
      (1 - u) * (1 - v) * bitSign (a + b) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp only [zero_add, add_zero, CharTwo.add_self_eq_zero] <;>
    norm_num [bitSign, show (1 : Bit).val = 1 by decide] <;> ring

theorem four_walsh_expansion {n : ℕ} (Q : Bits n → Bit) (h a : Bits n) (u v : ℂ) :
    4 * phaseCorrelation Q h a u v =
      (1 + u) * (1 + v) * (∑ z, character h z) +
      (1 - u) * (1 + v) * walsh Q h +
      (1 + u) * (1 - v) * walsh (fun z => Q (z + a)) h +
      (1 - u) * (1 - v) * walsh (derivative Q a) h := by
  have hp (z : Bits n) :
      4 * (character h z * u ^ (Q z).val * v ^ (Q (z + a)).val) =
        (1 + u) * (1 + v) * character h z +
        (1 - u) * (1 + v) * bitSign (Q z + dot h z) +
        (1 + u) * (1 - v) * bitSign (Q (z + a) + dot h z) +
        (1 - u) * (1 - v) * bitSign (derivative Q a z + dot h z) := by
    calc
      _ = character h z * (4 * (u ^ (Q z).val * v ^ (Q (z + a)).val)) := by ring
      _ = _ := by
        rw [phase_product_expansion]
        simp only [character, derivative, bitSign_add]
        ring
  unfold phaseCorrelation
  rw [Finset.mul_sum]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, walsh]

theorem walsh_translate {n : ℕ} (Q : Bits n → Bit) (h a : Bits n) :
    walsh (fun z => Q (z + a)) h = character h a * walsh Q h := by
  unfold walsh
  calc
    _ = ∑ z, bitSign (Q ((z + a) + a) + dot h (z + a)) :=
      (Equiv.sum_comp (Equiv.addRight a) (fun z => bitSign (Q (z + a) + dot h z))).symm
    _ = ∑ z, character h a * bitSign (Q z + dot h z) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [add_assoc, bits_add_self, add_zero, dot_add, bitSign_add, character]
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem phaseCorrelation_zero_classI {n : ℕ} (Q : Bits n → Bit) (h a : Bits n)
    (u v : ℂ) (hh : h ≠ 0) (ha : dot h a = 1) (hQ : walsh Q h = 0) :
    phaseCorrelation Q h a u v = 0 := by
  have he := four_walsh_expansion Q h a u v
  rw [character_sum, if_neg hh, hQ, walsh_translate, hQ,
    derivative_walsh_zero Q h a ha] at he
  norm_num at he
  exact he

theorem phaseCorrelation_zero_classII {n : ℕ} (Q : Bits n → Bit) (h a : Bits n)
    (u v : ℂ) (hh : h ≠ 0) (ha : dot h a = 0) (huv : u * v = 1)
    (hQ : walsh (derivative Q a) h = 0) : phaseCorrelation Q h a u v = 0 := by
  have he := four_walsh_expansion Q h a u v
  have hc : character h a = 1 := by simp [character, ha]
  rw [character_sum, if_neg hh, walsh_translate, hc, hQ] at he
  have hcoeff : (1 - u) * (1 + v) + (1 + u) * (1 - v) = 0 := by
    calc
      _ = 2 - 2 * (u * v) := by ring
      _ = 0 := by rw [huv]; ring
  have hz : 4 * phaseCorrelation Q h a u v = 0 := by
    calc
      _ = ((1 - u) * (1 + v) + (1 + u) * (1 - v)) * walsh Q h := by
        rw [he]
        ring
      _ = 0 := by rw [hcoeff]; ring
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem first_cross_term (t : ℝ) :
    ((Complex.I - anglePhase t) * (-Complex.I)).re = 1 - Real.sin t := by
  simp [anglePhase, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.exp_ofReal_mul_I_im]

theorem second_cross_term (t : ℝ) :
    (1 - Complex.I * star (anglePhase t)).re = 1 - Real.sin t := by
  simp [anglePhase, Complex.mul_re, Complex.sub_re, Complex.exp_ofReal_mul_I_im]

end OddEJM
