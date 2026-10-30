import OddEJM.Core

/- 任意长度的有限字符求和，不以有限 n 枚举代替一般证明。 -/
namespace OddEJM

open scoped BigOperators

theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  exact (show ∀ b : Bit, b = 0 ∨ b = 1 from by decide) b

@[simp] theorem bits_add_self {n : ℕ} (a : Bits n) : a + a = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (a i)

@[simp] theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]
@[simp] theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

theorem bitSign_add (a b : Bit) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp only [zero_add, add_zero, CharTwo.add_self_eq_zero] <;> norm_num [bitSign]

@[simp] theorem bitSign_star (b : Bit) : star (bitSign b) = bitSign b := by
  by_cases hb : b = 0 <;> simp [bitSign, hb]

@[simp] theorem bitSign_mul_self (b : Bit) : bitSign b * bitSign b = 1 := by
  by_cases hb : b = 0 <;> simp [bitSign, hb]

theorem sum_zero_of_neg_equiv {α : Type*} [Fintype α]
    (e : α ≃ α) (f : α → ℂ) (h : ∀ x, f (e x) = -f x) :
    ∑ x, f x = 0 := by
  have hs : (∑ x, f x) = -(∑ x, f x) := by
    calc
      (∑ x, f x) = ∑ x, f (e x) := (e.sum_comp f).symm
      _ = -(∑ x, f x) := by simp_rw [h]; rw [Finset.sum_neg_distrib]
  have ht : (2 : ℂ) * (∑ x, f x) = 0 := by
    calc
      _ = (∑ x, f x) + (∑ x, f x) := by ring
      _ = -(∑ x, f x) + (∑ x, f x) := congrArg (fun v => v + ∑ x, f x) hs
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

theorem sum_zero_of_neg_shift {α : Type*} [Fintype α] [AddGroup α]
    (a : α) (f : α → ℂ) (h : ∀ x, f (x + a) = -f x) :
    ∑ x, f x = 0 :=
  sum_zero_of_neg_equiv (Equiv.addRight a) f h

theorem dot_add {n : ℕ} (h z w : Bits n) : dot h (z + w) = dot h z + dot h w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_add_left {n : ℕ} (h k z : Bits n) : dot (h + k) z = dot h z + dot k z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem character_add {n : ℕ} (h z w : Bits n) :
    character h (z + w) = character h z * character h w := by
  simp only [character, dot_add, bitSign_add]

theorem character_add_left {n : ℕ} (h k z : Bits n) :
    character (h + k) z = character h z * character k z := by
  simp only [character, dot_add_left, bitSign_add]

@[simp] theorem character_star {n : ℕ} (h z : Bits n) :
    star (character h z) = character h z := bitSign_star _

@[simp] theorem character_mul_self {n : ℕ} (h z : Bits n) :
    character h z * character h z = 1 := bitSign_mul_self _

theorem weighted_character_zero {n : ℕ} (h w : Bits n) (F : Bits n → ℂ)
    (hw : dot h w = 1) (hF : ∀ z, F (z + w) = F z) :
    ∑ z, character h z * F z = 0 := by
  apply sum_zero_of_neg_shift w
  intro z
  rw [character_add, hF]
  have hc : character h w = -1 := by simp [character, hw]
  rw [hc]
  ring

theorem derivative_shift_invariant {n : ℕ} (Q : Bits n → Bit) (a z : Bits n) :
    derivative Q a (z + a) = derivative Q a z := by
  have haa : a + a = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (a i)
  simp only [derivative]
  rw [add_assoc, haa, add_zero, add_comm]

theorem derivative_walsh_zero {n : ℕ} (Q : Bits n → Bit) (h a : Bits n)
    (ha : dot h a = 1) : walsh (derivative Q a) h = 0 := by
  simp only [walsh, bitSign_add]
  rw [show (∑ z, bitSign (derivative Q a z) * bitSign (dot h z)) =
      ∑ z, character h z * bitSign (derivative Q a z) by
    apply Finset.sum_congr rfl; intro z _; simp [character, mul_comm]]
  apply weighted_character_zero h a _ ha
  intro z
  rw [derivative_shift_invariant]

theorem walsh_zero_of_affine_shift {n : ℕ} (Q : Bits n → Bit) (h w : Bits n)
    (δ : Bit) (hQ : ∀ z, Q (z + w) = Q z + δ) (hδ : δ + dot h w = 1) :
    walsh Q h = 0 := by
  unfold walsh
  apply sum_zero_of_neg_shift w
  intro z
  rw [hQ, dot_add]
  have heq : Q z + δ + (dot h z + dot h w) = (Q z + dot h z) + 1 := by
    rw [← hδ]
    ring
  rw [heq, bitSign_add, bitSign_one]
  ring

theorem character_sum {n : ℕ} (h : Bits n) :
    (∑ z, character h z) = if h = 0 then (2 : ℂ) ^ n else 0 := by
  classical
  by_cases hh : h = 0
  · subst h
    simp [character, dot, Fintype.card_fun]
  · rw [if_neg hh]
    obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
      by_contra! heq
      apply hh
      ext i
      exact heq i
    have hi1 : h i = 1 := (bit_cases (h i)).resolve_left hi
    let w : Bits n := Pi.single i 1
    have hw : dot h w = 1 := by
      simp [dot, w, Pi.single_apply, mul_ite, hi1]
    apply sum_zero_of_neg_shift w
    intro z
    rw [character_add]
    have hc : character h w = -1 := by simp [character, hw]
    simp [hc]

theorem character_orthogonality {n : ℕ} (a b : Bits n) :
    (∑ z, star (character a z) * character b z) =
      if a = b then (2 : ℂ) ^ n else 0 := by
  have heq : a + b = 0 ↔ a = b := by
    constructor
    · intro h
      have ht := congrArg (fun x : Bits n => x + b) h
      simpa [add_assoc] using ht
    · intro h
      subst a
      exact bits_add_self b
  simp_rw [character_star, ← character_add_left]
  simp only [character_sum, heq]

end OddEJM
