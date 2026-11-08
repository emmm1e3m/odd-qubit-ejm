import UnifiedEJM.Features
import UnifiedEJM.PhysicsLaurent
import Mathlib.Tactic

open OddEJM
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

/-- 自由位串的总奇偶同态。 -/
def parityHom (L : ℕ) : Bits L →+ Bit where
  toFun x := ∑ j, x j
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

lemma parity_surjective {L : ℕ} (hL : 1 ≤ L) :
    Function.Surjective (parityHom L) := by
  intro p
  let j : Fin L := ⟨0, by omega⟩
  refine ⟨Pi.single j p, ?_⟩
  simp [parityHom]

/-- 任意正长度的纤维计数；没有有限长度外推。 -/
theorem parity_fiber_card {L : ℕ} (hL : 1 ≤ L) (p : Bit) :
    Nat.card {x : Bits L // parityHom L x = p} = 2^(L-1) := by
  have hs := parity_surjective hL
  have hker := AddSubgroup.card_ker_mul_card_of_surjective hs
  have hcards : Nat.card (parityHom L).ker * 2 = 2^L := by
    simpa [Nat.card_fun, Nat.card_zmod] using hker
  have hpower : 2^L = 2^(L-1)*2 := by
    nth_rw 1 [show L = (L-1)+1 by omega]
    rw [pow_succ]
  have hk : Nat.card (parityHom L).ker = 2^(L-1) := by omega
  exact (Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hs p)).trans hk

@[simp] theorem parity_zero (L : ℕ) : parityHom L 0 = 0 := map_zero _
@[simp] theorem parity_one (L : ℕ) : parityHom L (1 : Bits L) = (L : Bit) := by
  simp [parityHom]

theorem sum_parity {R : Type*} [CommRing R] {L : ℕ} (hL : 1 ≤ L)
    (f : Bit → R) :
    (∑ x : Bits L, f (parityHom L x)) = (2^(L-1) : R) * ∑ p : Bit, f p := by
  rw [← Fintype.sum_fiberwise (parityHom L)]
  simp_rw [show ∀ p : Bit, ∀ x : {x : Bits L // parityHom L x = p},
    f (parityHom L x.val) = f p from fun p x => congrArg f x.property]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc (p : Bit) : Fintype.card {x : Bits L // parityHom L x = p} = 2^(L-1) := by
    simpa only [Nat.card_eq_fintype_card] using parity_fiber_card hL p
  simp_rw [hc, Nat.cast_pow, Nat.cast_ofNat]
  exact (Finset.mul_sum _ _ _).symm

/-- 类别依次为全零、全一、混合偶、混合奇。 -/
def wordClass {L : ℕ} (x : Bits L) : Fin 4 :=
  if x = 0 then 0 else if x = 1 then 1 else if parityHom L x = 0 then 2 else 3

def mixedClass (p : Bit) : Fin 4 := if p = 0 then 2 else 3

/-- 这是精确计数多项式，不把它作为输入假设。 -/
def classWeight {R : Type*} [CommRing R] (lp : Bit) (X : R) : Fin 4 → R :=
  ![1, 1, X - 1 - (if lp = 0 then 1 else 0), X - (if lp = 1 then 1 else 0)]

theorem zero_ne_one_word {L : ℕ} (hL : 1 ≤ L) : (0 : Bits L) ≠ 1 := by
  intro h
  have he := congrFun h ⟨0, by omega⟩
  exact zero_ne_one he

/-- 任意测试函数都可按四类精确求和，故适用于四副本Gaussian系数核。 -/
theorem sum_wordClass {R : Type*} [CommRing R] {L : ℕ} (hL : 1 ≤ L)
    (f : Fin 4 → R) :
    (∑ x : Bits L, f (wordClass x)) =
      ∑ c : Fin 4, classWeight (L : Bit) (2^(L-1) : R) c * f c := by
  classical
  have h01 := zero_ne_one_word hL
  have pointwise (x : Bits L) :
      f (wordClass x) = f (mixedClass (parityHom L x)) +
        (if x = 0 then f 0 - f 2 else 0) +
        (if x = 1 then f 1 - f (mixedClass (L : Bit)) else 0) := by
    by_cases hx0 : x = 0
    · subst x
      simp [wordClass, mixedClass, h01]
    · by_cases hx1 : x = 1
      · subst x
        simp [wordClass, mixedClass, hx0]
      · simp [wordClass, mixedClass, hx0, hx1]
  simp_rw [pointwise, Finset.sum_add_distrib]
  rw [sum_parity hL (fun p => f (mixedClass p))]
  have hu : (Finset.univ : Finset Bit) = {0,1} := by decide
  simp only [hu, Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rcases bit_cases (L : Bit) with hp | hp <;>
    simp [classWeight, mixedClass, hp, Fin.sum_univ_succ] <;> ring

end UnifiedEJM.PrefixCounts
