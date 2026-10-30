import OddEJM.Walsh
import Mathlib.Tactic

namespace OddEJM.MaskFacts
open scoped BigOperators
open Complex

/-- Pauli拉回表中截掉最后一位的尾掩码。 -/
def cutTail (n j : ℕ) : Bits n :=
  fun k => if j ≤ k.val ∧ k.val < n - 1 then 1 else 0

/-- 与电路拉回表的setBit尾掩码直接对齐。 -/
theorem cutTail_eq_setBit (n j : ℕ) :
    cutTail n j = setBit (tailMask n j) (n-1) 0 := by
  funext k
  by_cases hk : k.val = n-1
  · simp [cutTail,setBit,hk]
  · have hlt : k.val < n-1 := by omega
    simp [cutTail,setBit,tailMask,hk,hlt]

theorem x_beforeLast_internal {n : ℕ} (j : ℕ) (hj : 1 ≤ j) :
    unitBit n j + (if j = 0 then 0 else unitBit n (j-1)) = adjacentMask n j := by
  simp [show j ≠ 0 by omega,adjacentMask,add_comm]
structure ClassI {n : ℕ} (a b : Bits n) (c : ℂ) : Prop where
  ha : a ≠ 0
  hh : a + b ≠ 0
  hd : dot (a + b) a = 1
  hc : c * character b a = star c
  hg : c * star (I ^ weight a) = -I
  hq : Q (compress a) = 0

structure ClassII {n : ℕ} (a b : Bits n) (c : ℂ) : Prop where
  ha : a ≠ 0
  hh : a + b ≠ 0
  hd : dot (a + b) a = 0
  hc : c * character b a = star c
  hg : c * star (I ^ weight a) = -1
  hq : Q (compress a) = 1

theorem weight_add_disjoint {n : ℕ} (a b : Bits n)
    (hd : ∀ i, a i = 0 ∨ b i = 0) : weight (a + b) = weight a + weight b := by
  unfold weight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases hd i with hi | hi <;> simp [hi]

theorem weight_unit {n : ℕ} (j : ℕ) (hj : j < n) : weight (unitBit n j) = 1 := by
  unfold weight
  rw [Finset.sum_eq_single (⟨j,hj⟩ : Fin n)]
  · simp [unitBit, ZMod.val_one_eq_one_mod]
  · intro k _ hkj
    have hne : k.val ≠ j := fun he => hkj (Fin.ext he)
    simp [unitBit,hne]
  · simp

theorem weight_pair {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) (hne : i ≠ j) :
    weight (unitBit n i + unitBit n j) = 2 := by
  rw [weight_add_disjoint, weight_unit i hi, weight_unit j hj]
  · intro k
    by_cases hk : k.val = i
    · right; simp [unitBit,hk,hne]
    · left; simp [unitBit,hk]

theorem weight_triple {n : ℕ} (i j k : ℕ) (hi : i < n) (hj : j < n) (hk : k < n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    weight (unitBit n i + unitBit n j + unitBit n k) = 3 := by
  rw [weight_add_disjoint, weight_pair i j hi hj hij, weight_unit k hk]
  · intro l
    by_cases hl : l.val = k
    · left
      have hki : k ≠ i := Ne.symm hik
      have hkj : k ≠ j := Ne.symm hjk
      simp [unitBit,hl,hki,hkj]
    · right; simp [unitBit,hl]

theorem nonzero_of_weight {n : ℕ} {a : Bits n} (h : 0 < weight a) : a ≠ 0 := by
  intro ha
  simp [ha,weight] at h

theorem nonzero_of_dot_one {n : ℕ} {h a : Bits n} (hd : dot h a = 1) : h ≠ 0 := by
  intro hh
  simp [hh,dot] at hd

theorem dot_unit {n : ℕ} (a : Bits n) (j : ℕ) (hj : j < n) :
    dot a (unitBit n j) = a ⟨j,hj⟩ := dot_unitBit a ⟨j,hj⟩

theorem h_lastX {n : ℕ} (hn : 2 ≤ n) :
    unitBit n (n-2) + unitBit n (n-1) = tailMask n (n-2) := by
  funext k
  by_cases h2 : k.val = n-2
  · simp [unitBit,tailMask,h2,show n-2 ≠ n-1 by omega]
  by_cases h1 : k.val = n-1
  · simp [unitBit,tailMask,h1,show n-1 ≠ n-2 by omega,show n-2 ≤ n-1 by omega]
  · simp [unitBit,tailMask,h1,h2,show ¬n-2 ≤ k.val by omega]

theorem h_lastY {n : ℕ} :
    (unitBit n (n-1) + unitBit n (n-2)) + unitBit n (n-1) = unitBit n (n-2) := by
  have h := bits_add_self (unitBit n (n-1))
  linear_combination h

theorem h_localZ {n : ℕ} (j : ℕ) (hj : j < n) :
    unitBit n (n-1) + cutTail n j = tailMask n j := by
  funext k
  by_cases hk : k.val = n-1
  · simp [unitBit,cutTail,tailMask,hk,show j ≤ n-1 by omega]
  · have hlt : k.val < n-1 := by omega
    simp [unitBit,cutTail,tailMask,hk,hlt]

theorem h_firstY {n : ℕ} (hn : 2 ≤ n) :
    (unitBit n 0 + unitBit n (n-1)) + cutTail n 0 = tailMask n 1 := by
  rw [add_assoc, h_localZ 0 (by omega)]
  funext k
  by_cases hk : k.val = 0
  · simp [unitBit,tailMask,hk,CharTwo.add_self_eq_zero]
  · simp [unitBit,tailMask,hk,show 1 ≤ k.val by omega]

theorem h_internalY {n : ℕ} (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) :
    internalYMask n j + cutTail n j = internalYCharacter n j := by
  unfold internalYMask adjacentMask internalYCharacter
  rw [add_assoc, h_localZ j (by omega)]
  funext k
  by_cases hk : k.val = j
  · simp [unitBit,tailMask,hk,show j ≠ j-1 by omega,CharTwo.add_self_eq_zero]
  · by_cases hle : j ≤ k.val
    · have hlt : j+1 ≤ k.val := by omega
      simp [unitBit,tailMask,hk,hle,hlt]
    · have hlt : ¬ j+1 ≤ k.val := by omega
      simp [unitBit,tailMask,hk,hle,hlt]

/-- 邻位翻转压缩后仅有三种形状，长度只进入奇偶算术。 -/
theorem compress_adjacent {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n-1) :
    compress (adjacentMask n j) =
      if j = 1 then unitBit 5 0 + unitBit 5 1
      else if j = n-2 then unitBit 5 2 + unitBit 5 3
      else unitBit 5 1 + unitBit 5 2 := by
  have hnp : n % 2 = 1 := Nat.odd_iff.mp ho
  unfold adjacentMask
  rw [compress_add]
  by_cases h1 : j = 1
  · subst j
    simp [compress_first hn,compress_second hn]
  rw [ite_eq_right h1]
  by_cases h2 : j = n-2
  · subst j
    rw [ite_eq_left rfl, compress_penultimate hn]
    have he : (n-2-1) % 2 = 0 := by omega
    rw [compress_internal_even (⟨n-2-1,by omega⟩ : Fin n) (by simp; omega)
      (by simp; omega) he]
  rw [ite_eq_right h2]
  by_cases he : j % 2 = 0
  · have hp : (j-1) % 2 = 1 := by omega
    rw [compress_internal_odd (⟨j-1,by omega⟩ : Fin n) (by simp; omega)
      (by simp; omega) hp,
      compress_internal_even (⟨j,by omega⟩ : Fin n) hj (by simp; omega) he]
  · have hp : (j-1) % 2 = 0 := by omega
    have ho' : j % 2 = 1 := by omega
    rw [compress_internal_even (⟨j-1,by omega⟩ : Fin n) (by simp; omega)
      (by simp; omega) hp,
      compress_internal_odd (⟨j,by omega⟩ : Fin n) hj (by simp; omega) ho', add_comm]

theorem Q_adjacent {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n-1) : Q (compress (adjacentMask n j)) = 1 := by
  rw [compress_adjacent hn ho j hj hjn]
  split_ifs <;> decide

theorem Q_internalY {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n-1) : Q (compress (internalYMask n j)) = 1 := by
  rw [internalYMask,compress_add,compress_adjacent hn ho j hj hjn,compress_last hn]
  split_ifs <;> decide


theorem firstX {n : ℕ} (hn : 5 ≤ n) : ClassI (unitBit n 0) 0 1 := by
  have hw := weight_unit (n:=n) 0 (by omega)
  have hd : dot (unitBit n 0 + 0) (unitBit n 0) = 1 := by
    rw [add_zero,dot_unit _ 0 (by omega)]
    simp [unitBit]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_, ?_⟩
  · simp [character,dot]
  · simp [hw]
  · rw [compress_first hn]; decide

theorem internalX {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n-1) : ClassII (adjacentMask n j) 0 1 := by
  have hp : j-1 < n := by omega
  have hlt : j < n := by omega
  have hne : j-1 ≠ j := by omega
  have hne' : j ≠ j-1 := by omega
  have hw : weight (adjacentMask n j) = 2 := weight_pair (j-1) j hp hlt hne
  have ha : adjacentMask n j ≠ 0 := nonzero_of_weight (by omega)
  refine ⟨ha, by simpa using ha, ?_, ?_, ?_, Q_adjacent hn ho j hj hjn⟩
  · simp only [add_zero,adjacentMask,dot_add,dot_unit _ _ hp,dot_unit _ _ hlt]
    simp [unitBit,hne,hne',CharTwo.add_self_eq_zero]
  · simp [character,dot]
  · norm_num [hw]

theorem lastX {n : ℕ} (hn : 5 ≤ n) :
    ClassI (unitBit n (n-2)) (unitBit n (n-1)) 1 := by
  have h2 : n-2 < n := by omega
  have hne : n-2 ≠ n-1 := by omega
  have hw := weight_unit (n:=n) (n-2) h2
  have hd : dot (unitBit n (n-2) + unitBit n (n-1)) (unitBit n (n-2)) = 1 := by
    rw [dot_unit _ _ h2]
    simp [unitBit,hne]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_, ?_⟩
  · simp only [character,dot_unit _ _ h2]
    simp [unitBit,hne]
  · simp [hw]
  · rw [compress_penultimate hn]; decide

theorem firstY {n : ℕ} (hn : 5 ≤ n) :
    ClassI (unitBit n 0 + unitBit n (n-1)) (cutTail n 0) I := by
  have h0 : 0 < n := by omega
  have hl : n-1 < n := by omega
  have hne : 0 ≠ n-1 := by omega
  have hw := weight_pair (n:=n) 0 (n-1) h0 hl hne
  have hd : dot ((unitBit n 0 + unitBit n (n-1)) + cutTail n 0)
      (unitBit n 0 + unitBit n (n-1)) = 1 := by
    rw [h_firstY (by omega),dot_add,dot_unit _ _ h0,dot_unit _ _ hl]
    simp [tailMask,show 1 ≤ n-1 by omega]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_, ?_⟩
  · simp only [character,dot_add,dot_unit _ _ h0,dot_unit _ _ hl]
    simp [cutTail,show 0 < n-1 by omega]
  · norm_num [hw]
  · rw [compress_add,compress_first hn,compress_last hn]; decide

theorem internalY {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n-1) :
    ClassII (internalYMask n j) (cutTail n j) I := by
  have hp : j-1 < n := by omega
  have hlt : j < n := by omega
  have hl : n-1 < n := by omega
  have hpj : j-1 ≠ j := by omega
  have hjp : j ≠ j-1 := by omega
  have hpl : j-1 ≠ n-1 := by omega
  have hjl : j ≠ n-1 := by omega
  have hlp : n-1 ≠ j-1 := by omega
  have hw : weight (internalYMask n j) = 3 :=
    weight_triple (j-1) j (n-1) hp hlt hl hpj hpl hjl
  have ha : internalYMask n j ≠ 0 := nonzero_of_weight (by omega)
  have hh : internalYMask n j + cutTail n j ≠ 0 := by
    rw [h_internalY j hj hjn]
    intro hz
    have hz' := congrFun hz (⟨n-1,hl⟩ : Fin n)
    simp [internalYCharacter,unitBit,tailMask,hlp,show j+1 ≤ n-1 by omega] at hz'
  refine ⟨ha,hh,?_,?_,?_,Q_internalY hn ho j hj hjn⟩
  · rw [h_internalY j hj hjn]
    simp only [internalYMask,adjacentMask,dot_add,dot_unit _ _ hp,dot_unit _ _ hlt,
      dot_unit _ _ hl]
    simp [internalYCharacter,unitBit,tailMask,hjp,hlp,
      show ¬j+1 ≤ j-1 by omega,show ¬j+1 ≤ j by omega,
      show j+1 ≤ n-1 by omega,CharTwo.add_self_eq_zero]
  · simp only [character,internalYMask,adjacentMask,dot_add,
      dot_unit _ _ hp,dot_unit _ _ hlt,dot_unit _ _ hl]
    simp [cutTail,show ¬j ≤ j-1 by omega,hjn]
  · norm_num [hw,pow_succ]

theorem lastY {n : ℕ} (hn : 5 ≤ n) :
    ClassI (unitBit n (n-1) + unitBit n (n-2)) (unitBit n (n-1)) I := by
  have hl : n-1 < n := by omega
  have hp : n-2 < n := by omega
  have hlp : n-1 ≠ n-2 := by omega
  have hpl : n-2 ≠ n-1 := by omega
  have hw := weight_pair (n:=n) (n-1) (n-2) hl hp hlp
  have hd : dot ((unitBit n (n-1) + unitBit n (n-2)) + unitBit n (n-1))
      (unitBit n (n-1) + unitBit n (n-2)) = 1 := by
    rw [h_lastY,dot_add,dot_unit _ _ hl,dot_unit _ _ hp]
    simp [unitBit,hlp]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_, ?_⟩
  · simp only [character,dot_add,dot_unit _ _ hl,dot_unit _ _ hp]
    simp [unitBit,hpl]
  · norm_num [hw]
  · rw [compress_add,compress_last hn,compress_penultimate hn]; decide

theorem localZ {n : ℕ} (hn : 5 ≤ n) (j : ℕ) (hj : j < n) :
    ClassI (unitBit n (n-1)) (cutTail n j) 1 := by
  have hl : n-1 < n := by omega
  have hw := weight_unit (n:=n) (n-1) hl
  have hd : dot (unitBit n (n-1) + cutTail n j) (unitBit n (n-1)) = 1 := by
    rw [h_localZ j hj,dot_unit _ _ hl]
    simp [tailMask,show j ≤ n-1 by omega]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_, ?_⟩
  · simp only [character,dot_unit _ _ hl]
    simp [cutTail]
  · simp [hw]
  · rw [compress_last hn]; decide

end OddEJM.MaskFacts




