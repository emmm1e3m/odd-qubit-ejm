import UnifiedEJM.PrefixReindex
import UnifiedEJM.PrefixClassBridge

open OddEJM Complex
open UnifiedEJM.BoundaryAmplitude UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

theorem sum_cons {R : Type*} [AddCommMonoid R] (L : ℕ) (f : Bits (L+1) → R) :
    (∑ z : Bits (L+1), f z) = ∑ b : Bit, ∑ x : Bits L, f (Fin.cons b x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (L+1) => Bit)).sum_comp f]
  exact Fintype.sum_prod_type _

theorem sum_snoc {R : Type*} [AddCommMonoid R] (L : ℕ) (f : Bits (L+1) → R) :
    (∑ z : Bits (L+1), f z) = ∑ x : Bits L, ∑ b : Bit, f (Fin.snoc x b) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (L+1) => Bit)).sum_comp f]
  change (∑ p : Bit × Bits L, f (Fin.snoc p.2 p.1)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem coord_append {m n : ℕ} (x : Bits m) (y : Bits n) (j : ℕ) :
    coord (Fin.append x y) j = if j < m then coord x j else coord y (j-m) := by
  by_cases hj : j < m
  · have htotal : j < m+n := by omega
    simp only [coord, hj, htotal, dite_true, if_true]
    exact Fin.append_left x y ⟨j, hj⟩
  · by_cases htotal : j < m+n
    · have hr : j-m < n := by omega
      have he : (⟨j, htotal⟩ : Fin (m+n)) = Fin.natAdd m ⟨j-m, hr⟩ := by
        ext
        simp only [Fin.val_mk, Fin.val_natAdd]
        omega
      simp only [coord, hj, htotal, hr, dite_true, if_false, he]
      exact Fin.append_right x y ⟨j-m, hr⟩
    · have hr : ¬j-m < n := by omega
      simp [coord, hj, htotal, hr]

theorem coord_snoc {L : ℕ} (x : Bits L) (b : Bit) (j : ℕ) :
    coord (Fin.snoc x b) j = if j < L then coord x j else if j = L then b else 0 := by
  by_cases hj : j < L
  · have hsucc : j < L+1 := by omega
    simp only [coord, hj, hsucc, dite_true, if_true]
    exact Fin.snoc_castSucc (α := fun _ : Fin (L+1) => Bit) b x ⟨j, hj⟩
  · by_cases he : j = L
    · subst j
      simp only [coord, show L < L+1 by omega, dite_true,
        show ¬L < L by omega, ite_false, ite_true]
      change (Fin.snoc x b : Bits (L+1)) (Fin.last L) = b
      exact Fin.snoc_last (α := fun _ : Fin (L+1) => Bit) b x
    · have hn : ¬j < L+1 := by omega
      simp [coord, hj, he, hn]

theorem coord_cons {L : ℕ} (b : Bit) (x : Bits L) (j : ℕ) :
    coord (Fin.cons b x) j = if j = 0 then b else coord x (j-1) := by
  cases j with
  | zero => simp [coord]
  | succ j =>
    by_cases hj : j < L
    · simp only [coord, hj, show j+1 < L+1 by omega, dite_true,
        Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
      change (Fin.cons b x : Bits (L+1)) (⟨j,hj⟩ : Fin L).succ = x ⟨j,hj⟩
      rfl
    · simp [coord, hj, show ¬j+1 < L+1 by omega]

abbrev longK (LA : ℕ) : ℕ := 2+(LA+1)
abbrev longN (LA LB : ℕ) : ℕ := longK LA + ((LB+2)+1)

/-- 按真实物理顺序保留六位，其余分成两个连续同侧自由组。 -/
def fullWord {LA LB : ℕ} (f : Bits 2) (a : Bits LA) (left right : Bit)
    (b : Bits LB) (l : Bits 2) : Bits (longN LA LB) :=
  Fin.append (Fin.append f (Fin.snoc a left)) (Fin.cons right (Fin.append b l))

theorem fullWord_coord_first {LA LB : ℕ} (f : Bits 2) (a : Bits LA)
    (left right : Bit) (b : Bits LB) (l : Bits 2) :
    coord (fullWord f a left right b l) 0 = f 0 := by
  simp only [fullWord, coord_append]
  simp [longK, coord]

theorem fullWord_boundary {LA LB : ℕ} (f : Bits 2) (a : Bits LA)
    (left right : Bit) (b : Bits LB) (l : Bits 2) :
    boundary (fullWord f a left right b l) = ![f 0, f 1, l 0, l 1] := by
  have h2 : longN LA LB-2 = (2+(LA+1))+(LB+1) := by dsimp [longN, longK] <;> omega
  have h1 : longN LA LB-1 = (2+(LA+1))+(LB+2) := by dsimp [longN, longK] <;> omega
  ext i
  fin_cases i <;>
    simp [boundary, fullWord, coord_append, coord_cons, coord_snoc, h2, h1,
      show 0 < 2+(LA+1) by omega, show 1 < 2+(LA+1) by omega,
      show ¬ (2+(LA+1))+(LB+1) < 2+(LA+1) by omega,
      show ¬ (2+(LA+1))+(LB+2) < 2+(LA+1) by omega,
      show LB+1 ≠ 0 by omega, show LB+2 ≠ 0 by omega, show ¬ LB+1 < LB by omega] <;>
        simp [coord]

theorem fullWord_cut_coords {LA LB : ℕ} (f : Bits 2) (a : Bits LA)
    (left right : Bit) (b : Bits LB) (l : Bits 2) :
    coord (fullWord f a left right b l) (longK LA-1) = left ∧
    coord (fullWord f a left right b l) (longK LA) = right := by
  have hk : longK LA-1 = 2+LA := by dsimp [longK] <;> omega
  constructor <;>
    simp [fullWord, coord_append, coord_cons, coord_snoc, hk, longK,
      show 2+LA < 2+(LA+1) by omega, show ¬ 2+LA < 2 by omega] <;> simp [coord]

@[simp] theorem fullWord_cut_left {LA LB : ℕ} (f : Bits 2) (a : Bits LA)
    (left right : Bit) (b : Bits LB) (l : Bits 2) :
    coord (fullWord f a left right b l) (longK LA-1) = left :=
  (fullWord_cut_coords f a left right b l).1

@[simp] theorem fullWord_cut_right {LA LB : ℕ} (f : Bits 2) (a : Bits LA)
    (left right : Bit) (b : Bits LB) (l : Bits 2) :
    coord (fullWord f a left right b l) (longK LA) = right :=
  (fullWord_cut_coords f a left right b l).2

theorem fullWord_parity {LA LB : ℕ} (f : Bits 2) (a : Bits LA)
    (left right : Bit) (b : Bits LB) (l : Bits 2) :
    middleParity (fullWord f a left right b l) =
      parityHom LA a + left + right + parityHom LB b := by
  rw [middleParity_of_total (by dsimp [longN, longK] <;> omega)]
  have he := fullWord_boundary f a left right b l
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  have h3 := congrFun he 3
  simp [boundary] at h0 h1 h2 h3
  have hn1 : longN LA LB - 1 = longK LA + (LB + 2) := by
    dsimp [longN, longK] <;> omega
  rw [h0, h1, h2, hn1, h3]
  simp only [fullWord, parity_append, parity_cons, parity_snoc]
  change ((∑ j : Fin 2, f j) + ((∑ j, a j) + left)) +
    (right + ((∑ j, b j) + (∑ j : Fin 2, l j))) + f 0 + f 1 + l 0 + l 1 =
      (∑ j, a j) + left + right + (∑ j, b j)
  simp only [Fin.sum_univ_two]
  calc
    _ = (∑ j, a j) + left + right + (∑ j, b j) +
        (f 0 + f 0) + (f 1 + f 1) + (l 0 + l 0) + (l 1 + l 1) := by ac_rfl
    _ = _ := by simp [CharTwo.add_self_eq_zero]

theorem fullWord_constant {LA LB : ℕ} (f : Bits 2) (a : Bits LA)
    (left right : Bit) (b : Bits LB) (l : Bits 2) :
    (∀ j, fullWord f a left right b l j = coord (fullWord f a left right b l) 0) ↔
      f 1 = f 0 ∧ left = f 0 ∧ right = f 0 ∧ l 0 = f 0 ∧ l 1 = f 0 ∧
        (∀ j, a j = f 0) ∧ (∀ j, b j = f 0) := by
  rw [fullWord_coord_first]
  simp only [fullWord, constant_append, constant_cons, constant_snoc]
  simp only [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.forall_fin_zero]
  tauto

/-- 这是所有实际位串的双射重索引，既不取代表长度，也不舍弃常量串。 -/
theorem sum_fullWord {R : Type*} [AddCommMonoid R] (LA LB : ℕ)
    (h : Bits (longN LA LB) → R) :
    (∑ y : Bits (longN LA LB), h y) =
      ∑ f : Bits 2, ∑ a : Bits LA, ∑ left : Bit, ∑ right : Bit,
        ∑ b : Bits LB, ∑ l : Bits 2, h (fullWord f a left right b l) := by
  change (∑ y : Bits ((2+(LA+1))+((LB+2)+1)), h y) = _
  rw [sum_append (2+(LA+1)) ((LB+2)+1)]
  simp_rw [sum_append 2 (LA+1), sum_snoc LA, sum_cons (LB+2), sum_append LB 2]
  rfl

/-- 有限类别确实决定任意长物理串的完整边界振幅。 -/
theorem evaluatedBoundary_fullWord {LA LB : ℕ} (hA : 1 ≤ LA) (hB : 1 ≤ LB)
    (u : ℂ) (f : Bits 2) (a : Bits LA) (left right : Bit) (b : Bits LB) (l : Bits 2) :
    evaluatedBoundary u (fullWord f a left right b l) =
      boundaryValue (lengthParity (longN LA LB)) ![f 0,f 1,l 0,l 1]
        (PrefixKernel.catParity (LA : Bit) (wordClass a) + left + right +
          PrefixKernel.catParity (LB : Bit) (wordClass b))
        (decide (f 1 = f 0 ∧ left = f 0 ∧ right = f 0 ∧ l 0 = f 0 ∧ l 1 = f 0) &&
          PrefixKernel.catMatches (wordClass a) (f 0) &&
          PrefixKernel.catMatches (wordClass b) (f 0)) u := by
  simp only [evaluatedBoundary, fullWord_boundary, fullWord_parity,
    catParity_wordClass, catMatches_wordClass hA, catMatches_wordClass hB]
  simp [fullWord_constant, Bool.and_assoc, and_assoc]

/-- 包括任意一侧自由组为空的统一版本。 -/
theorem evaluatedBoundary_fullWord_run {LA LB : ℕ}
    (u : ℂ) (f : Bits 2) (a : Bits LA) (left right : Bit) (b : Bits LB) (l : Bits 2) :
    evaluatedBoundary u (fullWord f a left right b l) =
      boundaryValue (lengthParity (longN LA LB)) ![f 0,f 1,l 0,l 1]
        (PrefixKernel.runParity (runInfo LA) (wordClass a) + left + right +
          PrefixKernel.runParity (runInfo LB) (wordClass b))
        (decide (f 1 = f 0 ∧ left = f 0 ∧ right = f 0 ∧ l 0 = f 0 ∧ l 1 = f 0) &&
          PrefixKernel.runMatches (runInfo LA) (wordClass a) (f 0) &&
          PrefixKernel.runMatches (runInfo LB) (wordClass b) (f 0)) u := by
  simp only [evaluatedBoundary, fullWord_boundary, fullWord_parity,
    runParity_wordClass, runMatches_wordClass]
  simp [fullWord_constant, Bool.and_assoc, and_assoc]

theorem splice_fullWord {LA LB : ℕ} (f f' : Bits 2) (a a' : Bits LA)
    (left left' right right' : Bit) (b b' : Bits LB) (l l' : Bits 2) :
    splice (prefixSet (longN LA LB) (longK LA))
      (fullWord f a left right b l) (fullWord f' a' left' right' b' l') =
      fullWord f a left right' b' l' := by
  exact splice_append _ _ _ _

@[simp] theorem lengthParity_cast (n : ℕ) : lengthParity n = (n : Bit) := by
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rw [← ZMod.natCast_mod n 2]
  rcases h with h | h <;> simp [lengthParity, h]

@[simp] theorem lengthParity_longN (LA LB : ℕ) :
    lengthParity (longN LA LB) = (runInfo LA).getD 0 + (runInfo LB).getD 0 := by
  simp only [lengthParity_cast, runInfo_getD, longN, longK, Nat.cast_add, Nat.cast_ofNat]
  ring_nf <;> simp [show (6 : Bit) = 0 by decide]

end UnifiedEJM.PrefixCounts
