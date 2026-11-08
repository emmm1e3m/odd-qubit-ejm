import UnifiedEJM.PrefixLongBridge

open OddEJM Complex
open UnifiedEJM.PhysicsFinite UnifiedEJM.BoundaryAmplitude UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

noncomputable section

abbrev smallN (L : ℕ) : ℕ := 2+((L+2)+1)
abbrev smallK (L : ℕ) (suffix : Bool) : ℕ := if suffix then 2+(L+1) else 2

/-- 两位侧的五个保留物理位置。后缀割把跨边第三位放在自由组之后。 -/
def smallPack {α : Type*} {L : ℕ} (suffix : Bool) (first second third : α)
    (a : Fin L → α) (penult last : α) : Fin (smallN L) → α :=
  if suffix then Fin.append (m := 2) (n := L+3) ![first,second]
    (Fin.append (m := L) (n := 3) a ![third,penult,last])
  else Fin.append ![first,second] (Fin.cons third (Fin.append a ![penult,last]))

@[simp] theorem smallPack_first {L : ℕ} (suffix : Bool) (f s t : Bit)
    (a : Bits L) (p l : Bit) : coord (smallPack suffix f s t a p l) 0 = f := by
  cases suffix <;> simp only [smallPack, Bool.false_eq_true, ite_false, ite_true,
    coord_append] <;> simp [coord]

theorem smallPack_boundary {L : ℕ} (suffix : Bool) (f s t : Bit)
    (a : Bits L) (p l : Bit) : boundary (smallPack suffix f s t a p l) = ![f,s,p,l] := by
  have h2 : smallN L - 2 = 2+(L+1) := by dsimp [smallN] <;> omega
  have h1 : smallN L - 1 = 2+(L+2) := by dsimp [smallN] <;> omega
  ext i
  cases suffix <;> fin_cases i <;>
    simp [boundary, smallPack, coord_append, coord_cons, h2, h1,
      show ¬ 2+(L+1) < 2 by omega, show ¬ 2+(L+2) < 2 by omega,
      show ¬ L+1 < L by omega, show ¬ L+2 < L by omega] <;>
        simp [coord]

theorem smallPack_parity {L : ℕ} (suffix : Bool) (f s t : Bit)
    (a : Bits L) (p l : Bit) :
    middleParity (smallPack suffix f s t a p l) = t + parityHom L a := by
  rw [middleParity_of_total (by dsimp [smallN]; omega)]
  have hb := smallPack_boundary suffix f s t a p l
  have h0 := congrFun hb 0
  have h1 := congrFun hb 1
  have h2 := congrFun hb 2
  have h3 := congrFun hb 3
  change coord (smallPack suffix f s t a p l) 0 = f at h0
  change coord (smallPack suffix f s t a p l) 1 = s at h1
  change coord (smallPack suffix f s t a p l) (smallN L-2) = p at h2
  change coord (smallPack suffix f s t a p l) (smallN L-1) = l at h3
  rw [h0, h1, h2, h3]
  cases suffix
  · simp only [smallPack, Bool.false_eq_true, ite_false, parity_append, parity_cons]
    change ((∑ j : Fin 2, (![f,s] : Bits 2) j) +
      (t + ((∑ j, a j) + (∑ j : Fin 2, (![p,l] : Bits 2) j)))) + f + s + p + l =
        t + (∑ j, a j)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      _ = t + (∑ j, a j) + (f+f) + (s+s) + (p+p) + (l+l) := by ac_rfl
      _ = _ := by simp [CharTwo.add_self_eq_zero]
  · simp only [smallPack, ite_true, parity_append]
    rw [parity_append (m := L) (n := 3) a ![t,p,l]]
    change ((∑ j : Fin 2, (![f,s] : Bits 2) j) +
      ((∑ j, a j) + (∑ j : Fin 3, (![t,p,l] : Bits 3) j))) + f + s + p + l =
        t + (∑ j, a j)
    simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one]
    calc
      _ = t + (∑ j, a j) + (f+f) + (s+s) + (p+p) + (l+l) := by ac_rfl
      _ = _ := by simp [CharTwo.add_self_eq_zero]

theorem smallPack_constant {L : ℕ} (suffix : Bool) (f s t : Bit)
    (a : Bits L) (p l : Bit) :
    (∀ j, smallPack suffix f s t a p l j = coord (smallPack suffix f s t a p l) 0) ↔
      s = f ∧ t = f ∧ p = f ∧ l = f ∧ (∀ j, a j = f) := by
  rw [smallPack_first]
  cases suffix
  · change (∀ j, Fin.append ![f,s] (Fin.cons t (Fin.append a ![p,l])) j = f) ↔ _
    rw [constant_append ![f,s] (Fin.cons t (Fin.append a ![p,l])) f,
      constant_cons t f (Fin.append a ![p,l]), constant_append a ![p,l] f]
    simp only [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.forall_fin_zero]
    tauto
  · change (∀ j, Fin.append ![f,s] (Fin.append (m := L) (n := 3) a ![t,p,l]) j = f) ↔ _
    rw [constant_append ![f,s] (Fin.append (m := L) (n := 3) a ![t,p,l]) f,
      constant_append a ![t,p,l] f]
    simp only [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.forall_fin_zero]
    tauto

@[simp] theorem smallPack_cut_left {L : ℕ} (suffix : Bool) (f s t : Bit)
    (a : Bits L) (p l : Bit) :
    coord (smallPack suffix f s t a p l) (smallK L suffix-1) = if suffix then t else s := by
  have hk : 2+(L+1)-1 = 2+L := by omega
  cases suffix <;>
    simp [smallPack, smallK, coord_append, coord_cons, hk,
      show ¬ 2+L < 2 by omega] <;> simp [coord]

@[simp] theorem smallPack_cut_right {L : ℕ} (suffix : Bool) (f s t : Bit)
    (a : Bits L) (p l : Bit) :
    coord (smallPack suffix f s t a p l) (smallK L suffix) = if suffix then p else t := by
  cases suffix <;>
    simp [smallPack, smallK, coord_append, coord_cons,
      show ¬ 2+(L+1) < 2 by omega, show ¬ L+1 < L by omega] <;> simp [coord]

theorem splice_smallPack {L : ℕ} (suffix : Bool) (f s t f' s' t' : Bit)
    (a a' : Bits L) (p l p' l' : Bit) :
    splice (prefixSet (smallN L) (smallK L suffix))
      (smallPack suffix f s t a p l) (smallPack suffix f' s' t' a' p' l') =
      smallPack suffix f s (if suffix then t else t')
        (if suffix then a else a') p' l' := by
  cases suffix
  · exact splice_append _ _ _ _
  · ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · fin_cases i <;> simp [smallPack, splice, prefixSet, smallK,
        show 1 < 2+(L+1) by omega]
    · refine Fin.addCases (m := L) (n := 3) (fun i => ?_) (fun i => ?_) i
      · simp (disch := omega) [smallPack, splice, prefixSet, smallK]
      · fin_cases i <;> simp (disch := omega) [smallPack, splice, prefixSet, smallK]

theorem evaluatedBoundary_smallPack {L : ℕ} (hL : 1 ≤ L) (suffix : Bool) (u : ℂ)
    (f s t : Bit) (a : Bits L) (p l : Bit) :
    evaluatedBoundary u (smallPack suffix f s t a p l) =
      boundaryValue (lengthParity (smallN L)) ![f,s,p,l]
        (t + catParity (L : Bit) (wordClass a))
        (decide (s = f ∧ t = f ∧ p = f ∧ l = f) && catMatches (wordClass a) f) u := by
  have hc : (∀ j, smallPack suffix f s t a p l j = f) ↔
      s = f ∧ t = f ∧ p = f ∧ l = f ∧ (∀ j, a j = f) := by
    simpa only [smallPack_first] using smallPack_constant suffix f s t a p l
  simp only [evaluatedBoundary, smallPack_boundary, smallPack_parity,
    catParity_wordClass, catMatches_wordClass hL, smallPack_first]
  simp [hc, Bool.and_assoc]

theorem smallN_parity (L : ℕ) : (L : Bit) = 1+lengthParity (smallN L) := by
  simp only [lengthParity_cast, smallN, Nat.cast_add, Nat.cast_ofNat]
  ring_nf <;> simp [show (6 : Bit) = 0 by decide]

theorem pairWords_smallPack {L : ℕ} (suffix : Bool) (f s t : Fin 4)
    (a : Fin L → Fin 4) (p l : Fin 4) :
    pairWordsEquiv (smallN L) (smallPack suffix f s t a p l) =
      (smallPack suffix (pair f).1 (pair s).1 (pair t).1 ((pairWordsEquiv L a).1) (pair p).1 (pair l).1,
       smallPack suffix (pair f).2 (pair s).2 (pair t).2 ((pairWordsEquiv L a).2) (pair p).2 (pair l).2) := by
  apply Prod.ext <;> funext j
  all_goals
    cases suffix
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · fin_cases i <;> simp [pairWordsEquiv, smallPack]
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [pairWordsEquiv, smallPack]
        · refine Fin.addCases (m := L) (n := 2) (fun i => ?_) (fun i => ?_) i
          · simp [pairWordsEquiv, smallPack]
          · fin_cases i <;> simp [pairWordsEquiv, smallPack]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · fin_cases i <;> simp [pairWordsEquiv, smallPack]
      · refine Fin.addCases (m := L) (n := 3) (fun i => ?_) (fun i => ?_) i
        · simp [pairWordsEquiv, smallPack]
        · fin_cases i <;> simp [pairWordsEquiv, smallPack]

theorem sum_vec3 {R α : Type*} [AddCommMonoid R] [Fintype α]
    (f : (Fin 3 → α) → R) :
    (∑ x, f x) = ∑ a : α, ∑ b : α, ∑ c : α, f ![a,b,c] := by
  rw [sum_cons_generic 2]
  simp_rw [sum_vec2]
  rfl

theorem sum_smallPack_free_last {R α : Type*} [AddCommMonoid R] [Fintype α]
    (L : ℕ) (suffix : Bool) (h : (Fin (smallN L) → α) → R) :
    (∑ z, h z) = ∑ f : α, ∑ s : α, ∑ t : α, ∑ p : α, ∑ l : α,
      ∑ a : Fin L → α, h (smallPack suffix f s t a p l) := by
  cases suffix
  · change (∑ z : Fin (2+((L+2)+1)) → α, h z) = _
    rw [sum_append_generic]
    simp_rw [sum_vec2, sum_cons_generic (L+2), sum_append_generic L 2, sum_vec2]
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    rfl
  · change (∑ z : Fin (2+(L+3)) → α, h z) = _
    rw [sum_append_generic]
    simp_rw [sum_vec2, sum_append_generic L 3, sum_vec3]
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    rfl

end

end UnifiedEJM.PrefixCounts
