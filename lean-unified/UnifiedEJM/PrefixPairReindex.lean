import UnifiedEJM.PrefixPacking

open OddEJM
open UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

noncomputable section

/-- 位对编码是有限双射，仅有十六个候选检查。 -/
def pairEquiv : Fin 4 ≃ Bit × Bit :=
  Equiv.ofBijective PrefixKernel.pair (by decide +kernel)

def pairWordsEquiv (L : ℕ) : (Fin L → Fin 4) ≃ Bits L × Bits L where
  toFun z := (fun j => (PrefixKernel.pair (z j)).1,
    fun j => (PrefixKernel.pair (z j)).2)
  invFun z j := pairEquiv.symm (z.1 j, z.2 j)
  left_inv z := by
    funext j
    exact pairEquiv.symm_apply_apply (z j)
  right_inv z := by
    apply Prod.ext <;> funext j
    · exact congrArg Prod.fst (pairEquiv.apply_symm_apply (z.1 j, z.2 j))
    · exact congrArg Prod.snd (pairEquiv.apply_symm_apply (z.1 j, z.2 j))

/-- 两份完整位串重索引为逐位置位对，避免引入代表长度。 -/
theorem sum_pairWords {R : Type*} [AddCommMonoid R] (L : ℕ)
    (f : Bits L → Bits L → R) :
    (∑ y : Bits L, ∑ v : Bits L, f y v) =
      ∑ z : Fin L → Fin 4, f ((pairWordsEquiv L z).1) ((pairWordsEquiv L z).2) := by
  calc
    _ = ∑ p : Bits L × Bits L, f p.1 p.2 :=
      (Fintype.sum_prod_type (fun p : Bits L × Bits L => f p.1 p.2)).symm
    _ = _ := ((pairWordsEquiv L).sum_comp (fun z => f z.1 z.2)).symm

/-- 任意正长度的位对自由组，精确变成两个类别重数的乘积。 -/
theorem sum_pairWord_classes {R : Type*} [CommRing R] {L : ℕ} (hL : 1 ≤ L)
    (f : Fin 4 → Fin 4 → R) :
    (∑ z : Fin L → Fin 4,
      f (wordClass ((pairWordsEquiv L z).1)) (wordClass ((pairWordsEquiv L z).2))) =
      ∑ c : Fin 4, ∑ d : Fin 4,
        classWeight (L : Bit) (2^(L-1) : R) c *
          classWeight (L : Bit) (2^(L-1) : R) d * f c d := by
  rw [← sum_pairWords L (fun y v => f (wordClass y) (wordClass v))]
  have hin (c : Fin 4) :
      (∑ v : Bits L, f c (wordClass v)) =
        ∑ d : Fin 4, classWeight (L : Bit) (2^(L-1) : R) d * f c d :=
    sum_wordClass hL (fun d => f c d)
  simp_rw [hin]
  rw [sum_wordClass hL (fun c =>
    ∑ d : Fin 4, classWeight (L : Bit) (2^(L-1) : R) d * f c d)]
  simp only [Finset.mul_sum, mul_assoc]

theorem sum_pairWord_runs {R : Type*} [CommRing R] (L : ℕ)
    (f : Fin 4 → Fin 4 → R) :
    (∑ z : Fin L → Fin 4,
      f (wordClass ((pairWordsEquiv L z).1)) (wordClass ((pairWordsEquiv L z).2))) =
      ∑ c : Fin 4, ∑ d : Fin 4,
        (PrefixKernel.runWeight (2^(L-1)) (runInfo L) c : R) *
          (PrefixKernel.runWeight (2^(L-1)) (runInfo L) d : R) * f c d := by
  rw [← sum_pairWords L (fun y v => f (wordClass y) (wordClass v))]
  have hin (c : Fin 4) :
      (∑ v : Bits L, f c (wordClass v)) =
        ∑ d : Fin 4, (PrefixKernel.runWeight (2^(L-1)) (runInfo L) d : R) * f c d :=
    sum_runClass_ring (fun d => f c d)
  simp_rw [hin]
  rw [sum_runClass_ring (fun c =>
    ∑ d : Fin 4, (PrefixKernel.runWeight (2^(L-1)) (runInfo L) d : R) * f c d)]
  simp only [Finset.mul_sum, mul_assoc]

theorem sum_pairWord_cats {R : Type*} [CommRing R] {L : ℕ} (hL : 1 ≤ L)
    (f : Fin 4 → Fin 4 → R) :
    (∑ z : Fin L → Fin 4,
      f (wordClass ((pairWordsEquiv L z).1)) (wordClass ((pairWordsEquiv L z).2))) =
      ∑ c : Fin 4, ∑ d : Fin 4,
        (PrefixKernel.catWeight (2^(L-1)) (L : Bit) c : R) *
          (PrefixKernel.catWeight (2^(L-1)) (L : Bit) d : R) * f c d := by
  simpa [runInfo, show L ≠ 0 by omega, PrefixKernel.runWeight,
    PrefixKernel.runCoeff, PrefixKernel.catWeight] using sum_pairWord_runs L f

def pack {α : Type*} {LA LB : ℕ} (first second : α) (a : Fin LA → α)
    (left right : α) (b : Fin LB → α) (penult last : α) : Fin (longN LA LB) → α :=
  Fin.append (Fin.append ![first,second] (Fin.snoc a left))
    (Fin.cons right (Fin.append b ![penult,last]))

theorem pairWords_pack {LA LB : ℕ} (first second : Fin 4) (a : Fin LA → Fin 4)
    (left right : Fin 4) (b : Fin LB → Fin 4) (penult last : Fin 4) :
    pairWordsEquiv (longN LA LB) (pack first second a left right b penult last) =
      (fullWord ![(PrefixKernel.pair first).1,(PrefixKernel.pair second).1]
        ((pairWordsEquiv LA a).1) (PrefixKernel.pair left).1 (PrefixKernel.pair right).1
        ((pairWordsEquiv LB b).1) ![(PrefixKernel.pair penult).1,(PrefixKernel.pair last).1],
       fullWord ![(PrefixKernel.pair first).2,(PrefixKernel.pair second).2]
        ((pairWordsEquiv LA a).2) (PrefixKernel.pair left).2 (PrefixKernel.pair right).2
        ((pairWordsEquiv LB b).2) ![(PrefixKernel.pair penult).2,(PrefixKernel.pair last).2]) := by
  apply Prod.ext <;> funext j
  all_goals
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun h => ?_) (fun h => ?_) i
      · fin_cases h <;> simp [pairWordsEquiv, pack, fullWord]
      · refine Fin.lastCases ?_ (fun h' => ?_) h <;>
          simp [pairWordsEquiv, pack, fullWord, -Fin.natAdd_last]
    · refine Fin.cases ?_ (fun h => ?_) i
      · simp [pairWordsEquiv, pack, fullWord]
      · refine Fin.addCases (fun h' => ?_) (fun h' => ?_) h
        · simp [pairWordsEquiv, pack, fullWord]
        · fin_cases h' <;> simp [pairWordsEquiv, pack, fullWord]

theorem sum_cons_generic {R α : Type*} [AddCommMonoid R] [Fintype α]
    (L : ℕ) (f : (Fin (L+1) → α) → R) :
    (∑ z, f z) = ∑ b : α, ∑ x : Fin L → α, f (Fin.cons b x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (L+1) => α)).sum_comp f]
  exact Fintype.sum_prod_type _

theorem sum_snoc_generic {R α : Type*} [AddCommMonoid R] [Fintype α]
    (L : ℕ) (f : (Fin (L+1) → α) → R) :
    (∑ z, f z) = ∑ x : Fin L → α, ∑ b : α, f (Fin.snoc x b) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (L+1) => α)).sum_comp f]
  change (∑ p : α × (Fin L → α), f (Fin.snoc p.2 p.1)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sum_append_generic {R α : Type*} [AddCommMonoid R] [Fintype α]
    (m n : ℕ) (f : (Fin (m+n) → α) → R) :
    (∑ z, f z) = ∑ x : Fin m → α, ∑ y : Fin n → α, f (Fin.append x y) := by
  rw [← (Fin.appendEquiv (α := α) m n).sum_comp f]
  exact Fintype.sum_prod_type _

theorem sum_vec2 {R α : Type*} [AddCommMonoid R] [Fintype α]
    (f : (Fin 2 → α) → R) :
    (∑ x, f x) = ∑ a : α, ∑ b : α, f ![a,b] := by
  rw [sum_cons_generic 1]
  simp_rw [sum_cons_generic 0]
  simp
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1

theorem sum_pack {R α : Type*} [AddCommMonoid R] [Fintype α] (LA LB : ℕ)
    (h : (Fin (longN LA LB) → α) → R) :
    (∑ y, h y) =
      ∑ f : α, ∑ s : α, ∑ a : Fin LA → α, ∑ left : α, ∑ right : α,
        ∑ b : Fin LB → α, ∑ p : α, ∑ l : α, h (pack f s a left right b p l) := by
  change (∑ y : Fin ((2+(LA+1))+((LB+2)+1)) → α, h y) = _
  rw [sum_append_generic]
  simp_rw [sum_append_generic 2 (LA+1), sum_snoc_generic LA,
    sum_cons_generic (LB+2), sum_append_generic LB 2, sum_vec2]
  rfl

/-- 两个连续自由组移到求和最内层，便于直接应用任意长度计数。 -/
theorem sum_pack_free_last {R α : Type*} [AddCommMonoid R] [Fintype α] (LA LB : ℕ)
    (h : (Fin (longN LA LB) → α) → R) :
    (∑ y, h y) =
      ∑ f : α, ∑ s : α, ∑ left : α, ∑ right : α, ∑ p : α, ∑ l : α,
        ∑ a : Fin LA → α, ∑ b : Fin LB → α, h (pack f s a left right b p l) := by
  rw [sum_pack]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  calc
    _ = ∑ a : Fin LA → α, ∑ p : α, ∑ l : α, ∑ b : Fin LB → α,
        h (pack f s a left right b p l) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]

end

end UnifiedEJM.PrefixCounts
