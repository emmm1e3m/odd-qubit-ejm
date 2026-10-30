import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic

namespace OddEJM.Geometry

/-- 任意满射二位加法标号的全部纤维等大。 -/
lemma twoBit_fiber_card (n : ℕ) (hn : 2 ≤ n)
    (f : (Fin n → ZMod 2) →+ (ZMod 2 × ZMod 2)) (hf : Function.Surjective f)
    (v : ZMod 2 × ZMod 2) :
    Nat.card {x : Fin n → ZMod 2 // f x = v} = 2 ^ (n - 2) := by
  have hker := AddSubgroup.card_ker_mul_card_of_surjective hf
  have hcards : Nat.card f.ker * 4 = 2 ^ n := by
    simpa [Nat.card_prod, Nat.card_fun, Nat.card_zmod] using hker
  have hpower : 2 ^ n = 2 ^ (n - 2) * 4 := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
  have hk : Nat.card f.ker = 2 ^ (n - 2) := by omega
  have he := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf v)
  exact he.trans hk

/-- 边标号附加一个独立位，适用于每一个局部 q_j。 -/
def pairedLabel {m : ℕ} (f : (Fin m → ZMod 2) →+ ZMod 2) :
    ((Fin m → ZMod 2) × ZMod 2) →+ (ZMod 2 × ZMod 2) where
  toFun x := (f x.1, x.2)
  map_zero' := by simp
  map_add' x y := by simp

lemma pairedLabel_surjective {m : ℕ} (f : (Fin m → ZMod 2) →+ ZMod 2)
    (hf : Function.Surjective f) : Function.Surjective (pairedLabel f) := by
  rintro ⟨q, s⟩
  obtain ⟨e, he⟩ := hf q
  exact ⟨(e, s), Prod.ext he rfl⟩

lemma pairedLabel_fiber_card (m : ℕ) (hm : 1 ≤ m)
    (f : (Fin m → ZMod 2) →+ ZMod 2) (hf : Function.Surjective f)
    (v : ZMod 2 × ZMod 2) :
    Nat.card {x : (Fin m → ZMod 2) × ZMod 2 // pairedLabel f x = v} = 2 ^ (m - 1) := by
  have hsurj := pairedLabel_surjective f hf
  have hker := AddSubgroup.card_ker_mul_card_of_surjective hsurj
  have hcards : Nat.card (pairedLabel f).ker * 4 = 2 ^ m * 2 := by
    simpa [Nat.card_prod, Nat.card_fun, Nat.card_zmod] using hker
  have hpower : 2 ^ m * 2 = 2 ^ (m - 1) * 4 := by
    nth_rw 1 [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hk : Nat.card (pairedLabel f).ker = 2 ^ (m - 1) := by omega
  exact (Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hsurj v)).trans hk

/-- 第 j 个物理位旁的边位之和：边 k 邻接物理位 k 和 k+1。 -/
def edgeParityHom (m : ℕ) (j : Fin (m + 1)) :
    (Fin m → ZMod 2) →+ ZMod 2 where
  toFun e := ∑ k : Fin m, if k.val = j.val ∨ k.val + 1 = j.val then e k else 0
  map_zero' := by simp
  map_add' e f := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp

lemma adjacent_edge_exists (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 1)) :
    ∃ k : Fin m, k.val = j.val ∨ k.val + 1 = j.val := by
  by_cases h : j.val < m
  · exact ⟨⟨j.val, h⟩, Or.inl rfl⟩
  · have hj : j.val = m := by omega
    refine ⟨⟨m - 1, by omega⟩, Or.inr ?_⟩
    simp only
    omega

lemma edgeParityHom_surjective (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 1)) :
    Function.Surjective (edgeParityHom m j) := by
  intro q
  obtain ⟨p, hp⟩ := adjacent_edge_exists m hm j
  refine ⟨Pi.single p q, ?_⟩
  change (∑ k : Fin m, if k.val = j.val ∨ k.val + 1 = j.val
    then (Pi.single p q) k else 0) = q
  rw [Finset.sum_eq_single p]
  · simp [hp]
  · intro b hb hbp
    simp [Pi.single_eq_of_ne hbp]
  · simp

/-- n=m+1 个物理位时，每个局部标号 (q,s) 恰出现 2^(n−2) 次。 -/
lemma localLabel_fiber_card (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 1))
    (v : ZMod 2 × ZMod 2) :
    Nat.card {x : (Fin m → ZMod 2) × ZMod 2 //
      pairedLabel (edgeParityHom m j) x = v} = 2 ^ (m - 1) :=
  pairedLabel_fiber_card m hm _ (edgeParityHom_surjective m hm j) v
/-- 与 Core 的 Bits (m+1) 完全相同的输入类型；末位为独立 s。 -/
def fullLabelHom (m : ℕ) (j : Fin (m + 1)) :
    (Fin (m + 1) → ZMod 2) →+ (ZMod 2 × ZMod 2) where
  toFun x := (edgeParityHom m j (fun k => x k.castSucc), x (Fin.last m))
  map_zero' := by
    apply Prod.ext
    · exact map_zero (edgeParityHom m j)
    · rfl
  map_add' x y := by
    apply Prod.ext
    · exact map_add (edgeParityHom m j) _ _
    · rfl

lemma fullLabelHom_surjective (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 1)) :
    Function.Surjective (fullLabelHom m j) := by
  rintro ⟨q, s⟩
  obtain ⟨e, he⟩ := edgeParityHom_surjective m hm j q
  refine ⟨Fin.snoc e s, ?_⟩
  change (edgeParityHom m j (fun k => (@Fin.snoc m (fun _ => ZMod 2) e s) k.castSucc),
    (@Fin.snoc m (fun _ => ZMod 2) e s) (Fin.last m)) = (q, s)
  simpa only [Fin.snoc_castSucc, Fin.snoc_last] using Prod.ext he (rfl : s = s)

lemma fullLabel_fiber_card (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 1))
    (v : ZMod 2 × ZMod 2) :
    Nat.card {x : Fin (m + 1) → ZMod 2 // fullLabelHom m j x = v} = 2 ^ (m - 1) := by
  simpa only [show m + 1 - 2 = m - 1 by omega] using
    twoBit_fiber_card (m + 1) (by omega) _ (fullLabelHom_surjective m hm j) v
end OddEJM.Geometry





