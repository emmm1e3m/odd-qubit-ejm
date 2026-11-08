import UnifiedEJM.CosineEndpoint

noncomputable section
open scoped BigOperators
open Complex OddEJM OddEJM.CircuitPauli
open UnifiedEJM.EvenWalsh

namespace UnifiedEJM.CosineEndpoint

/-- 除第二物理位外，其余AND坐标。 -/
def restSet (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => InE n j.val ∧ j.val ≠ 1)

def restZero {n : ℕ} (z : Bits n) : Prop := ∀ j ∈ restSet n, z j = 0

instance {n : ℕ} (z : Bits n) : Decidable (restZero z) :=
  inferInstanceAs (Decidable (∀ j ∈ restSet n, z j = 0))

theorem restZero_add_one {n : ℕ} (z : Bits n) :
    restZero (z + unitBit n 1) ↔ restZero z := by
  unfold restZero
  have hz (j : Fin n) (hj : j ∈ restSet n) : unitBit n 1 j = 0 := by
    have h := (Finset.mem_filter.mp hj).2.2
    simp [unitBit, h]
  simp only [Pi.add_apply]
  constructor <;> intro h j hj <;> simpa only [hz j hj, add_zero] using h j hj

theorem qA_from_rest {n : ℕ} (hn : 4 ≤ n) (z : Bits n) :
    qA z = if restZero z then 1 - coord z 1 else 0 := by
  have h1 : 1 < n := by omega
  have he : EZero z ↔ restZero z ∧ coord z 1 = 0 := by
    constructor
    · intro hz
      refine ⟨fun j hj => hz j (Finset.mem_filter.mp hj).2.1, ?_⟩
      simpa [coord, h1] using hz ⟨1,h1⟩ (by simp [InE]; omega)
    · rintro ⟨hr,hz⟩ j hj
      by_cases hj1 : j.val = 1
      · have hj' : j = ⟨1,h1⟩ := Fin.ext hj1
        subst j
        simpa [coord, h1] using hz
      · exact hr j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hj1⟩)
  unfold qA
  simp only [he]
  by_cases hr : restZero z <;>
    rcases OddEJM.bit_cases (coord z 1) with h | h <;> simp [hr,h]

theorem indicator_sum (n : ℕ) (S : Finset (Fin n)) :
    (∑ z : Bits n, if ∀ j ∈ S, z j = 0 then (1:ℂ) else 0) =
      (2:ℂ)^(n-S.card) := by
  classical
  have hprod (z : Bits n) :
      (if ∀ j ∈ S, z j = 0 then (1:ℂ) else 0) =
        ∏ j : Fin n, if j ∈ S → z j = 0 then (1:ℂ) else 0 := by
    rw [Fintype.prod_boole]
    split_ifs <;> simp_all
  rw [show (∑ z : Bits n, if ∀ j ∈ S, z j = 0 then (1:ℂ) else 0) =
      ∑ z : Bits n, ∏ j : Fin n, if j ∈ S → z j = 0 then (1:ℂ) else 0 by
        simp_rw [hprod]]
  rw [← Fintype.prod_sum (fun (j : Fin n) (b : Bit) =>
    if j ∈ S → b=0 then (1:ℂ) else 0)]
  have hsum (j : Fin n) :
      (∑ b : Bit, if j ∈ S → b = 0 then (1:ℂ) else 0) = if j ∈ S then 1 else 2 := by
    by_cases hj : j ∈ S <;> simp [hj, sum_bit]
  simp_rw [hsum]
  rw [Finset.prod_ite]
  have hcomp : Finset.univ.filter (fun j : Fin n => j ∉ S) = Sᶜ := by
    ext j
    simp
  rw [hcomp]
  simp [Finset.card_compl]

/-- 用显式双射计数条件坐标，不枚举n。 -/
def restEquiv {n : ℕ} (hn : 4 ≤ n) (hev : Even n) :
    Fin (n/2-2) ≃ {j : Fin n // j ∈ restSet n} where
  toFun k := ⟨⟨2*k.val+3, by
    have hp := Nat.even_iff.mp hev
    have hk := k.isLt
    omega⟩, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (1 ≤ 2*k.val+3 ∧ 2*k.val+3 < n-2 ∧ (2*k.val+3)%2=1) ∧ 2*k.val+3≠1
      have hp := Nat.even_iff.mp hev
      have hk := k.isLt
      omega⟩
  invFun j := ⟨(j.val.val-3)/2, by
    have hj := (Finset.mem_filter.mp j.property).2
    have hp := Nat.even_iff.mp hev
    simp only [InE] at hj
    omega⟩
  left_inv k := by apply Fin.ext; simp <;> omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hj := (Finset.mem_filter.mp j.property).2
    simp only [InE] at hj
    simp only
    omega

theorem restSet_card {n : ℕ} (hn : 4 ≤ n) (hev : Even n) :
    (restSet n).card = n/2-2 := by
  have h := Fintype.card_congr (restEquiv hn hev)
  simpa using h.symm

theorem rest_count {n : ℕ} (hn : 4 ≤ n) (hev : Even n) :
    (∑ z : Bits n, if restZero z then (1:ℂ) else 0) = (2:ℂ)^(n-(n/2-2)) := by
  rw [show (∑ z : Bits n, if restZero z then (1:ℂ) else 0) =
      ∑ z : Bits n, if ∀ j ∈ restSet n, z j = 0 then (1:ℂ) else 0 from rfl,
    indicator_sum, restSet_card hn hev]

theorem flip_one_correlation {n : ℕ} (hn : 4 ≤ n) (hev : Even n) :
    (∑ z : Bits n, character (unitBit n 1) z *
      (I ^ (qA z).val * star (I ^ (qA (z+unitBit n 1)).val))) =
        I * (2:ℂ)^(n-(n/2-2)) := by
  have hp (z : Bits n) : character (unitBit n 1) z *
      (I ^ (qA z).val * star (I ^ (qA (z+unitBit n 1)).val)) =
      I * (if restZero z then 1 else 0) +
        character (unitBit n 1) z * (if restZero z then 0 else 1) := by
    rw [qA_from_rest hn z, qA_from_rest hn (z+unitBit n 1)]
    simp only [restZero_add_one, at_add, coord_unit _ _ (by omega : 1<n), ite_true,
      character, dot_unit_left]
    by_cases hr : restZero z <;>
      rcases OddEJM.bit_cases (coord z 1) with h | h <;>
      norm_num [hr,h,bitSign,ZMod.val_one_eq_one_mod]
  have hz : (∑ z : Bits n, character (unitBit n 1) z *
      (if restZero z then (0:ℂ) else 1)) = 0 := by
    apply weighted_character_zero (unitBit n 1) (unitBit n 1)
    · simp [dot_unit_left, coord_unit _ _ (by omega : 1<n)]
    · intro z; simp only [restZero_add_one]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, rest_count hn hev, hz, add_zero]

end UnifiedEJM.CosineEndpoint
