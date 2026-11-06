import OddEJM.Pauli
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic
import UnifiedEJM.CliffordGroup

noncomputable section
open scoped BigOperators Matrix
open OddEJM

namespace UnifiedEJM.CliffordFoundation

abbrev Gate (n : ℕ) := Matrix.unitaryGroup (Bits n) ℂ

/-- 按真实计算基定义的 c X^a Z^b 矩阵。 -/
def pauliMatrix {n : ℕ} (a b : Bits n) (c : ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  fun x y => if x = y + a then c * character b y else 0

theorem character_mul_self {n : ℕ} (b z : Bits n) :
    character b z * character b z = 1 := by
  unfold character
  rcases CircuitPauli.bit_cases (dot b z) with h | h <;> simp [h, bitSign]

theorem star_character {n : ℕ} (b z : Bits n) :
    star (character b z) = character b z := by
  unfold character
  rcases CircuitPauli.bit_cases (dot b z) with h | h <;> simp [h, bitSign]

theorem pauliMatrix_mul {n : ℕ} (a b a' b' : Bits n) (c c' : ℂ) :
    pauliMatrix a b c * pauliMatrix a' b' c' =
      pauliMatrix (a + a') (b + b') (c * c' * character b a') := by
  ext x y
  simp only [Matrix.mul_apply, pauliMatrix]
  rw [Finset.sum_eq_single (y+a')]
  · simp only [ite_true, CircuitPauli.char_add]
    have hc : character (b+b') y = character b y * character b' y := by
      simp [character, CircuitPauli.dot_add_left, CircuitPauli.sign_add]
    rw [hc]
    by_cases h : x = y + (a+a')
    · have h' : x = y+a'+a := by simpa only [add_assoc, add_comm a a'] using h
      rw [ite_eq_left h', ite_eq_left h]
      ring
    · have h' : x ≠ y+a'+a := by simpa only [add_assoc, add_comm a a'] using h
      simp [h, h']
  · intro z _ hz
    simp only [ite_eq_right hz, mul_zero]
  · simp

theorem pauliMatrix_one {n : ℕ} : pauliMatrix (0 : Bits n) 0 1 = 1 := by
  ext x y
  simp [pauliMatrix, character, dot, bitSign, Matrix.one_apply]

theorem pauliMatrix_star {n : ℕ} (a b : Bits n) (c : ℂ) :
    (pauliMatrix a b c)ᴴ = pauliMatrix a b (star c * character b a) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, pauliMatrix]
  have he : y = x+a ↔ x = y+a := by
    constructor <;> intro h <;> subst_vars <;> ext j <;>
      simp [add_assoc, CharTwo.add_self_eq_zero]
  by_cases h : x = y+a
  · have h' := he.mpr h
    rw [ite_eq_left h', ite_eq_left h]
    rw [star_mul, star_character]
    rw [h, CircuitPauli.char_add]
    ring
  · rw [ite_eq_right h, ite_eq_right (mt he.mp h), star_zero]

theorem pauliMatrix_unitary {n : ℕ} (a b : Bits n) (c : unitary ℂ) :
    pauliMatrix a b (c : ℂ) ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change pauliMatrix a b (c : ℂ) * (pauliMatrix a b (c : ℂ))ᴴ = 1
  rw [pauliMatrix_star, pauliMatrix_mul]
  have hc : (c : ℂ) * (star (c : ℂ) * character b a) * character b a = 1 := by
    calc
      _ = ((c : ℂ) * star (c : ℂ)) * (character b a * character b a) := by ring
      _ = 1 := by rw [c.property.2, character_mul_self]; simp
  have ha : a+a = 0 := by ext j; exact CharTwo.add_self_eq_zero (a j)
  have hb : b+b = 0 := by ext j; exact CharTwo.add_self_eq_zero (b j)
  rw [ha, hb, hc, pauliMatrix_one]

def pauli {n : ℕ} (a b : Bits n) (c : unitary ℂ) : Gate n :=
  ⟨pauliMatrix a b (c : ℂ), pauliMatrix_unitary a b c⟩

def characterUnit {n : ℕ} (b z : Bits n) : unitary ℂ :=
  ⟨character b z, by
    constructor <;> rw [star_character, character_mul_self]⟩

/-- 标量相位、X平移与Z字符的真实Pauli酉子群。 -/
def pauliSubgroup (n : ℕ) : Subgroup (Gate n) where
  carrier := {U | ∃ a b, ∃ c : unitary ℂ, U = pauli a b c}
  one_mem' := by
    refine ⟨0, 0, 1, ?_⟩
    apply Subtype.ext
    exact pauliMatrix_one.symm
  mul_mem' := by
    rintro U V ⟨a,b,c,rfl⟩ ⟨a',b',c',rfl⟩
    refine ⟨a+a', b+b', c*c'*characterUnit b a', ?_⟩
    apply Subtype.ext
    exact pauliMatrix_mul a b a' b' (c : ℂ) (c' : ℂ)
  inv_mem' := by
    rintro U ⟨a,b,c,rfl⟩
    refine ⟨a, b, c⁻¹*characterUnit b a, ?_⟩
    apply Subtype.ext
    exact pauliMatrix_star a b (c : ℂ)

theorem mem_pauliSubgroup {n : ℕ} (a b : Bits n) (c : unitary ℂ) :
    pauli a b c ∈ pauliSubgroup n := ⟨a,b,c,rfl⟩

/-- 物理级数从1开始，使用真实矩阵Pauli共轭递归。 -/
def IsLevel {n : ℕ} (k : ℕ) (U : Gate n) : Prop :=
  0 < k ∧ HierarchyAt (pauliSubgroup n) (k-1) U

def IsClifford {n : ℕ} (U : Gate n) : Prop := Normalizes (pauliSubgroup n) U

theorem isLevel_mul_right_clifford_iff {n k : ℕ} (hk : 2 ≤ k) {C : Gate n}
    (hC : IsClifford C) (U : Gate n) : IsLevel k (U*C) ↔ IsLevel k U := by
  obtain ⟨j,rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
  simp only [IsLevel, show (j+2)-1=j+1 by omega]
  exact and_congr_right (fun _ => hierarchy_mul_right_clifford_iff hC j U)

theorem isLevel_mul_left_clifford_iff {n k : ℕ} (hk : 2 ≤ k) {C : Gate n}
    (hC : IsClifford C) (U : Gate n) : IsLevel k (C*U) ↔ IsLevel k U := by
  obtain ⟨j,rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
  simp only [IsLevel, show (j+2)-1=j+1 by omega]
  exact and_congr_right (fun _ => hierarchy_mul_left_clifford_iff hC j U)

theorem isLevel_mono {n j k : ℕ} (hjk : j ≤ k) {U : Gate n}
    (hU : IsLevel j U) : IsLevel k U :=
  ⟨lt_of_lt_of_le hU.1 hjk, hierarchy_mono (Nat.sub_le_sub_right hjk 1) hU.2⟩

/-- 前一层的非成员证书排除所有更低的正层级。 -/
theorem not_isLevel_of_not_previous {n j k : ℕ} {U : Gate n}
    (hU : ¬ IsLevel (k-1) U) (hjk : j < k) : ¬ IsLevel j U := by
  intro hj
  exact hU (isLevel_mono (by omega) hj)

end UnifiedEJM.CliffordFoundation

