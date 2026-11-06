import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

namespace UnifiedEJM.CliffordFoundation

section Abstract
variable {G : Type*} [Group G]

/-- 零下标表示物理第一层；递归直接使用群共轭。 -/
def HierarchyAt (P : Subgroup G) : ℕ → G → Prop
  | 0, U => U ∈ P
  | k+1, U => ∀ p ∈ P, HierarchyAt P k (U*p*U⁻¹)

/-- Clifford是实际Pauli子群的正规化子。 -/
def Normalizes (P : Subgroup G) (C : G) : Prop :=
  ∀ p, p ∈ P ↔ C*p*C⁻¹ ∈ P

theorem normalizes_inv {P : Subgroup G} {C : G} (h : Normalizes P C) :
    Normalizes P C⁻¹ := by
  intro p
  have he : C * (C⁻¹*p*(C⁻¹)⁻¹) * C⁻¹ = p := by group
  simpa only [he] using (h (C⁻¹*p*(C⁻¹)⁻¹)).symm

theorem normalizes_of_mem {P : Subgroup G} {p : G} (hp : p ∈ P) :
    Normalizes P p := by
  intro x
  constructor
  · intro hx
    exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
  · intro hx
    have hh := P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh

theorem hierarchy_conjugate {P : Subgroup G} {C : G} (hC : Normalizes P C)
    (k : ℕ) {U : G} (hU : HierarchyAt P k U) :
    HierarchyAt P k (C*U*C⁻¹) := by
  induction k generalizing U with
  | zero => exact (hC U).mp hU
  | succ k ih =>
      intro p hp
      have hp' : C⁻¹*p*(C⁻¹)⁻¹ ∈ P := (normalizes_inv hC p).mp hp
      have ht := ih (hU _ hp')
      have he : (C*U*C⁻¹)*p*(C*U*C⁻¹)⁻¹ =
          C*(U*(C⁻¹*p*(C⁻¹)⁻¹)*U⁻¹)*C⁻¹ := by group
      rw [he]
      exact ht

theorem hierarchy_conjugate_iff {P : Subgroup G} {C : G} (hC : Normalizes P C)
    (k : ℕ) (U : G) : HierarchyAt P k (C*U*C⁻¹) ↔ HierarchyAt P k U := by
  constructor
  · intro h
    have hh := hierarchy_conjugate (normalizes_inv hC) k h
    simpa only [inv_mul_cancel_left, mul_assoc, inv_inv, inv_mul_cancel, mul_one] using hh
  · exact hierarchy_conjugate hC k

theorem hierarchy_mul_right_clifford {P : Subgroup G} {C : G} (hC : Normalizes P C)
    (k : ℕ) {U : G} (hU : HierarchyAt P (k+1) U) :
    HierarchyAt P (k+1) (U*C) := by
  intro p hp
  have he : (U*C)*p*(U*C)⁻¹ = U*(C*p*C⁻¹)*U⁻¹ := by group
  rw [he]
  exact hU _ ((hC p).mp hp)

theorem hierarchy_mul_right_clifford_iff {P : Subgroup G} {C : G}
    (hC : Normalizes P C) (k : ℕ) (U : G) :
    HierarchyAt P (k+1) (U*C) ↔ HierarchyAt P (k+1) U := by
  constructor
  · intro h
    have hh := hierarchy_mul_right_clifford (normalizes_inv hC) k h
    simpa only [mul_inv_cancel_right] using hh
  · exact hierarchy_mul_right_clifford hC k

theorem hierarchy_mul_left_clifford_iff {P : Subgroup G} {C : G}
    (hC : Normalizes P C) (k : ℕ) (U : G) :
    HierarchyAt P (k+1) (C*U) ↔ HierarchyAt P (k+1) U := by
  have he : C*U = (C*U*C⁻¹)*C := by group
  rw [he, hierarchy_mul_right_clifford_iff hC,
    hierarchy_conjugate_iff hC]

theorem hierarchy_mul_right_pauli_iff {P : Subgroup G} {p : G}
    (hp : p ∈ P) (k : ℕ) (U : G) :
    HierarchyAt P k (U*p) ↔ HierarchyAt P k U := by
  cases k with
  | zero =>
      constructor
      · intro h
        have hh := P.mul_mem h (P.inv_mem hp)
        simpa only [HierarchyAt, mul_inv_cancel_right] using hh
      · intro h; exact P.mul_mem h hp
  | succ k => exact hierarchy_mul_right_clifford_iff (normalizes_of_mem hp) k U

theorem hierarchy_mul_left_pauli_iff {P : Subgroup G} {p : G}
    (hp : p ∈ P) (k : ℕ) (U : G) :
    HierarchyAt P k (p*U) ↔ HierarchyAt P k U := by
  cases k with
  | zero =>
      constructor
      · intro h
        have hh := P.mul_mem (P.inv_mem hp) h
        simpa only [HierarchyAt, inv_mul_cancel_left] using hh
      · intro h; exact P.mul_mem hp h
  | succ k => exact hierarchy_mul_left_clifford_iff (normalizes_of_mem hp) k U

/-- 层级嵌套保证相邻层的非成员证书确实给出最小层级。 -/
theorem hierarchy_step {P : Subgroup G} (k : ℕ) {U : G}
    (hU : HierarchyAt P k U) : HierarchyAt P (k+1) U := by
  induction k generalizing U with
  | zero =>
      intro p hp
      exact P.mul_mem (P.mul_mem hU hp) (P.inv_mem hU)
  | succ k ih =>
      intro p hp
      exact ih (hU p hp)

theorem hierarchy_mono {P : Subgroup G} {j k : ℕ} (hjk : j ≤ k) {U : G}
    (hU : HierarchyAt P j U) : HierarchyAt P k U := by
  induction k, hjk using Nat.le_induction with
  | base => exact hU
  | succ k _ ih => exact hierarchy_step k ih

end Abstract
end UnifiedEJM.CliffordFoundation
