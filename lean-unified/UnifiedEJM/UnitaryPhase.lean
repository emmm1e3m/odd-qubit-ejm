import UnifiedEJM.CliffordFoundation

noncomputable section
open scoped BigOperators Matrix
open OddEJM

namespace UnifiedEJM.CliffordFoundation

abbrev Phase (n : ℕ) := Bits n → unitary ℂ

def phaseDifference {n : ℕ} (a : Bits n) (u : Phase n) : Phase n :=
  fun z => u (z+a) * (u z)⁻¹

def PhaseDepth {n : ℕ} : ℕ → Phase n → Prop
  | 0, u => ∀ x y, u x = u y
  | k+1, u => ∀ a, PhaseDepth k (phaseDifference a u)

/-- 任意二元位空间的复乘法字符都是一个实际Pauli Z字符。 -/
theorem exists_character_of_additive {n : ℕ} (χ : Bits n → ℂ)
    (hzero : χ 0 = 1) (hadd : ∀ x y, χ (x+y)=χ x*χ y) :
    ∃ b : Bits n, ∀ z, χ z = character b z := by
  classical
  let e (j : Fin n) : Bits n := Pi.single j 1
  have hsquare (j : Fin n) : χ (e j) * χ (e j) = 1 := by
    rw [← hadd]
    have he : e j + e j = 0 := by ext i; exact CharTwo.add_self_eq_zero (e j i)
    rw [he,hzero]
  let b : Bits n := fun j => if χ (e j) = 1 then 0 else 1
  refine ⟨b, fun z => ?_⟩
  have hb (j : Fin n) : χ (e j) = bitSign (b j) := by
    rcases (mul_self_eq_one_iff.mp (hsquare j)) with h | h
    · simp [b,h,bitSign]
    · simp [b,h,bitSign]
  have hsum (s : Finset (Fin n)) :
      χ (∑ j ∈ s, Pi.single j (z j)) = ∏ j ∈ s, χ (Pi.single j (z j)) := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert j s hj ih => simp only [Finset.sum_insert hj, Finset.prod_insert hj, hadd, ih]
  have hvec : (∑ j : Fin n, Pi.single j (z j)) = z := by
    ext i
    simp
  calc
    χ z = χ (∑ j : Fin n, Pi.single j (z j)) := congrArg χ hvec.symm
    _ = ∏ j : Fin n, χ (Pi.single j (z j)) := hsum Finset.univ
    _ = ∏ j : Fin n, bitSign (b j * z j) := by
      apply Finset.prod_congr rfl
      intro j _
      rcases CircuitPauli.bit_cases (z j) with hj | hj
      · simp [hj,hzero]
      · simpa [hj,e] using hb j
    _ = character b z := (CircuitPauli.bitSign_sum Finset.univ (fun j => b j*z j)).symm

def diagonalGate {n : ℕ} (u : Phase n) : Gate n :=
  ⟨Matrix.diagonal (fun z => (u z : ℂ)), by
    apply Matrix.diagonal_mem_unitary.mpr
    constructor <;> ext z
    · exact (u z).property.1
    · exact (u z).property.2⟩

@[simp] theorem diagonalGate_apply {n : ℕ} (u : Phase n) (x y : Bits n) :
    diagonalGate u x y = if x=y then (u x : ℂ) else 0 := by
  rfl

theorem phaseDepth_one_iff {n : ℕ} (u : Phase n) :
    PhaseDepth 1 u ↔ ∃ b : Bits n, ∃ c : unitary ℂ,
      ∀ z, (u z : ℂ) = (c : ℂ) * character b z := by
  constructor
  · intro h
    let χ : Bits n → ℂ := fun z => (u z : ℂ) * ((u 0 : ℂ))⁻¹
    have hne (z : Bits n) : (u z : ℂ) ≠ 0 := by
      intro hz
      have ht := (u z).property.2
      simp [hz] at ht
    have hzero : χ 0 = 1 := by simp [χ,hne]
    have hadd : ∀ x y, χ (x+y) = χ x * χ y := by
      intro x y
      have hd := congrArg (fun v : unitary ℂ => (v : ℂ)) (h y x 0)
      simp only [phaseDifference, Submonoid.coe_mul, Unitary.coe_inv] at hd
      change (u (x+y) : ℂ) * ((u x : ℂ))⁻¹ =
        (u (0+y) : ℂ) * ((u 0 : ℂ))⁻¹ at hd
      simp only [zero_add] at hd
      dsimp [χ]
      field_simp [hne] at hd ⊢
      linear_combination hd
    obtain ⟨b,hb⟩ := exists_character_of_additive χ hzero hadd
    refine ⟨b,u 0, fun z => ?_⟩
    have hh := hb z
    dsimp [χ] at hh
    calc
      (u z : ℂ) = (u 0 : ℂ) * ((u z : ℂ) * (u 0 : ℂ)⁻¹) := by field_simp [hne 0]
      _ = _ := by rw [hh]
  · rintro ⟨b,c,hu⟩ a x y
    apply Subtype.ext
    simp only [phaseDifference, Submonoid.coe_mul, Unitary.coe_inv]
    change (u (x+a) : ℂ) * ((u x : ℂ))⁻¹ =
      (u (y+a) : ℂ) * ((u y : ℂ))⁻¹
    simp only [hu, CircuitPauli.char_add]
    have hc : (c : ℂ) ≠ 0 := by
      intro h; have hh := c.property.2; simp [h] at hh
    have hx : character b x ≠ 0 := by
      intro h; have hh := character_mul_self b x; simp [h] at hh
    have hy : character b y ≠ 0 := by
      intro h; have hh := character_mul_self b y; simp [h] at hh
    field_simp

theorem unitary_val_ne_zero (c : unitary ℂ) : (c : ℂ) ≠ 0 := by
  intro h
  have hh := c.property.2
  simp [h] at hh

theorem unitary_star_val (c : unitary ℂ) : star (c : ℂ) = (c : ℂ)⁻¹ := by
  change ((star c : unitary ℂ) : ℂ) = _
  rw [Unitary.star_eq_inv, Unitary.coe_inv]

theorem diagonalGate_mem_pauli_iff {n : ℕ} (u : Phase n) :
    diagonalGate u ∈ pauliSubgroup n ↔ PhaseDepth 1 u := by
  rw [phaseDepth_one_iff]
  constructor
  · rintro ⟨a,b,c,he⟩
    have ha : a = 0 := by
      by_contra hne
      have hh := congrArg (fun U : Gate n => U a 0) he
      have hz : (0 : ℂ) = (c : ℂ) := by
        simpa [diagonalGate_apply, pauli, pauliMatrix, hne, character, dot, bitSign] using hh
      exact unitary_val_ne_zero c hz.symm
    subst a
    refine ⟨b,c,fun z => ?_⟩
    have hh := congrArg (fun U : Gate n => U z z) he
    simpa [diagonalGate_apply, pauli, pauliMatrix] using hh
  · rintro ⟨b,c,hu⟩
    refine ⟨0,b,c,?_⟩
    apply Subtype.ext
    ext x y
    change (if x=y then (u x : ℂ) else 0) =
      (if x=y+0 then (c : ℂ)*character b y else 0)
    by_cases h : x=y
    · subst x; simp [hu]
    · simp [h]

/-- 对角酉共轭真实Pauli的余项正是有限差分相位。 -/
theorem diagonalGate_conjugate_pauli {n : ℕ} (u : Phase n)
    (a b : Bits n) (c : unitary ℂ) :
    diagonalGate u * pauli a b c * (diagonalGate u)⁻¹ =
      pauli a b c * diagonalGate (phaseDifference a u) := by
  apply Subtype.ext
  ext x y
  change (Matrix.diagonal (fun z => (u z : ℂ)) * pauliMatrix a b (c : ℂ) *
      (Matrix.diagonal (fun z => (u z : ℂ)))ᴴ) x y =
    (pauliMatrix a b (c : ℂ) * Matrix.diagonal
      (fun z => ((phaseDifference a u z) : ℂ))) x y
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    phaseDifference, Submonoid.coe_mul, Unitary.coe_inv, pauliMatrix, Pi.star_def, unitary_star_val]
  by_cases h : x=y+a
  · rw [ite_eq_left h]
    rw [h]
    ring
  · simp [h]

/-- 有限差分深度与真实矩阵Clifford层级等价，不另定义一个替代层级。 -/
theorem diagonalGate_hierarchyAt_iff {n : ℕ} (k : ℕ) (u : Phase n) :
    HierarchyAt (pauliSubgroup n) k (diagonalGate u) ↔ PhaseDepth (k+1) u := by
  induction k generalizing u with
  | zero => exact diagonalGate_mem_pauli_iff u
  | succ k ih =>
      constructor
      · intro h a
        have hh := h (pauli a 0 1) (mem_pauliSubgroup a 0 1)
        rw [diagonalGate_conjugate_pauli,
          hierarchy_mul_left_pauli_iff (mem_pauliSubgroup a 0 1)] at hh
        exact (ih _).mp hh
      · intro h p hp
        obtain ⟨a,b,c,rfl⟩ := hp
        rw [diagonalGate_conjugate_pauli,
          hierarchy_mul_left_pauli_iff (mem_pauliSubgroup a b c)]
        exact (ih _).mpr (h a)

theorem diagonalGate_isLevel_iff {n k : ℕ} (hk : 0 < k) (u : Phase n) :
    IsLevel k (diagonalGate u) ↔ PhaseDepth k u := by
  obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1, by omega⟩
  simp only [IsLevel, Nat.add_sub_cancel, show 0 < j+1 by omega, true_and]
  exact diagonalGate_hierarchyAt_iff j u

end UnifiedEJM.CliffordFoundation

