import UnifiedEJM.Physical
import OddEJM.CNOT
import Mathlib.LinearAlgebra.UnitaryGroup
import UnifiedEJM.CliffordFoundation

noncomputable section
open scoped BigOperators Matrix

namespace UnifiedEJM.PhysicsCircuit
open OddEJM OddEJM.CircuitPauli
open CliffordFoundation

/-- 既有原门电路的真实计算基矩阵。 -/
def circuitMatrix (n : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  fun x y => circuit (ket y) x

/-- Hadamard张量积的真实计算基矩阵。 -/
def hadamardMatrix (n : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  fun x y => normFactor n * character y x

theorem circuitMatrix_mulVec (n : ℕ) (v : Vec n) :
    (circuitMatrix n).mulVec v = circuit v := by
  funext x
  simp only [Matrix.mulVec, dotProduct, circuitMatrix, circuit, chain, hadamardAt]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  simp [ket]

theorem circuitMatrix_gate_order {n : ℕ} (hn : 0 < n) (v : Vec n) :
    (circuitMatrix n).mulVec v = rightCNOTCircuit (n-1) (hadamardAt (n-1) v) := by
  rw [circuitMatrix_mulVec, circuit_gate_order hn]

theorem hadamardMatrix_mulVec (n : ℕ) (v : Vec n) :
    (hadamardMatrix n).mulVec v = tensorHadamard v := by
  funext x
  simp [Matrix.mulVec, dotProduct, hadamardMatrix, tensorHadamard,
    tensorHadamardKernel_eq_character]

theorem ket_inner {n : ℕ} (k l : Bits n) :
    OddEJM.inner (ket k) (ket l) = if k = l then 1 else 0 := by
  simp [OddEJM.inner, ket, eq_comm]

theorem circuitMatrix_unitary {n : ℕ} (hn : 0 < n) :
    circuitMatrix n ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext k l
  have h := circuit_inner hn (ket k) (ket l)
  rw [ket_inner] at h
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, circuitMatrix,
    Matrix.one_apply, OddEJM.inner] using h

theorem hadamardMatrix_unitary (n : ℕ) :
    hadamardMatrix n ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext k l
  have h := phaseColumn_orthonormal (fun _ : Bits n => (1:ℂ)) (by simp) k l
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hadamardMatrix,
    Matrix.one_apply, OddEJM.inner] using h

def circuitGate {n : ℕ} (hn : 0 < n) : Matrix.unitaryGroup (Bits n) ℂ :=
  ⟨circuitMatrix n, circuitMatrix_unitary hn⟩

def hadamardGate (n : ℕ) : Matrix.unitaryGroup (Bits n) ℂ :=
  ⟨hadamardMatrix n, hadamardMatrix_unitary n⟩

theorem character_symm {n : ℕ} (a b : Bits n) : character a b = character b a := by
  simp [character, dot, mul_comm]

def prefixMask {n : ℕ} (b : Bits n) : Bits n :=
  fun k => ∑ j, if j ≤ k then b j else 0

theorem dot_prefix {n : ℕ} (b z : Bits n) : dot (prefixMask b) z = dot b (suffix z) := by
  simp only [dot, prefixMask, suffix, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

theorem prefix_edgeMask {n : ℕ} (b : Bits n) : prefixMask (edgeMask b) = b := by
  funext j
  have h : dot (prefixMask (edgeMask b)) (unitBit n j.val) = dot b (unitBit n j.val) := by
    rw [dot_prefix, dot_edgeMask, difference_suffix]
  simpa [dot_unit_right, coord, j.isLt] using h

theorem edgeMask_prefix {n : ℕ} (b : Bits n) : edgeMask (prefixMask b) = b := by
  funext j
  have h : dot (edgeMask (prefixMask b)) (unitBit n j.val) = dot b (unitBit n j.val) := by
    rw [dot_edgeMask, dot_prefix, suffix_difference]
  simpa [dot_unit_right, coord, j.isLt] using h

theorem chain_pauli_forward {n : ℕ} (a b : Bits n) (c : ℂ) (v : Vec n) :
    chain (pauliAction a b c v) = pauliAction (suffix a) (edgeMask b) c (chain v) := by
  symm
  have h := chain_pauli (suffix a) (edgeMask b) b c v
    (fun z => by simp [character, dot_edgeMask])
  simpa only [difference_suffix] using h

theorem tensorHadamard_pauli {n : ℕ} (a b : Bits n) (c : ℂ) (v : Vec n) :
    pauliAction a b c (tensorHadamard v) =
      tensorHadamard (pauliAction b a (c * character a b) v) := by
  funext z
  simp only [pauliAction, tensorHadamard, tensorHadamardKernel_eq_character]
  rw [Finset.mul_sum]
  have hs := Equiv.sum_comp (Equiv.addRight b)
    (fun y : Bits n => normFactor n * character y z *
      (c * character a b * character a (y+b) * v (y+b)))
  rw [← hs]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Equiv.coe_addRight, add_assoc, bits_add_self, add_zero,
    character_add, character_add_left]
  rw [character_symm y a, character_symm b a]
  ring

theorem bitSign_mul_self (b : Bit) : bitSign b * bitSign b = 1 := by
  rcases CircuitPauli.bit_cases b with rfl | rfl <;> norm_num [bitSign]

def bitSignUnit (b : Bit) : unitary ℂ :=
  ⟨bitSign b, by
    rcases CircuitPauli.bit_cases b with rfl | rfl <;> constructor <;> norm_num [bitSign]⟩

theorem setBit_coord {n : ℕ} (a : Bits n) (j : ℕ) : setBit a j (coord a j) = a := by
  apply setBit_eq_self
  rfl

theorem hadamard_pauli_forward {n : ℕ} (j : ℕ) (hj : j < n)
    (a b : Bits n) (c : ℂ) (v : Vec n) :
    hadamardAt j (pauliAction a b c v) =
      pauliAction (setBit a j (coord b j)) (setBit b j (coord a j))
        (c * bitSign (coord a j * coord b j)) (hadamardAt j v) := by
  have h := hadamard_pauli j hj (setBit a j (coord b j))
    (setBit b j (coord a j)) (c * bitSign (coord a j * coord b j)) v
  rw [coord_setBit _ _ _ hj, coord_setBit _ _ _ hj,
    setBit_twice, setBit_twice, setBit_coord, setBit_coord] at h
  have hc : c * bitSign (coord a j * coord b j) * bitSign (coord b j * coord a j) = c := by
    rw [mul_comm (coord b j), mul_assoc, bitSign_mul_self, mul_one]
  simpa only [hc] using h.symm

theorem circuit_pauli_forward {n : ℕ} (hn : 0 < n)
    (a b : Bits n) (c : ℂ) (v : Vec n) :
    circuit (pauliAction a b c v) =
      pauliAction (suffix (setBit a (n-1) (coord b (n-1))))
        (edgeMask (setBit b (n-1) (coord a (n-1))))
        (c * bitSign (coord a (n-1) * coord b (n-1))) (circuit v) := by
  unfold circuit
  rw [hadamard_pauli_forward (n-1) (by omega), chain_pauli_forward]

theorem pauliMatrix_mulVec {n : ℕ} (a b : Bits n) (c : ℂ) (v : Vec n) :
    (pauliMatrix a b c).mulVec v = pauliAction a b c v := by
  funext x
  simp only [Matrix.mulVec, dotProduct, pauliMatrix, pauliAction]
  rw [Finset.sum_eq_single (x+a)]
  · simp [add_assoc, bits_add_self]
  · intro y _ hy
    have hh : x ≠ y+a := by
      intro hh
      apply hy
      rw [hh, add_assoc, bits_add_self, add_zero]
    simp [hh]
  · simp

theorem isClifford_of_intertwines {n : ℕ} (U : Gate n)
    (hf : ∀ a b c, ∃ a' b' c', U * pauli a b c = pauli a' b' c' * U)
    (hb : ∀ a b c, ∃ a' b' c', pauli a b c * U = U * pauli a' b' c') :
    IsClifford U := by
  intro p
  constructor
  · rintro ⟨a,b,c,rfl⟩
    obtain ⟨a',b',c',hh⟩ := hf a b c
    refine ⟨a',b',c',?_⟩
    rw [hh]
    group
  · rintro ⟨a,b,c,hp⟩
    obtain ⟨a',b',c',hh⟩ := hb a b c
    refine ⟨a',b',c',?_⟩
    have he : U*p = U*pauli a' b' c' := by
      rw [← hh, ← hp]
      group
    exact mul_left_cancel he

theorem circuitGate_isClifford {n : ℕ} (hn : 0 < n) :
    IsClifford (circuitGate hn) := by
  apply isClifford_of_intertwines
  · intro a b c
    refine ⟨suffix (setBit a (n-1) (coord b (n-1))),
      edgeMask (setBit b (n-1) (coord a (n-1))),
      c * bitSignUnit (coord a (n-1) * coord b (n-1)), ?_⟩
    apply Subtype.ext
    change circuitMatrix n * pauliMatrix a b (c:ℂ) = _
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simp only [Submonoid.coe_mul, pauli, circuitGate, bitSignUnit,
      ← Matrix.mulVec_mulVec, circuitMatrix_mulVec, pauliMatrix_mulVec]
    exact circuit_pauli_forward hn a b (c:ℂ) v
  · intro a b c
    refine ⟨setBit (difference a) (n-1) (coord (prefixMask b) (n-1)),
      setBit (prefixMask b) (n-1) (coord (difference a) (n-1)),
      c * bitSignUnit (coord (difference a) (n-1) * coord (prefixMask b) (n-1)), ?_⟩
    apply Subtype.ext
    change pauliMatrix a b (c:ℂ) * circuitMatrix n = _
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simp only [Submonoid.coe_mul, pauli, circuitGate, bitSignUnit,
      ← Matrix.mulVec_mulVec, circuitMatrix_mulVec, pauliMatrix_mulVec]
    exact circuit_pauli hn a b (prefixMask b) (c:ℂ) v
      (fun z => by simp [character, dot_prefix, suffix_difference])

theorem hadamardGate_isClifford (n : ℕ) : IsClifford (hadamardGate n) := by
  apply isClifford_of_intertwines
  · intro a b c
    refine ⟨b, a, c * characterUnit a b, ?_⟩
    apply Subtype.ext
    change hadamardMatrix n * pauliMatrix a b (c:ℂ) = _
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simp only [Submonoid.coe_mul, pauli, hadamardGate, characterUnit,
      ← Matrix.mulVec_mulVec, hadamardMatrix_mulVec, pauliMatrix_mulVec]
    have h := tensorHadamard_pauli b a ((c:ℂ)*character a b) v
    have hc : (c:ℂ)*character a b*character b a = c := by
      rw [character_symm b a, mul_assoc, OddEJM.character_mul_self, mul_one]
    simpa only [hc] using h.symm
  · intro a b c
    refine ⟨b, a, c * characterUnit a b, ?_⟩
    apply Subtype.ext
    change pauliMatrix a b (c:ℂ) * hadamardMatrix n = _
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simp only [Submonoid.coe_mul, pauli, hadamardGate, characterUnit,
      ← Matrix.mulVec_mulVec, hadamardMatrix_mulVec, pauliMatrix_mulVec]
    exact tensorHadamard_pauli a b (c:ℂ) v

/-- 论文的完整测量矩阵等于原电路、对角相位及H张量积之乘积。 -/
theorem measurement_matrix_factorization {n : ℕ} (u : Bits n → ℂ) :
    (fun x k => Physical.measurement u k x) =
      circuitMatrix n * Matrix.diagonal u * hadamardMatrix n := by
  ext x k
  have h := congrFun (circuitMatrix_mulVec n
    (fun y => u y * (normFactor n * character k y))) x
  change Physical.measurement u k x =
    ∑ j, (circuitMatrix n * Matrix.diagonal u) x j * hadamardMatrix n j k
  simp only [Matrix.mul_diagonal]
  simpa [Matrix.mulVec, dotProduct, hadamardMatrix,
    Physical.measurement, mul_assoc, mul_comm, mul_left_comm] using h.symm

/-- 将相位酉矩阵置于论文的真实前后电路之间。 -/
def measurementGate {n : ℕ} (hn : 0 < n) (D : Gate n) : Gate n :=
  circuitGate hn * D * hadamardGate n

theorem measurementGate_matrix {n : ℕ} (hn : 0 < n) (D : Gate n)
    (u : Bits n → ℂ) (hD : (D : Matrix (Bits n) (Bits n) ℂ) = Matrix.diagonal u) :
    (measurementGate hn D : Matrix (Bits n) (Bits n) ℂ) =
      fun x k => Physical.measurement u k x := by
  rw [measurement_matrix_factorization]
  change circuitMatrix n * (D : Matrix (Bits n) (Bits n) ℂ) * hadamardMatrix n = _
  rw [hD]

/-- Clifford前后电路保持每一个至少为二的真实共轭层级。 -/
theorem isLevel_measurementGate_iff {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    (D : Gate n) : IsLevel k (measurementGate hn D) ↔ IsLevel k D := by
  unfold measurementGate
  rw [isLevel_mul_right_clifford_iff hk (hadamardGate_isClifford n),
    isLevel_mul_left_clifford_iff hk (circuitGate_isClifford hn)]

end UnifiedEJM.PhysicsCircuit
