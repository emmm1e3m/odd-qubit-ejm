import OddEJM.MeasurementBridge
import OddEJM.Completeness
import OddEJM.Tensor
import OddEJM.CNOT
import OddEJM.Spectrum
import OddEJM.DensityMultiplicity

/-!
# 任意等模对角相位的实际测量桥

所有物理对象均复用计算基复振幅、电路和真实有限和偏迹。
此模块对相位函数不作核形状、奇偶性或参数个数限制。
-/
namespace UnifiedEJM.Physical

open OddEJM OddEJM.CircuitPauli
open scoped BigOperators

/-- 任意输入对角相位的真实种子。 -/
noncomputable def seed {n : ℕ} (u : Bits n → ℂ) : Vec n :=
  circuit (fun z => normFactor n * u z)

/-- 任意输入对角相位的全部有序测量列。 -/
noncomputable def measurement {n : ℕ} (u : Bits n → ℂ) (label : Bits n) : Vec n :=
  circuit (fun z => normFactor n * u z * character label z)

theorem measurement_eq_gate_column {n : ℕ} (u : Bits n → ℂ) (label : Bits n) :
    measurement u label = circuit (phaseGate u (tensorHadamard (ket label))) := by
  rw [tensorHadamard_ket]
  unfold measurement phaseGate
  congr 1
  funext z
  ring

/-- 全部测量列直接等于论文中从右至左执行的逐门电路。 -/
theorem measurement_eq_original_gate_sequence {n : ℕ} (hn : 0 < n)
    (u : Bits n → ℂ) (label : Bits n) :
    measurement u label = rightCNOTCircuit (n - 1)
      (hadamardAt (n - 1) (phaseGate u (tensorHadamard (ket label)))) := by
  rw [measurement_eq_gate_column, circuit_gate_order hn]

theorem measurement_orthonormal {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (k l : Bits n) :
    inner (measurement u k) (measurement u l) = if k = l then 1 else 0 :=
  phaseBasis_orthonormal hn u hu k l

theorem measurement_normalized {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (label : Bits n) :
    inner (measurement u label) (measurement u label) = 1 := by
  simpa using measurement_orthonormal hn u hu label label

@[simp] theorem measurement_zero {n : ℕ} (u : Bits n → ℂ) :
    measurement u 0 = seed u := by
  simp [measurement, seed, character, dot, bitSign]

theorem seed_normalized {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) : inner (seed u) (seed u) = 1 := by
  simpa using measurement_normalized hn u hu 0

/-- 实际秩一投影逐矩阵元的完备性。 -/
theorem measurement_complete {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (z w : Bits n) :
    (∑ label, measurement u label z * star (measurement u label w)) =
      if z = w then 1 else 0 := by
  let M : Matrix (Bits n) (Bits n) ℂ := Matrix.of (fun x label => measurement u label x)
  have hcol : M.conjTranspose * M = 1 := by
    ext k l
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      M, Matrix.of_apply, OddEJM.inner] using measurement_orthonormal hn u hu k l
  have hrow : M * M.conjTranspose = 1 := mul_eq_one_comm.mp hcol
  have h := congrArg (fun A : Matrix (Bits n) (Bits n) ℂ => A z w) hrow
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    M, Matrix.of_apply] using h

/-- 与边ZZ及全X轨道逐振幅相同，未把轨道同一性作为前提。 -/
theorem measurement_orbit {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ) (label : Bits n) :
    measurement u label = pauliAction (orbitX label) (orbitZ label) 1 (seed u) := by
  rw [seed, orbit_pullback hn]
  unfold measurement
  congr 1
  funext z
  simp [pauliAction, mul_comm]

theorem measurement_localX_sign {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (label : Bits n) (j : ℕ) (hj : j < n) :
    pauliExpectation (measurement u label) (unitBit n j) 0 1 =
      bitSign (localParity label j) * pauliExpectation (seed u) (unitBit n j) 0 1 := by
  rw [measurement_orbit hn, pauli_conjugation_expectation]
  have hz : dot (0 : Bits n) (orbitX label) = 0 := by simp [dot]
  simp only [character, dot_unit_right, orbitZ_coord _ _ hj, hz, bitSign_zero, one_mul]

theorem measurement_localZ_sign {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (label : Bits n) (j : ℕ) (hj : j < n) :
    pauliExpectation (measurement u label) 0 (unitBit n j) 1 =
      bitSign (coord label (n - 1)) * pauliExpectation (seed u) 0 (unitBit n j) 1 := by
  rw [measurement_orbit hn, pauli_conjugation_expectation]
  have hz : dot (orbitZ label) 0 = 0 := by simp [dot]
  simp only [character, dot_unit_left, orbitX_coord _ _ hj, hz, bitSign_zero, mul_one]

theorem measurement_localY_sign {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (label : Bits n) (j : ℕ) (hj : j < n) :
    pauliExpectation (measurement u label) (unitBit n j) (unitBit n j) Complex.I =
      bitSign (coord label (n - 1) + localParity label j) *
        pauliExpectation (seed u) (unitBit n j) (unitBit n j) Complex.I := by
  rw [measurement_orbit hn, pauli_conjugation_expectation]
  simp only [character, dot_unit_left, dot_unit_right, orbitZ_coord _ _ hj,
    orbitX_coord _ _ hj, sign_add]

theorem radius_vertex_components (m ε : ℝ) (q s : Bit) :
    (fun k => (Real.sqrt 3 * m) * Geometry.vertex ε q s k) =
      ![m * Geometry.signR q, m * ε * Geometry.signR q * Geometry.signR s,
        m * Geometry.signR s] := by
  funext k
  fin_cases k <;> simp [Geometry.vertex] <;>
    field_simp [ne_of_gt Geometry.sqrt_three_pos] <;> ring

/-- 种子的共同signed分量传播到所有实际测量列。 -/
theorem measurement_radial_components_from_seed {n : ℕ} (hn : 0 < n)
    (u : Bits n → ℂ) (m : ℝ) (label : Bits n) (j : Fin n)
    (hX : localX (seed u) j = (m : ℂ))
    (hY : localY (seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (seed u) j = (m : ℂ)) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    localX (measurement u label) j = ((Real.sqrt 3 * m : ℝ) : ℂ) * (v 0 : ℂ) ∧
    localY (measurement u label) j = ((Real.sqrt 3 * m : ℝ) : ℂ) * (v 1 : ℂ) ∧
    localZ (measurement u label) j = ((Real.sqrt 3 * m : ℝ) : ℂ) * (v 2 : ℂ) := by
  dsimp only
  have hv := radius_vertex_components m (localOrientation j)
    (localParity label j.val) (coord label (n - 1))
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  have hv2 := congrFun hv 2
  simp at hv0 hv1 hv2
  have hY' : localY (seed u) j = ((m * localOrientation j : ℝ) : ℂ) := by
    rw [hY]
    by_cases hj : j.val = n - 1 <;> simp [localOrientation, hj]
  change pauliExpectation (seed u) (unitBit n j.val) 0 1 = _ at hX
  change pauliExpectation (seed u) (unitBit n j.val) (unitBit n j.val) Complex.I = _ at hY'
  change pauliExpectation (seed u) 0 (unitBit n j.val) 1 = _ at hZ
  refine ⟨?_, ?_, ?_⟩
  · rw [localX, measurement_localX_sign hn u label j.val j.isLt, hX]
    have h := congrArg Complex.ofReal hv0
    simp only [Complex.ofReal_mul] at h
    rw [bitSign_eq_real]
    simpa only [localOutcome, Complex.ofReal_mul, mul_comm] using h.symm
  · rw [localY, measurement_localY_sign hn u label j.val j.isLt, hY',
      sign_add, bitSign_eq_real, bitSign_eq_real]
    have h := congrArg Complex.ofReal hv1
    simp only [Complex.ofReal_mul] at h
    simp only [localOutcome, Complex.ofReal_mul]
    rw [h]
    ring
  · rw [localZ, measurement_localZ_sign hn u label j.val j.isLt, hZ]
    have h := congrArg Complex.ofReal hv2
    simp only [Complex.ofReal_mul] at h
    rw [bitSign_eq_real]
    simpa only [localOutcome, Complex.ofReal_mul, mul_comm] using h.symm

/-- 对其余n−1指标的实际偏迹，由核计算的三分量接入。 -/
theorem measurement_reduced_from_seed {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (m : ℝ) (label : Bits n) (j : Fin n)
    (hX : localX (seed u) j = (m : ℂ))
    (hY : localY (seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (seed u) j = (m : ℂ)) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement u label) j = (1 / 2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      ((Real.sqrt 3 * m : ℝ) : ℂ) •
        ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ)) := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components_from_seed hn u m label j hX hY hZ
  exact reduced_radial (measurement u label) j ((Real.sqrt 3 * m : ℝ) : ℂ)
    (fun k => (Geometry.vertex (localOrientation j) (localOutcome j label).1
      (localOutcome j label).2 k : ℂ)) (measurement_normalized hn u hu label) hx hy hz

/-- 同一偏迹的Bloch矩阵形式，用于谱与实际矩阵重数。 -/
theorem measurement_reduced_bloch {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (m : ℝ) (label : Bits n) (j : Fin n)
    (hX : localX (seed u) j = (m : ℂ))
    (hY : localY (seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (seed u) j = (m : ℂ)) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement u label) j = blochMatrix 1
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (v 0 : ℂ))
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (v 1 : ℂ))
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (v 2 : ℂ)) := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components_from_seed hn u m label j hX hY hZ
  exact reduced_of_components _ j _ _ _ (measurement_normalized hn u hu label) hx hy hz

theorem measurement_purity {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (m : ℝ) (label : Bits n) (j : Fin n)
    (hX : localX (seed u) j = (m : ℂ))
    (hY : localY (seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (seed u) j = (m : ℂ)) :
    Matrix.trace (reduced (measurement u label) j * reduced (measurement u label) j) =
      (((1 + (Real.sqrt 3 * m) ^ 2) / 2 : ℝ) : ℂ) := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components_from_seed hn u m label j hX hY hZ
  have h := reduced_purity_radial (measurement u label) j ((Real.sqrt 3 * m : ℝ) : ℂ)
    (fun k => (Geometry.vertex (localOrientation j) (localOutcome j label).1
      (localOutcome j label).2 k : ℂ))
    (measurement_normalized hn u hu label) hx hy hz
    (local_vertex_complex_unit j (localOutcome j label).1 (localOutcome j label).2)
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat] using h

theorem measurement_eigenvalues {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (m : ℝ) (label : Bits n) (j : Fin n)
    (hX : localX (seed u) j = (m : ℂ))
    (hY : localY (seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (seed u) j = (m : ℂ)) :
    Matrix.det (reduced (measurement u label) j -
      ((((1 + Real.sqrt 3 * m) / 2 : ℝ) : ℂ)) • (1 : Matrix Bit Bit ℂ)) = 0 ∧
    Matrix.det (reduced (measurement u label) j -
      ((((1 - Real.sqrt 3 * m) / 2 : ℝ) : ℂ)) • (1 : Matrix Bit Bit ℂ)) = 0 := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components_from_seed hn u m label j hX hY hZ
  have hv := local_vertices_unit j (localOutcome j label).1 (localOutcome j label).2
  simp only [Geometry.dot3, Fin.sum_univ_three, ← pow_two] at hv
  have hh := fun ε hε => reduced_radial_det_eigenvalue (measurement u label) j (Real.sqrt 3 * m)
    (Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2)
    ε (measurement_normalized hn u hu label) hx hy hz hv hε
  constructor
  · simpa using hh 1 (by norm_num)
  · simpa [sub_eq_add_neg] using hh (-1) (by norm_num)

/-- 非零半径时，四个标签对应四个不同的实际局部矩阵。 -/
theorem measurement_reduced_eq_iff {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (m : ℝ) (hm : m ≠ 0)
    (label : Bits n) (j : Fin n) (a : Bit × Bit)
    (hX : localX (seed u) j = (m : ℂ))
    (hY : localY (seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (seed u) j = (m : ℂ)) :
    reduced (measurement u label) j = blochMatrix 1
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 0 : ℂ))
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 1 : ℂ))
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 2 : ℂ)) ↔
      localOutcome j label = a := by
  rw [measurement_reduced_bloch hn u hu m label j hX hY hZ]
  constructor
  · intro h
    exact radial_vertex_matrix_injective j (Real.sqrt 3 * m)
      (mul_ne_zero (ne_of_gt Geometry.sqrt_three_pos) hm) h
  · intro h
    rw [h]

/-- 计数的是实际偏迹矩阵，而非仅辅助标签。 -/
theorem measurement_reduced_multiplicity {n : ℕ} (hn : 2 ≤ n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (m : ℝ) (hm : m ≠ 0)
    (j : Fin n) (a : Bit × Bit)
    (hX : localX (seed u) j = (m : ℂ))
    (hY : localY (seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (seed u) j = (m : ℂ)) :
    Nat.card {label : Bits n // reduced (measurement u label) j = blochMatrix 1
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 0 : ℂ))
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 1 : ℂ))
      (((Real.sqrt 3 * m : ℝ) : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 2 : ℂ))} =
      2 ^ (n - 2) := by
  have he := Equiv.subtypeEquivRight (fun label : Bits n =>
    measurement_reduced_eq_iff (by omega) u hu m hm label j a hX hY hZ)
  exact (Nat.card_congr he).trans (localOutcome_fiber_card hn j a)

theorem measurement_maximally_mixed {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (label : Bits n) (j : Fin n)
    (hX : localX (seed u) j = 0) (hY : localY (seed u) j = 0)
    (hZ : localZ (seed u) j = 0) :
    reduced (measurement u label) j = (1 / 2 : ℂ) • (1 : Matrix Bit Bit ℂ) := by
  have hy : localY (seed u) j = if j.val = n - 1 then -(0 : ℂ) else 0 := by simpa using hY
  simpa using measurement_reduced_from_seed hn u hu 0 label j hX hy hZ

end UnifiedEJM.Physical

