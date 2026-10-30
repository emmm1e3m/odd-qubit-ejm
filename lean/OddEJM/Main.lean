import OddEJM.MeasurementBridge
import OddEJM.SeedExpectations
import OddEJM.OriginalPhase
import OddEJM.Tensor
import OddEJM.Completeness

namespace OddEJM
open scoped BigOperators

/-- 任意奇数n≥5、任意列、任意物理位的三个实际Pauli期望。 -/
theorem measurement_radial_components {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    localX (measurement n t label) j = (radius n t : ℂ) * (v 0 : ℂ) ∧
    localY (measurement n t label) j = (radius n t : ℂ) * (v 1 : ℂ) ∧
    localZ (measurement n t label) j = (radius n t : ℂ) * (v 2 : ℂ) := by
  exact measurement_radial_components_from_seed (by omega) t label j
    (seed_localX hn ho t j.val j.isLt) (seed_localY hn ho t j.val j.isLt)
    (seed_localZ hn ho t j.val j.isLt)

/-- 完整局部密度矩阵定理：无待证种子期望或归一化前提。 -/
theorem measurement_reduced {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement n t label) j = (1 / 2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      (radius n t : ℂ) • ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ)) := by
  exact measurement_reduced_from_seed (by omega) t label j
    (seed_localX hn ho t j.val j.isLt) (seed_localY hn ho t j.val j.isLt)
    (seed_localZ hn ho t j.val j.isLt)

/-- 等价的逐矩阵元闭式，仍以真实偏迹作为左端。 -/
theorem measurement_reduced_bloch {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement n t label) j = blochMatrix 1
      ((radius n t : ℂ) * (v 0 : ℂ)) ((radius n t : ℂ) * (v 1 : ℂ))
      ((radius n t : ℂ) * (v 2 : ℂ)) := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components hn ho t label j
  exact reduced_of_components _ j _ _ _ (measurement_normalized (by omega) t label) hx hy hz

/-- 全参数相位直接按原基本对称相位与显式布尔支持给出。 -/
theorem measurement_original_phase {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (label : Bits n) :
    measurement n t label = circuit (fun z => normFactor n *
      (originalDiagonal z * anglePhase t ^ (phaseSupport z).val) * character label z) := by
  unfold measurement
  congr 1
  funext z
  rw [rawPhase_eq_originalDiagonal hn]

/-- 共同纯度来自实际偏迹的矩阵乘法。 -/
theorem measurement_purity {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    Matrix.trace (reduced (measurement n t label) j * reduced (measurement n t label) j) =
      (((1 + radius n t ^ 2) / 2 : ℝ) : ℂ) := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components hn ho t label j
  have h := reduced_purity_radial (measurement n t label) j (radius n t : ℂ)
    (fun k => (Geometry.vertex (localOrientation j) (localOutcome j label).1
      (localOutcome j label).2 k : ℂ))
    (measurement_normalized (by omega) t label) hx hy hz
    (local_vertex_complex_unit j (localOutcome j label).1 (localOutcome j label).2)
  push_cast
  exact h

/-- 收缩端点的每一列、每一物理位均为完全混合态。 -/
theorem measurement_maximally_mixed {n : ℕ} (hn : 5 ≤ n) (ho : Odd n)
    (label : Bits n) (j : Fin n) :
    reduced (measurement n (Real.pi / 2) label) j = (1 / 2 : ℂ) • (1 : Matrix Bit Bit ℂ) := by
  rw [measurement_reduced hn ho]
  simp only [radius_eq_geometry, Geometry.radius_at_right, Complex.ofReal_zero,
    zero_smul, add_zero]

/-- 任意奇数n≥5的完整EJM族，所有断言都落实到原振幅measurement。 -/
theorem odd_ejm_family {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) :
    (∀ t k l, inner (measurement n t k) (measurement n t l) = if k = l then 1 else 0) ∧
    (∀ t label j,
      let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
      reduced (measurement n t label) j = (1 / 2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
        (radius n t : ℂ) • ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ))) ∧
    (∀ (j : Fin n) (q s : Bit),
      Geometry.dot3 (Geometry.vertex (localOrientation j) q s)
        (Geometry.vertex (localOrientation j) q s) = 1) ∧
    (∀ (j : Fin n) (a b : Bit × Bit), a ≠ b →
      Geometry.dot3 (Geometry.vertex (localOrientation j) a.1 a.2)
        (Geometry.vertex (localOrientation j) b.1 b.2) = -(1 / 3 : ℝ)) ∧
    (∀ (j : Fin n) (a : Bit × Bit),
      Nat.card {label : Bits n // localOutcome j label = a} = 2 ^ (n - 2)) ∧
    (radius n '' Geometry.parameterInterval = Set.Icc 0 (Geometry.radiusMax n)) ∧
    Continuous (radius n) ∧ StrictAntiOn (radius n) Geometry.parameterInterval ∧
    (∀ label, measurement n 0 label =
      circuit (fun z => normFactor n * originalDiagonal z * character label z)) ∧
    (∀ t label, measurement n t label =
      circuit (phaseGate (rawPhase (anglePhase t)) (tensorHadamard (ket label)))) ∧
    (∀ (t : ℝ) (z w : Bits n), (∑ label, measurement n t label z * star (measurement n t label w)) =
      if z = w then 1 else 0) := by
  refine ⟨measurement_orthonormal (by omega), measurement_reduced hn ho,
    local_vertices_unit, local_vertices_distinct_dot, localOutcome_fiber_card (by omega),
    radius_image_exact (by omega), radius_continuous n, radius_strict_decreasing n,
    measurement_basepoint_original (by omega), measurement_eq_gate_column n,
    measurement_complete (by omega)⟩

end OddEJM
