import UnifiedEJM.Seed
import UnifiedEJM.Physical
import UnifiedEJM.Features

namespace UnifiedEJM
open OddEJM
open scoped BigOperators

/-- 新相位的酉性逐输入核验。 -/
theorem measurement_orthonormal {n : ℕ} (hn : 0 < n) (t : ℝ) (k l : Bits n) :
    inner (measurement n t k) (measurement n t l) = if k = l then 1 else 0 :=
  Physical.measurement_orthonormal hn (rawPhase (anglePhase t))
    (rawPhase_star_mul_self _ (anglePhase_norm t)) k l

/-- 与全部实际H张量输入列相同。 -/
theorem measurement_eq_gate_column (n : ℕ) (t : ℝ) (label : Bits n) :
    measurement n t label = circuit (phaseGate (rawPhase (anglePhase t))
      (tensorHadamard (ket label))) :=
  Physical.measurement_eq_gate_column _ _

/-- 新版核、任意n≥5的完整约化密度矩阵。 -/
theorem measurement_reduced {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement n t label) j = (1 / 2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      (radius n t : ℂ) • ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ)) := by
  exact Physical.measurement_reduced_from_seed (by omega) (rawPhase (anglePhase t))
    (rawPhase_star_mul_self _ (anglePhase_norm t)) (componentScale n t) label j
    (seed_localX hn t j.val j.isLt) (seed_localY hn t j.val j.isLt)
    (seed_localZ hn t j.val j.isLt)

theorem measurement_complete {n : ℕ} (hn : 0 < n) (t : ℝ) (z w : Bits n) :
    (∑ label, measurement n t label z * star (measurement n t label w)) =
      if z = w then 1 else 0 :=
  Physical.measurement_complete hn (rawPhase (anglePhase t))
    (rawPhase_star_mul_self _ (anglePhase_norm t)) z w

/-- 真正偏迹的纯度，不把Bloch公式当定义。 -/
theorem measurement_purity {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    Matrix.trace (reduced (measurement n t label) j * reduced (measurement n t label) j) =
      (((1 + radius n t ^ 2) / 2 : ℝ) : ℂ) :=
  Physical.measurement_purity (by omega) (rawPhase (anglePhase t))
    (rawPhase_star_mul_self _ (anglePhase_norm t)) (componentScale n t) label j
    (seed_localX hn t j.val j.isLt) (seed_localY hn t j.val j.isLt)
    (seed_localZ hn t j.val j.isLt)

/-- 两个真实约化谱值的特征多项式证书。 -/
theorem measurement_eigenvalues {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    Matrix.det (reduced (measurement n t label) j -
      ((((1 + radius n t) / 2 : ℝ) : ℂ)) • (1 : Matrix Bit Bit ℂ)) = 0 ∧
    Matrix.det (reduced (measurement n t label) j -
      ((((1 - radius n t) / 2 : ℝ) : ℂ)) • (1 : Matrix Bit Bit ℂ)) = 0 :=
  Physical.measurement_eigenvalues (by omega) (rawPhase (anglePhase t))
    (rawPhase_star_mul_self _ (anglePhase_norm t)) (componentScale n t) label j
    (seed_localX hn t j.val j.isLt) (seed_localY hn t j.val j.isLt)
    (seed_localZ hn t j.val j.isLt)

/-- 收缩端点的全部实际单比特约化态都是I/2。 -/
theorem measurement_maximally_mixed {n : ℕ} (hn : 5 ≤ n)
    (label : Bits n) (j : Fin n) :
    reduced (measurement n (Real.pi / 2) label) j =
      (1 / 2 : ℂ) • (1 : Matrix Bit Bit ℂ) := by
  rw [measurement_reduced hn]
  simp only [radius_eq_geometry, Geometry.radius_at_right, Complex.ofReal_zero,
    zero_smul, add_zero]

/-- 正半径时计数真实局部密度矩阵，每个顶点恰出现2^(n-2)次。 -/
theorem measurement_reduced_multiplicity {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (ht : radius n t ≠ 0) (j : Fin n) (a : Bit × Bit) :
    Nat.card {label : Bits n // reduced (measurement n t label) j = blochMatrix 1
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 0 : ℂ))
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 1 : ℂ))
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 2 : ℂ))} =
      2 ^ (n - 2) := by
  have hm : componentScale n t ≠ 0 := by
    intro hm
    apply ht
    simp only [radius, hm, mul_zero]
  exact Physical.measurement_reduced_multiplicity (by omega) (rawPhase (anglePhase t))
    (rawPhase_star_mul_self _ (anglePhase_norm t)) (componentScale n t) hm j a
    (seed_localX hn t j.val j.isLt) (seed_localY hn t j.val j.isLt)
    (seed_localZ hn t j.val j.isLt)

/-- 全n统一构造主定理：前提只有n≥5。 -/
theorem unified_ejm_family {n : ℕ} (hn : 5 ≤ n) :
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
  refine ⟨measurement_orthonormal (by omega), measurement_reduced hn,
    local_vertices_unit, local_vertices_distinct_dot, localOutcome_fiber_card (by omega),
    radius_image_exact (by omega), radius_continuous n, radius_strict_decreasing n,
    measurement_basepoint_original (by omega), measurement_eq_gate_column n,
    measurement_complete (by omega)⟩

end UnifiedEJM
