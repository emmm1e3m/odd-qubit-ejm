import UnifiedEJM.Main
import UnifiedEJM.Entropy

namespace UnifiedEJM
open OddEJM

/-- 全n新版测量的实际单比特von Neumann熵；唯一维数前提为n≥5。 -/
theorem measurement_vonNeumann_entropy {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    Entropy.vonNeumann (reduced (measurement n t label) j)
      (Entropy.reduced_isHermitian _ j) = Entropy.binary ((1+radius n t)/2) := by
  exact Entropy.measurement_entropy (by omega) (rawPhase (anglePhase t))
    (rawPhase_star_mul_self _ (anglePhase_norm t)) (componentScale n t) label j
    (seed_localX hn t j.val j.isLt) (seed_localY hn t j.val j.isLt)
    (seed_localZ hn t j.val j.isLt)

/-- 完整实际谱而不只是特征行列式的两个零点；重根情形也包含在内。 -/
theorem measurement_actual_spectrum {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    let hA := Entropy.reduced_isHermitian (measurement n t label) j
    (hA.eigenvalues 0 = (1+radius n t)/2 ∧ hA.eigenvalues 1 = (1-radius n t)/2) ∨
    (hA.eigenvalues 0 = (1-radius n t)/2 ∧ hA.eigenvalues 1 = (1+radius n t)/2) := by
  obtain ⟨hx,hy,hz⟩ := Physical.measurement_radial_components_from_seed (by omega)
    (rawPhase (anglePhase t)) (componentScale n t) label j
    (seed_localX hn t j.val j.isLt) (seed_localY hn t j.val j.isLt)
    (seed_localZ hn t j.val j.isLt)
  have hv := local_vertices_unit j (localOutcome j label).1 (localOutcome j label).2
  simp only [Geometry.dot3, Fin.sum_univ_three, ← pow_two] at hv
  exact Entropy.reduced_eigenvalues_radial (measurement n t label) j (radius n t)
    (Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2)
    (by simpa using measurement_orthonormal (by omega) t label label) hx hy hz hv

/-- 在论文区间内半径严格下降，实际各单比特熵严格上升。 -/
theorem measurement_entropy_strictMonoOn {n : ℕ} (hn : 5 ≤ n)
    (label : Bits n) (j : Fin n) :
    StrictMonoOn (fun t : ℝ => Entropy.vonNeumann (reduced (measurement n t label) j)
      (Entropy.reduced_isHermitian _ j)) Geometry.parameterInterval := by
  intro a ha b hb hab
  dsimp only
  rw [measurement_vonNeumann_entropy hn, measurement_vonNeumann_entropy hn]
  exact Entropy.entropy_strictAntiOn_radius (radius_bounds hn b) (radius_bounds hn a)
    (radius_strict_decreasing n ha hb hab)

/-- 收缩终点实际单比特熵为一比特。 -/
theorem measurement_entropy_at_right {n : ℕ} (hn : 5 ≤ n)
    (label : Bits n) (j : Fin n) :
    Entropy.vonNeumann (reduced (measurement n (Real.pi/2) label) j)
      (Entropy.reduced_isHermitian _ j) = 1 := by
  rw [measurement_vonNeumann_entropy hn, radius_eq_geometry, Geometry.radius_at_right]
  exact Entropy.entropy_zero_radius

theorem measurement_entropy_bounds {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    Entropy.vonNeumann (reduced (measurement n t label) j)
      (Entropy.reduced_isHermitian _ j) ∈ Set.Icc (0:ℝ) 1 := by
  rw [measurement_vonNeumann_entropy hn]
  exact Entropy.entropy_radius_bounds _ (radius_bounds hn t)

end UnifiedEJM
