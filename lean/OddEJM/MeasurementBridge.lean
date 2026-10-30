import OddEJM.Pauli
import OddEJM.FamilyGeometry
import OddEJM.Labels

namespace OddEJM
open scoped BigOperators

/-- 将实际种子三分量经已证Pauli轨道输运到任意测量列。 -/
theorem measurement_radial_components_from_seed {n : ℕ} (hn : 0 < n) (t : ℝ)
    (label : Bits n) (j : Fin n)
    (hX : localX (seed n t) j = (componentScale n t : ℂ))
    (hY : localY (seed n t) j =
      if j.val = n - 1 then -(componentScale n t : ℂ) else (componentScale n t : ℂ))
    (hZ : localZ (seed n t) j = (componentScale n t : ℂ)) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    localX (measurement n t label) j = (radius n t : ℂ) * (v 0 : ℂ) ∧
    localY (measurement n t label) j = (radius n t : ℂ) * (v 1 : ℂ) ∧
    localZ (measurement n t label) j = (radius n t : ℂ) * (v 2 : ℂ) := by
  dsimp only
  have hv := radius_vertex_components n t (localOrientation j)
    (CircuitPauli.localParity label j.val) (coord label (n - 1))
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  have hv2 := congrFun hv 2
  simp at hv0 hv1 hv2
  have hY' : localY (seed n t) j = ((componentScale n t * localOrientation j : ℝ) : ℂ) := by
    rw [hY]
    by_cases hj : j.val = n - 1 <;> simp [localOrientation, hj]
  change pauliExpectation (seed n t) (unitBit n j.val) 0 1 = _ at hX
  change pauliExpectation (seed n t) (unitBit n j.val) (unitBit n j.val) Complex.I = _ at hY'
  change pauliExpectation (seed n t) 0 (unitBit n j.val) 1 = _ at hZ
  refine ⟨?_, ?_, ?_⟩
  · rw [localX, CircuitPauli.measurement_localX_sign hn t label j.val j.isLt, hX]
    have h := congrArg Complex.ofReal hv0
    simp only [Complex.ofReal_mul] at h
    rw [bitSign_eq_real]
    simpa only [localOutcome, mul_comm] using h.symm
  · rw [localY, CircuitPauli.measurement_localY_sign hn t label j.val j.isLt, hY',
      CircuitPauli.sign_add, bitSign_eq_real, bitSign_eq_real]
    have h := congrArg Complex.ofReal hv1
    simp only [Complex.ofReal_mul] at h
    simp only [localOutcome, Complex.ofReal_mul]
    rw [h]
    ring
  · rw [localZ, CircuitPauli.measurement_localZ_sign hn t label j.val j.isLt, hZ]
    have h := congrArg Complex.ofReal hv2
    simp only [Complex.ofReal_mul] at h
    rw [bitSign_eq_real]
    simpa only [localOutcome, mul_comm] using h.symm

/-- 种子结果一旦接入，这里给出真实n−1指标偏迹的完整四面体公式。 -/
theorem measurement_reduced_from_seed {n : ℕ} (hn : 0 < n) (t : ℝ)
    (label : Bits n) (j : Fin n)
    (hX : localX (seed n t) j = (componentScale n t : ℂ))
    (hY : localY (seed n t) j =
      if j.val = n - 1 then -(componentScale n t : ℂ) else (componentScale n t : ℂ))
    (hZ : localZ (seed n t) j = (componentScale n t : ℂ)) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement n t label) j = (1 / 2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      (radius n t : ℂ) • ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ)) := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components_from_seed hn t label j hX hY hZ
  exact reduced_radial (measurement n t label) j (radius n t : ℂ)
    (fun k => (Geometry.vertex (localOrientation j) (localOutcome j label).1
      (localOutcome j label).2 k : ℂ)) (measurement_normalized hn t label) hx hy hz

end OddEJM
