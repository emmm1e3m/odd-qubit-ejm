import UnifiedEJM.SixFamily

namespace UnifiedEJM.SixFamily
open OddEJM Complex
open UnifiedEJM.SixCertificate
open scoped BigOperators

noncomputable def measurement (α β γ φ : ℝ) (label : Bits 6) : Vec 6 :=
  Physical.measurement (diagonal α β γ φ) label

lemma colourPhases_norm (α β γ : ℝ) : ∀ r : Fin 4, ‖colourPhases α β γ r‖ = 1 := by
  intro r; fin_cases r <;> simp [colourPhases]

theorem diagonal_unit (α β γ φ : ℝ) (z : Bits 6) :
    star (diagonal α β γ φ z) * diagonal α β γ φ z = 1 := by
  have hn : ‖diagonal α β γ φ z‖ = 1 := by
    by_cases hz : z=0
    · subst z
      have hc : colour (0 : Bits 6) = 3 := by decide
      have he : diagonal α β γ φ 0 = -I * anglePhase φ := by
        simp [diagonal, background, deltaZero, hc, colourPhases]
      rw [he]
      simp
    · simp [diagonal, background, deltaZero, hz, norm_mul, norm_pow, colourPhases_norm]
  simpa only [Complex.star_def, hn, one_pow, Complex.ofReal_one] using
    Complex.conj_mul' (diagonal α β γ φ z)

theorem measurement_orthonormal (α β γ φ : ℝ) (k l : Bits 6) :
    inner (measurement α β γ φ k) (measurement α β γ φ l) = if k=l then 1 else 0 :=
  Physical.measurement_orthonormal (by omega) _ (diagonal_unit α β γ φ) k l

/-- 这四颜色模型的指定原点严格等于原始EJM相位。 -/
theorem basepoint (z : Bits 6) : diagonal 0 0 0 (Real.pi/2) z = originalDiagonal z := by
  rw [originalDiagonal_eq_rawPhase_zero (by omega : 1≤6)]
  have ht : anglePhase (Real.pi/2) = I := by
    simp [anglePhase, Complex.exp_ofReal_mul_I]
  have hc : ∀ r : Fin 4, colourPhases 0 0 0 r = 1 := by
    intro r; fin_cases r <;> simp [colourPhases]
  by_cases hz : z=0
  · subst z
    simp [diagonal, background, deltaZero, ht, hc, OddEJM.rawPhase]
  · simp [diagonal, background, deltaZero, ht, hc, hz, OddEJM.rawPhase]

/-- 真实signed等分量条件给全部有序列的真实偏迹与固定局部四面体。 -/
theorem measurement_reduced_of_regular (α β γ φ : ℝ)
    (h : ActualRegular (seed α β γ φ)) (label : Bits 6) (j : Fin 6) :
    let m := total 0 α β γ φ / 64
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement α β γ φ label) j = (1/2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      ((Real.sqrt 3*m : ℝ) : ℂ) •
        ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ)) := by
  have h0 := actual_X (0 : Fin 6) α β γ φ
  change localX (seed α β γ φ) 0 = ((total 0 α β γ φ / 64 : ℝ) : ℂ) at h0
  have hx : localX (seed α β γ φ) j = ((total 0 α β γ φ / 64 : ℝ) : ℂ) :=
    (h j).1.trans h0
  have hz : localZ (seed α β γ φ) j = ((total 0 α β γ φ / 64 : ℝ) : ℂ) :=
    (h j).2.2.trans h0
  have hy0 := (h j).2.1.trans h0
  have hy : localY (seed α β γ φ) j = if j.val=6-1 then
      -((total 0 α β γ φ / 64 : ℝ) : ℂ) else ((total 0 α β γ φ / 64 : ℝ) : ℂ) := by
    by_cases hj : j.val=5
    · simpa [hj] using neg_eq_iff_eq_neg.mp (by simpa [hj] using hy0)
    · simpa [hj] using hy0
  exact Physical.measurement_reduced_from_seed (by omega) _ (diagonal_unit α β γ φ)
    (total 0 α β γ φ / 64) label j hx hy hz

/-- 局部交叉的两支均处于原四面体正方向，未掺入负半径符号分支。 -/
theorem regular_component_positive {α β γ φ : ℝ}
    (hα : |α| ≤ Real.pi/12) (hβ : |β| ≤ Real.pi/12)
    (hγ : |γ| ≤ Real.pi/12) (hφ : |φ-Real.pi/2| ≤ Real.pi/12)
    (hreg : ActualRegular (seed α β γ φ)) : 0 < total 0 α β γ φ / 64 := by
  obtain ⟨haxes, rfl⟩ := (actual_local_crossing hα hβ hγ hφ).mp hreg
  rcases haxes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [total_at_zero]
    simp only [SixLocal.defectI, sub_self, Real.sin_zero, sub_zero,
      Real.sin_pi_div_two_sub]
    have hc : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith [(abs_le.mp hα).1, (abs_le.mp hα).2, Real.pi_pos])
    positivity
  · rw [total_at_zero]
    simp only [SixLocal.defectI, sub_zero, Real.sin_pi_div_two]
    have hs : Real.sin γ < 1 := by
      have hh := Real.strictMonoOn_sin
        (show γ ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from by
          constructor <;> linarith [(abs_le.mp hβ).1, (abs_le.mp hβ).2, Real.pi_pos])
        (show Real.pi/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from by
          constructor <;> linarith [Real.pi_pos])
        (show γ < Real.pi/2 from by linarith [(abs_le.mp hβ).2, Real.pi_pos])
      simpa using hh
    positivity

theorem measurement_complete (α β γ φ : ℝ) (z w : Bits 6) :
    (∑ label, measurement α β γ φ label z * star (measurement α β γ φ label w)) =
      if z=w then 1 else 0 :=
  Physical.measurement_complete (by omega) _ (diagonal_unit α β γ φ) z w

end UnifiedEJM.SixFamily

