import UnifiedEJM.EvenGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace UnifiedEJM.SixLocal

/-- 六比特四颜色背景的三个独立方程。 -/
def BackgroundEquations (α β γ : ℝ) : Prop :=
  Real.sin β = Real.sin (γ - α) ∧
  Real.cos α = Real.cos (γ - β) ∧
  Real.cos γ = Real.cos (α - β)

noncomputable def defectI (α γ φ : ℝ) : ℝ :=
  Real.sin (φ - α) - Real.sin (γ - α)
noncomputable def defectII (β γ φ : ℝ) : ℝ :=
  Real.cos (γ - β) - Real.cos (φ - β)
noncomputable def gap (α β γ φ : ℝ) : ℝ := defectI α γ φ - defectII β γ φ

lemma small_angle_sin_zero {x : ℝ} (hx : |x| ≤ Real.pi / 12) :
    Real.sin x = 0 ↔ x = 0 := by
  apply Real.sin_eq_zero_iff_of_lt_of_lt <;> linarith [(abs_le.mp hx).1,
    (abs_le.mp hx).2, Real.pi_pos]

/-- 小邻域内，正弦单射先迫使γ=α+β，再由余弦方程分离两轴。 -/
theorem background_local_iff {α β γ : ℝ}
    (hα : |α| ≤ Real.pi / 12) (hβ : |β| ≤ Real.pi / 12)
    (hγ : |γ| ≤ Real.pi / 12) :
    BackgroundEquations α β γ ↔
      (β = 0 ∧ γ = α) ∨ (α = 0 ∧ γ = β) := by
  constructor
  · rintro ⟨hs, hc, hd⟩
    have hbmem : β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [(abs_le.mp hβ).1, (abs_le.mp hβ).2, Real.pi_pos]
    have hgmem : γ - α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [(abs_le.mp hγ).1, (abs_le.mp hγ).2,
        (abs_le.mp hα).1, (abs_le.mp hα).2, Real.pi_pos]
    have hsum : γ = α + β := by linarith [Real.injOn_sin hbmem hgmem hs]
    rw [hsum, Real.cos_add, Real.cos_sub] at hd
    have hprod : Real.sin α * Real.sin β = 0 := by linarith
    rcases mul_eq_zero.mp hprod with ha | hb
    · have ha0 := (small_angle_sin_zero hα).mp ha
      right; exact ⟨ha0, by linarith⟩
    · have hb0 := (small_angle_sin_zero hβ).mp hb
      left; exact ⟨hb0, by linarith⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [BackgroundEquations, Real.cos_neg]

lemma gap_derivative (α β γ φ : ℝ) :
    HasDerivAt (gap α β γ) (Real.cos (φ - α) - Real.sin (φ - β)) φ := by
  have hs := ((hasDerivAt_id φ).sub_const α).sin
  have hc := ((hasDerivAt_id φ).sub_const β).cos
  convert (hs.sub_const (Real.sin (γ - α))).sub
    ((hasDerivAt_const φ (Real.cos (γ - β))).sub hc) using 1 <;>
    first | rfl | (funext x; rfl) | simp [gap, defectI, defectII]

/-- 在一个明确邻域上对独立零点相位严格单调，避免隐含相位分支。 -/
theorem gap_strictAnti {α β : ℝ} (γ : ℝ)
    (hα : |α| ≤ Real.pi / 12) (hβ : |β| ≤ Real.pi / 12) :
    StrictAntiOn (gap α β γ)
      (Set.Icc (Real.pi / 2 - Real.pi / 12) (Real.pi / 2 + Real.pi / 12)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (show Continuous (gap α β γ) from by
      unfold gap defectI defectII; fun_prop).continuousOn
  · intro φ hφ
    have hm := interior_subset hφ
    rcases hm with ⟨hl, hu⟩
    rw [(gap_derivative α β γ φ).deriv]
    have hδa : |φ - Real.pi / 2 - α| ≤ Real.pi / 6 := by
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp hα).1, (abs_le.mp hα).2]
    have hδb : |φ - Real.pi / 2 - β| ≤ Real.pi / 6 := by
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp hβ).1, (abs_le.mp hβ).2]
    have hsin : -(1 / 2 : ℝ) ≤ Real.sin (φ - Real.pi / 2 - α) := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi / 2) ≤ -(Real.pi / 6) by linarith [Real.pi_pos])
        (show φ - Real.pi / 2 - α ≤ Real.pi / 2 by
          linarith [(abs_le.mp hδa).2, Real.pi_pos])
        (abs_le.mp hδa).1
      simpa [Real.sin_neg, Real.sin_pi_div_six] using h
    have hcos : (1 / 2 : ℝ) < Real.cos (φ - Real.pi / 2 - β) := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi
        (abs_nonneg (φ - Real.pi / 2 - β))
        (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos])
        (show |φ - Real.pi / 2 - β| < Real.pi / 3 by linarith [Real.pi_pos])
      simpa [Real.cos_pi_div_three, Real.cos_abs] using h
    have ha : Real.cos (φ - α) = -Real.sin (φ - Real.pi / 2 - α) := by
      rw [show φ - α = Real.pi / 2 + (φ - Real.pi / 2 - α) by ring,
        Real.cos_add]
      simp
    have hb : Real.sin (φ - β) = Real.cos (φ - Real.pi / 2 - β) := by
      rw [show φ - β = Real.pi / 2 + (φ - Real.pi / 2 - β) by ring,
        Real.sin_add]
      simp
    rw [ha, hb]
    linarith

lemma gap_base_on_axes {α β γ : ℝ}
    (h : (β = 0 ∧ γ = α) ∨ (α = 0 ∧ γ = β)) :
    gap α β γ (Real.pi / 2) = 0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [gap, defectI, defectII, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

/-- 四颜色与独立零点相位的方程在显式邻域内恰有两条交叉支。 -/
theorem local_crossing_iff {α β γ φ : ℝ}
    (hα : |α| ≤ Real.pi / 12) (hβ : |β| ≤ Real.pi / 12)
    (hγ : |γ| ≤ Real.pi / 12) (hφ : |φ - Real.pi / 2| ≤ Real.pi / 12) :
    (BackgroundEquations α β γ ∧ defectI α γ φ = defectII β γ φ) ↔
      ((β = 0 ∧ γ = α) ∨ (α = 0 ∧ γ = β)) ∧ φ = Real.pi / 2 := by
  constructor
  · rintro ⟨hbg, hdef⟩
    have hax := (background_local_iff hα hβ hγ).mp hbg
    refine ⟨hax, ?_⟩
    apply (gap_strictAnti γ hα hβ).injOn
    · constructor <;> linarith [(abs_le.mp hφ).1, (abs_le.mp hφ).2]
    · constructor <;> linarith [Real.pi_pos]
    · rw [gap_base_on_axes hax]
      exact sub_eq_zero.mpr hdef
  · rintro ⟨hax, rfl⟩
    exact ⟨(background_local_iff hα hβ hγ).mpr hax,
      sub_eq_zero.mp (gap_base_on_axes hax)⟩

/-- 直接叠加的混合项为零在同一邻域内等价于两参数轴。 -/
theorem direct_crossing_iff {α β : ℝ}
    (hα : |α| ≤ Real.pi / 12) (hβ : |β| ≤ Real.pi / 12) :
    Real.sin α * Real.sin β = 0 ↔ α = 0 ∨ β = 0 := by
  rw [mul_eq_zero, small_angle_sin_zero hα, small_angle_sin_zero hβ]

end UnifiedEJM.SixLocal

