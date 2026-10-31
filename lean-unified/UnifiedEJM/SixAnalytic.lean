import UnifiedEJM.SixCertificate
import UnifiedEJM.SixLocal
import OddEJM.LocalExpectation
import Mathlib.Tactic

namespace UnifiedEJM.SixCertificate
open OddEJM Complex
open scoped BigOperators

noncomputable def colourPhases (α β γ : ℝ) : Fin 4 → ℂ :=
  ![1, anglePhase β, anglePhase α, anglePhase γ]

noncomputable def backgroundX (α β γ : ℝ) : ℝ :=
  4 * (-Real.cos α + Real.cos γ - Real.cos (α-β) + Real.cos (β-γ))
noncomputable def backgroundY (α β γ : ℝ) : ℝ :=
  8 * (Real.cos α - Real.cos (β-γ))
noncomputable def backgroundZ (α β γ : ℝ) : ℝ :=
  -8 * (Real.sin β + Real.sin (α-γ))
noncomputable def backgroundTable (p : Fin 18) (α β γ : ℝ) : ℝ :=
  if p=2 ∨ p=3 then backgroundX α β γ else if p=8 then backgroundY α β γ else
    if p=5 ∨ p=15 ∨ p=16 then backgroundZ α β γ else 0

/-- 三个非零背景公式由全部288项颜色系数精确导出。 -/
theorem background_table (p : Fin 18) (α β γ : ℝ) :
    gamma p * colourSum p (colourPhases α β γ) = (backgroundTable p α β γ : ℂ) := by
  rw [colour_sum_eq_coeff]
  fin_cases p <;>
    norm_num [gamma, expectedCoeff, matrixX, matrixY, matrixZ, backgroundTable,
      colourPhases, Fin.sum_univ_succ]
  all_goals
    apply Complex.ext <;>
      simp [anglePhase, Complex.exp_ofReal_mul_I, Complex.mul_re, Complex.mul_im,
        backgroundX, backgroundY, backgroundZ, Real.cos_sub, Real.sin_sub]
  all_goals
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    nlinarith [Real.sin_sq_add_cos_sq β]

/-- 背景表全零等价于论文的三个独立颜色方程。 -/
theorem background_zero_iff (α β γ : ℝ) :
    (∀ p : Fin 18, backgroundTable p α β γ = 0) ↔
      SixLocal.BackgroundEquations α β γ := by
  constructor
  · intro h
    have hx := h 2
    have hy := h 8
    have hz := h 5
    norm_num [backgroundTable, backgroundX, backgroundY, backgroundZ] at hx hy hz
    refine ⟨?_, ?_, ?_⟩
    · have hs : Real.sin (α-γ) = -Real.sin (γ-α) := by
        rw [show α-γ = -(γ-α) by ring, Real.sin_neg]
      rw [hs] at hz
      linarith
    · have hc : Real.cos (β-γ) = Real.cos (γ-β) := by
        rw [show β-γ = -(γ-β) by ring, Real.cos_neg]
      rw [hc] at hy
      linarith
    · linarith
  · rintro ⟨hs, hc, hd⟩ p
    have hc' : Real.cos (β-γ) = Real.cos α := by
      rw [show β-γ = -(γ-β) by ring, Real.cos_neg, hc]
    have hs' : Real.sin (α-γ) = -Real.sin β := by
      rw [show α-γ = -(γ-α) by ring, Real.sin_neg, ← hs]
    unfold backgroundTable
    split_ifs <;> simp [backgroundX, backgroundY, backgroundZ, hc', hs', hd] <;> ring

/-- 直接两参数叠加的两个额外X分量具有精确混合项。 -/
theorem direct_background_x (α β : ℝ) :
    backgroundX α β (α+β) = -8 * Real.sin α * Real.sin β := by
  simp [backgroundX, Real.cos_add, Real.cos_sub]

  ring

theorem direct_background_other (α β : ℝ) :
    backgroundY α β (α+β) = 0 ∧ backgroundZ α β (α+β) = 0 := by
  constructor
  · rw [backgroundY, show β-(α+β) = -α by ring, Real.cos_neg]; ring
  · rw [backgroundZ, show α-(α+β) = -β by ring, Real.sin_neg]; ring

end UnifiedEJM.SixCertificate


