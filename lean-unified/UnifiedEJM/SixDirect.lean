import UnifiedEJM.SixMeasurement
import UnifiedEJM.EvenAxes

namespace UnifiedEJM.SixFamily
open OddEJM Complex
open UnifiedEJM.SixCertificate UnifiedEJM.EvenWalsh
open scoped BigOperators

lemma angle_add (α β : ℝ) : anglePhase (α+β) = anglePhase α * anglePhase β := by
  simp only [anglePhase, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem colour_digits : ∀ z : Bits 6,
    (colour z).val = 2 * (qA z).val + (UnifiedEJM.q z).val := by decide

/-- 四颜色框架严格包含原直接两相位叠加，不只包含其半径。 -/
theorem colour_direct_phase (α β : ℝ) (z : Bits 6) :
    colourPhases α β (α+β) (colour z) =
      anglePhase α ^ (qA z).val * anglePhase β ^ (UnifiedEJM.q z).val := by
  have hc := colour_digits z
  rcases bit_cases (qA z) with ha | ha <;>
    rcases bit_cases (UnifiedEJM.q z) with hb | hb
  all_goals
    simp only [ha, hb, ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.one_mod] at hc ⊢
    generalize hr : colour z = r at hc ⊢
    fin_cases r <;> norm_num at hc <;> norm_num [colourPhases, angle_add]

theorem direct_diagonal (α β : ℝ) :
    diagonal α β (α+β) (Real.pi/2) = EvenFamily.diagonal 6 α β := by
  funext z
  rw [EvenFamily.diagonal, EvenRaw.raw_eq_corrected qA UnifiedEJM.q _ _
    (qA_zero 6) (q_zero 6)]
  unfold diagonal EvenRaw.corrected background EvenRaw.background
  rw [colour_direct_phase, angle_add]
  have ht : anglePhase (Real.pi/2) = I := by simp [anglePhase, Complex.exp_ofReal_mul_I]
  rw [ht]
  ring

theorem direct_seed (α β : ℝ) :
    seed α β (α+β) (Real.pi/2) = EvenFamily.seed 6 α β := by
  unfold seed EvenFamily.seed
  rw [direct_diagonal]

/-- 直接叠加的全实参数障碍，从实际物理种子而来。 -/
theorem direct_regular_iff (α β : ℝ) :
    ActualRegular (EvenFamily.seed 6 α β) ↔ Real.sin α * Real.sin β = 0 := by
  rw [← direct_seed, actual_regular_iff_table, table_regular_iff_equations]
  simp only [SixLocal.BackgroundEquations, add_sub_cancel_left, add_sub_cancel_right,
    SixLocal.defectI, SixLocal.defectII, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub, and_true, true_and]
  rw [Real.cos_add, Real.cos_sub]
  constructor <;> intro h <;> nlinarith

end UnifiedEJM.SixFamily


