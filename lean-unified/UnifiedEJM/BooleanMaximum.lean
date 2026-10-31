import UnifiedEJM.BooleanNormal
import UnifiedEJM.BooleanDelta
import UnifiedEJM.LowBooleanPhysical
import UnifiedEJM.Seed

/-! 完整Boolean相位直线模型的精确最大半径及实际达到性。 -/
noncomputable section
namespace UnifiedEJM.BooleanLines
open OddEJM Complex
open UnifiedEJM.LowBooleanPhysical
open scoped BigOperators

/-- 允许模型中的共同半径，零半径按收缩四面体解释。 -/
def modelRadius {n : ℕ} (q : Bits n → Bit) (t : ℝ) : ℝ :=
  Real.sqrt 3*|seedX q t 0|

def radiusValues (n : ℕ) : Set ℝ :=
  {r | ∃ q : Bits n → Bit, q 0=1 ∧ LocallyRegular q ∧ ∃ t : ℝ, r=modelRadius q t}

def modelMaximum (n : ℕ) : ℝ :=
  if n≤4 then Real.sqrt 3/(2:ℝ)^(n-1) else 2*(Real.sqrt 3/(2:ℝ)^(n-1))

/-- 背景q与d(0)=0的原模型逐输入双射。 -/
def supportOfQ {n : ℕ} (q : Bits n → Bit) (z : Bits n) : Bit :=
  if z=0 then 0 else q z

@[simp] theorem supportOfQ_zero {n : ℕ} (q : Bits n → Bit) : supportOfQ q 0=0 := by
  simp [supportOfQ]

theorem qOfSupport_supportOfQ {n : ℕ} (q : Bits n → Bit) (hq : q 0=1) :
    qOfSupport (supportOfQ q)=q := by
  funext z
  by_cases hz : z=0
  · subst z; simp [hq]
  · simp [qOfSupport,supportOfQ,hz]

theorem supportOfQ_qOfSupport {n : ℕ} (d : Bits n → Bit) (hd : d 0=0) :
    supportOfQ (qOfSupport d)=d := by
  funext z
  by_cases hz : z=0
  · subst z; simp [hd]
  · simp [qOfSupport,supportOfQ,hz]

theorem seedX_at_zero {n : ℕ} (hn : 2≤n) (q : Bits n → Bit) (hq : q 0=1) :
    seedX q 0 0=2/(2:ℝ)^n := by
  rw [seedX_first hn q hq]
  simp [coeffI,Trig.eval]
  ring

theorem modelRadius_at_zero {n : ℕ} (hn : 2≤n) (q : Bits n → Bit) (hq : q 0=1) :
    modelRadius q 0=Real.sqrt 3/(2:ℝ)^(n-1) := by
  rw [modelRadius,seedX_at_zero hn q hq,abs_of_pos (by positivity)]
  have hp : (2:ℝ)^n=(2:ℝ)^(n-1)*2 := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤n)]
  rw [hp]
  ring

theorem all_dimensions_upper_bound {n : ℕ} (hn : 2≤n)
    (q : Bits n → Bit) (hq : q 0=1) (hr : LocallyRegular q) (t : ℝ) :
    modelRadius q t≤modelMaximum n := by
  by_cases hsmall : n≤4
  · interval_cases n
    · calc
        modelRadius q t ≤ Real.sqrt 3*(1/2) :=
          mul_le_mul_of_nonneg_left (actual_two_bound q hq hr t) (Real.sqrt_nonneg 3)
        _ = modelMaximum 2 := by norm_num [modelMaximum]; ring
    · have hx := actual_three_constant q hq hr t
      simp [modelRadius,modelMaximum,hx]
      ring_nf
      exact le_rfl
    · calc
        modelRadius q t ≤ Real.sqrt 3*(1/8) :=
          mul_le_mul_of_nonneg_left (actual_four_bound q hq hr t) (Real.sqrt_nonneg 3)
        _ = modelMaximum 4 := by norm_num [modelMaximum]; ring
  · have hn5 : 5≤n := by omega
    have hreg : ∀ᶠ u in nhds (0:ℝ), seedX q u 0^2=seedX q u 1^2 := by
      filter_upwards [hr] with u hu
      exact (hu 1 (by omega)).1.symm
    have hb := mul_le_mul_of_nonneg_left (actual_seed_bound (by omega) q hq hreg t)
      (Real.sqrt_nonneg 3)
    have hp : (2:ℝ)^n=(2:ℝ)^(n-1)*2 := by
      rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤n)]
    calc
      modelRadius q t ≤ Real.sqrt 3*(4/(2:ℝ)^n) := hb
      _ = modelMaximum n := by
        rw [modelMaximum,ite_eq_right hsmall,hp]
        ring

theorem unified_seed_eq (n : ℕ) (t : ℝ) :
    seed (@UnifiedEJM.q n) t=UnifiedEJM.seed n t := rfl

theorem unified_locally_regular {n : ℕ} (hn : 5≤n) : LocallyRegular (@UnifiedEJM.q n) := by
  apply Filter.Eventually.of_forall
  intro t j hj
  simp only [seedX,seedY,seedZ,unified_seed_eq]
  rw [UnifiedEJM.seed_localX hn t j hj,UnifiedEJM.seed_localX hn t 0 (by omega),
    UnifiedEJM.seed_localY hn t j hj,UnifiedEJM.seed_localZ hn t j hj]
  split_ifs <;> simp

theorem unified_maximum_attained {n : ℕ} (hn : 5≤n) :
    modelRadius (@UnifiedEJM.q n) (-(Real.pi/2))=modelMaximum n := by
  have hx : seedX (@UnifiedEJM.q n) (-(Real.pi/2)) 0=
      componentScale n (-(Real.pi/2)) := by
    simp only [seedX,unified_seed_eq,UnifiedEJM.seed_localX hn _ 0 (by omega),Complex.ofReal_re]
  rw [modelRadius,hx]
  have hnonneg : 0≤componentScale n (-(Real.pi/2)) := by
    simp only [componentScale,Real.sin_neg,Real.sin_pi_div_two]
    positivity
  rw [abs_of_nonneg hnonneg]
  simp only [modelMaximum,ite_eq_right (show ¬n≤4 by omega),componentScale,
    Real.sin_neg,Real.sin_pi_div_two]
  ring

/-- 两段最优值都是最大值，低维在基点达到，高维由新四特征核达到。 -/
theorem boolean_model_exact_maximum {n : ℕ} (hn : 2≤n) :
    IsGreatest (radiusValues n) (modelMaximum n) := by
  constructor
  · by_cases hsmall : n≤4
    · refine ⟨qDelta,qDelta_zero n,?_,0,?_⟩
      · exact delta_locally_regular hn
      · rw [modelRadius_at_zero hn _ (qDelta_zero n)]
        simp [modelMaximum,hsmall]
    · exact ⟨UnifiedEJM.q,UnifiedEJM.q_zero n,unified_locally_regular (by omega),
        -(Real.pi/2),(unified_maximum_attained (by omega)).symm⟩
  · intro r hr
    obtain ⟨q,hq,hreg,t,rfl⟩ := hr
    exact all_dimensions_upper_bound hn q hq hreg t

end UnifiedEJM.BooleanLines
