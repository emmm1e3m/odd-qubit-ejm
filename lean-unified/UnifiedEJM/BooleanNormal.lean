import UnifiedEJM.BooleanOriginal

/-! 两值实生成元的规范化及四律的逐支精确幅值。 -/
noncomputable section
namespace UnifiedEJM.BooleanLines
open OddEJM Complex

theorem angle_neg_mul (t : ℝ) : anglePhase t * anglePhase (-t)=1 := by
  unfold anglePhase
  rw [←Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  push_cast
  ring

/-- d(0)=1时取补集与反向参数，完整对角相位只差一个整体相位。 -/
theorem originalLine_complement {n : ℕ} (d : Bits n → Bit) (t : ℝ) (z : Bits n) :
    originalLine d t z=anglePhase t*originalLine (fun w=>1+d w) (-t) z := by
  have hu := angle_neg_mul t
  rcases bit_cases (d z) with h|h
  · simp [originalLine,h,ZMod.val_one_eq_one_mod]
    linear_combination -(originalDiagonal z)*hu
  · simp [originalLine,h,CharTwo.add_self_eq_zero,ZMod.val_one_eq_one_mod]
    ring

theorem complement_zero {n : ℕ} (d : Bits n → Bit) (hd : d 0=1) :
    (1+d 0:Bit)=0 := by rw [hd]; decide

/-- 任意两个实斜率a,b经整体相位与参数缩放归入Boolean斜率。 -/
theorem two_rate_phase (a b t : ℝ) (s : Bit) :
    Complex.exp (((t*(a+(b-a)*(s.val:ℝ)):ℝ):ℂ)*I) =
      anglePhase (a*t) * anglePhase ((b-a)*t)^s.val := by
  rcases bit_cases s with rfl|rfl
  · simp [anglePhase,mul_comm]
  · simp only [ZMod.val_one_eq_one_mod,Nat.one_mod,Nat.cast_one,mul_one,pow_one]
    unfold anglePhase
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring

theorem cos_sub_sin_bound (t : ℝ) : |Real.cos t-Real.sin t|≤Real.sqrt 2 := by
  have htrig := Real.sin_sq_add_cos_sq t
  have hsqrt := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp := sq_nonneg (Real.cos t+Real.sin t)
  have ha := sq_abs (Real.cos t-Real.sin t)
  have hn := abs_nonneg (Real.cos t-Real.sin t)
  have hq := Real.sqrt_nonneg 2
  nlinarith

theorem law_fourth_bound (t : ℝ) : |(law 1 1).eval t|≤2*Real.sqrt 2 := by
  have h := cos_sub_sin_bound t
  have he : (law 1 1).eval t=2*(Real.cos t-Real.sin t) := by
    simp [law,Trig.eval,ZMod.val_one_eq_one_mod]
    ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem law_fourth_attains : (law 1 1).eval (-Real.pi/4)=2*Real.sqrt 2 := by
  have hn : -Real.pi/4=-(Real.pi/4) := by ring
  simp [law,Trig.eval,ZMod.val_one_eq_one_mod,hn,Real.sin_pi_div_four,Real.cos_pi_div_four]
  ring

theorem law_enhanced_attains : (law 0 1).eval (-Real.pi/2)=4 := by
  have hn : -Real.pi/2=-(Real.pi/2) := by ring
  simp [law,Trig.eval,ZMod.val_one_eq_one_mod,hn]
  norm_num

theorem law_unenhanced_bound (s : Bit) (t : ℝ) : |(law s 0).eval t|≤2 := by
  have hc := Real.neg_one_le_cos t
  have hc' := Real.cos_le_one t
  rcases bit_cases s with rfl|rfl <;>
    simp [law,Trig.eval,ZMod.val_one_eq_one_mod] <;> rw [abs_le] <;> constructor <;> linarith

/-- 论文Walsh条件的充分性，同样落实到实际I类有限和。 -/
theorem I_law_of_spectrum {n : ℕ} (q : Bits n → Bit) (hq : q 0=1)
    {a b : Bits n} {c : ℂ} (hp : PullI a b c) (s k : Bit)
    (hs : q a=s) (hW : (walsh q (a+b)).re=2*((s.val:ℝ)+k.val-1)) (t : ℝ) :
    (pauliExpectation (raw q (anglePhase t)) a b c).re=(law s k).eval t := by
  rw [raw_I_coeff q hq hp,hs,hW]
  simp only [coeffI,law,Trig.eval]
  ring

/-- 论文Walsh条件的充分性：任意II行与同一个公共分量一致。 -/
theorem II_law_of_spectrum {n : ℕ} (q : Bits n → Bit) (hq : q 0=1)
    {a b : Bits n} {c : ℂ} (hp : PullII a b c) (s k : Bit)
    (hk : q a=k) (hV : (walsh (derivative q a) (a+b)).re=4*((s.val:ℝ)+k.val-1))
    (t : ℝ) :
    (pauliExpectation (raw q (anglePhase t)) a b c).re=(law s k).eval t := by
  rw [raw_II_coeff q hq hp,hk,hV]
  simp only [coeffII,law,Trig.eval]
  ring

end UnifiedEJM.BooleanLines
