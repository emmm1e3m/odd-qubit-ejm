import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

namespace UnifiedEJM.Curved

noncomputable def k : ℝ := Real.sqrt 2 - 1

def F (x z : ℝ) : ℝ :=
  -x^3*z^2+x^3*z-3*x^2*z^2-3*x^2*z-4*x^2+3*x*z^2+x*z+4*x+z^2-3*z

def Fx (x z : ℝ) : ℝ :=
  -3*x^2*z^2+3*x^2*z-6*x*z^2-6*x*z-8*x+3*z^2+z+4

def Fz (x z : ℝ) : ℝ :=
  -2*x^3*z+x^3-6*x^2*z-3*x^2+6*x*z+x+2*z-3

lemma k_sq : k^2+2*k-1=0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  dsimp [k]
  nlinarith

lemma k_bounds : 2/5 < k ∧ k < 1/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  dsimp [k]
  constructor <;> nlinarith

lemma k_pos : 0 < k := by linarith [k_bounds.1]
lemma k_lt_one : k < 1 := by linarith [k_bounds.2]

lemma hasDerivAt_F_left (x z : ℝ) : HasDerivAt (fun x => F x z) (Fx x z) x := by
  have h1 := ((hasDerivAt_id x).pow 3).neg.mul_const (z^2)
  have h2 := h1.add (((hasDerivAt_id x).pow 3).mul_const z)
  have h3 := h2.sub ((((hasDerivAt_id x).pow 2).const_mul 3).mul_const (z^2))
  have h4 := h3.sub ((((hasDerivAt_id x).pow 2).const_mul 3).mul_const z)
  have h5 := h4.sub (((hasDerivAt_id x).pow 2).const_mul 4)
  have h6 := h5.add (((hasDerivAt_id x).const_mul 3).mul_const (z^2))
  have h7 := h6.add ((hasDerivAt_id x).mul_const z)
  have h8 := h7.add ((hasDerivAt_id x).const_mul 4)
  have h9 := (h8.add_const (z^2)).sub_const (3*z)
  convert h9 using 1 <;> simp only [F, Fx, id_eq, Pi.add_apply, Pi.sub_apply,
    Pi.pow_apply, Pi.neg_apply] <;> ring

lemma hasDerivAt_F_right (x z : ℝ) : HasDerivAt (F x) (Fz x z) z := by
  have h1 := ((hasDerivAt_id z).pow 2).const_mul (-x^3)
  have h2 := h1.add ((hasDerivAt_id z).const_mul (x^3))
  have h3 := h2.sub (((hasDerivAt_id z).pow 2).const_mul (3*x^2))
  have h4 := h3.sub ((hasDerivAt_id z).const_mul (3*x^2))
  have h5 := h4.sub_const (4*x^2)
  have h6 := h5.add (((hasDerivAt_id z).pow 2).const_mul (3*x))
  have h7 := h6.add ((hasDerivAt_id z).const_mul x)
  have h8 := h7.add_const (4*x)
  have h9 := (h8.add ((hasDerivAt_id z).pow 2)).sub ((hasDerivAt_id z).const_mul 3)
  convert h9 using 1
  · ext y
    simp only [F, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
  · simp only [Fz, id_eq]
    ring

lemma Fx_lower {x z : ℝ} (hx : x ∈ Set.Icc 0 k) (hz : z ∈ Set.Icc 0 k) :
    20*k-8 ≤ Fx x z := by
  have hx0 := hx.1
  have hxk := hx.2
  have hz0 := hz.1
  have hzk := hz.2
  have hk0 := k_pos.le
  have hk1 := k_lt_one
  have hz1 : z ≤ 1 := le_trans hz.2 hk1.le
  have hc : 4-12*k < 0 := by linarith [k_bounds.1]
  have hbase : Fx k z = 4-8*k+(4-12*k)*z := by
    unfold Fx
    linear_combination (-3*z^2+3*z) * k_sq
  have hdiff : Fx x z - Fx k z =
      (k-x)*(3*z*((x+k)*(z-1)+2*(z+1))+8) := by unfold Fx; ring
  have hb : 0 ≤ (x+k)*(z-1)+2*(z+1) := by
    have hsum : x+k ≤ 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hz1)
    nlinarith
  have hnn : 0 ≤ 3*z*((x+k)*(z-1)+2*(z+1))+8 := by positivity
  have hcomp : Fx k z ≤ Fx x z := by rw [← sub_nonneg, hdiff]; positivity
  have hlast := mul_le_mul_of_nonpos_left hz.2 hc.le
  rw [hbase] at hcomp
  nlinarith [k_sq]

lemma Fx_pos {x z : ℝ} (hx : x ∈ Set.Icc 0 k) (hz : z ∈ Set.Icc 0 k) :
    0 < Fx x z := by linarith [Fx_lower hx hz, k_bounds.1]

lemma k_cube : k^3 = 5*k-2 := by
  linear_combination k*k_sq-2*k_sq

lemma Fz_upper {x z : ℝ} (hx : x ∈ Set.Icc 0 k) (hz : z ∈ Set.Icc 0 k) :
    Fz x z ≤ 1-4*k := by
  rcases hx with ⟨hx0,hxk⟩
  rcases hz with ⟨hz0,hzk⟩
  have hk0 := k_pos.le
  have hx3 := pow_nonneg hx0 3
  have hx2 := sq_nonneg x
  have hp1 := mul_nonneg hz0 (show 0 ≤ 3*x^2+x^3 by positivity)
  have hp2 := mul_le_mul_of_nonneg_left hxk (show 0 ≤ 3*z by positivity)
  have hp3 := mul_le_mul_of_nonneg_right hzk (show 0 ≤ 1+3*k by positivity)
  have hp4 := pow_le_pow_left₀ hx0 hxk 3
  unfold Fz
  nlinarith [k_sq, k_cube]

lemma Fz_neg {x z : ℝ} (hx : x ∈ Set.Icc 0 k) (hz : z ∈ Set.Icc 0 k) :
    Fz x z < 0 := by linarith [Fz_upper hx hz, k_bounds.1]

lemma F_left_strictMono {z : ℝ} (hz : z ∈ Set.Icc 0 k) :
    StrictMonoOn (fun x => F x z) (Set.Icc 0 k) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold F; fun_prop)
  intro x hx
  rw [(hasDerivAt_F_left x z).deriv]
  exact Fx_pos (interior_subset hx) hz

lemma F_right_strictAnti {x : ℝ} (hx : x ∈ Set.Icc 0 k) :
    StrictAntiOn (F x) (Set.Icc 0 k) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (by unfold F; fun_prop)
  intro z hz
  rw [(hasDerivAt_F_right x z).deriv]
  exact Fz_neg hx (interior_subset hz)

lemma F_diag (x : ℝ) : F x x = -x*(1+x^2)*(x^2+2*x-1) := by unfold F; ring

lemma F_kk : F k k = 0 := by rw [F_diag, k_sq]; ring

lemma F_diag_nonneg {x : ℝ} (hx : x ∈ Set.Icc 0 k) : 0 ≤ F x x := by
  have hx0 := hx.1
  have hxk := hx.2
  have hpow := pow_le_pow_left₀ hx0 hxk 2
  have hpoly : x^2+2*x-1 ≤ 0 := by nlinarith [k_sq]
  rw [F_diag]
  have := mul_nonneg (show 0 ≤ x*(1+x^2) by positivity) (neg_nonneg.mpr hpoly)
  nlinarith

lemma F_top_nonpos {x : ℝ} (hx : x ∈ Set.Icc 0 k) : F x k ≤ 0 := by
  have hm := (F_left_strictMono (show k ∈ Set.Icc 0 k from ⟨k_pos.le,le_rfl⟩)).monotoneOn
  have h := hm hx ⟨k_pos.le,le_rfl⟩ hx.2
  simpa only [F_kk] using h

/-- 每个半角参数都有区间内唯一实根；没有数值求根前提。 -/
lemma existsUnique_root {x : ℝ} (hx : x ∈ Set.Icc 0 k) :
    ∃! z, z ∈ Set.Icc x k ∧ F x z = 0 := by
  obtain ⟨z,hz,hF⟩ := intermediate_value_Icc' hx.2
    (show ContinuousOn (F x) (Set.Icc x k) by unfold F; fun_prop)
    (show 0 ∈ Set.Icc (F x k) (F x x) from ⟨F_top_nonpos hx,F_diag_nonneg hx⟩)
  refine ⟨z,⟨hz,hF⟩,?_⟩
  intro w hw
  exact (F_right_strictAnti hx).injOn ⟨le_trans hx.1 hw.1.1,hw.1.2⟩
    ⟨le_trans hx.1 hz.1,hz.2⟩ (hw.2.trans hF.symm)

def a (x : ℝ) : ℝ := 1+3*x-3*x^2-x^3
def b (x : ℝ) : ℝ := 3-x+3*x^2-x^3
def c (x : ℝ) : ℝ := 4*x*(1-x)
def disc (x : ℝ) : ℝ := (b x)^2-4*a x*c x
noncomputable def root (x : ℝ) : ℝ := 2*c x/(b x+Real.sqrt (disc x))

lemma F_quadratic (x z : ℝ) : F x z = a x*z^2-b x*z+c x := by
  unfold F a b c; ring
lemma Fz_quadratic (x z : ℝ) : Fz x z = 2*a x*z-b x := by
  unfold Fz a b; ring
lemma a_pos {x : ℝ} (hx : x ∈ Set.Icc 0 k) : 0 < a x := by
  have hx0 := hx.1
  have hx1 : x < 1 := lt_of_le_of_lt hx.2 k_lt_one
  have heq : a x = (1-x)*(x^2+4*x+1) := by unfold a; ring
  rw [heq]; positivity
lemma b_pos {x : ℝ} (hx : x ∈ Set.Icc 0 k) : 0 < b x := by
  have hx0 := hx.1
  have hx1 : x < 1 := lt_of_le_of_lt hx.2 k_lt_one
  have heq : b x = 2+(1-x)*(1+x^2)+2*x^2 := by unfold b; ring
  rw [heq]; positivity

/-- 有理化的小根公式在整个闭区间有定义，并等于唯一的区间根。 -/
lemma root_data {x : ℝ} (hx : x ∈ Set.Icc 0 k) :
    0 < disc x ∧ 0 < b x+Real.sqrt (disc x) ∧
    root x ∈ Set.Icc x k ∧ F x (root x) = 0 := by
  obtain ⟨w,⟨hw,hF⟩,_⟩ := existsUnique_root hx
  have hw0 : w ∈ Set.Icc 0 k := ⟨le_trans hx.1 hw.1,hw.2⟩
  have hder := Fz_neg hx hw0
  rw [Fz_quadratic] at hder
  rw [F_quadratic] at hF
  have heq : disc x = (b x-2*a x*w)^2 := by
    unfold disc
    linear_combination -4*a x*hF
  have hgap : 0 < b x-2*a x*w := by linarith
  have hdisc : 0 < disc x := by rw [heq]; exact sq_pos_of_pos hgap
  have hsqrt : Real.sqrt (disc x) = b x-2*a x*w := by
    rw [heq,Real.sqrt_sq (by linarith)]
  have hden : 0 < b x+Real.sqrt (disc x) := by
    have := b_pos hx
    have := Real.sqrt_nonneg (disc x)
    linarith
  have hr : root x = w := by
    unfold root
    apply (div_eq_iff (ne_of_gt hden)).2
    rw [hsqrt]
    nlinarith [hF]
  exact ⟨hdisc,hden,hr.symm ▸ hw,hr.symm ▸ (F_quadratic x w ▸ hF)⟩

lemma root_mem {x : ℝ} (hx : x ∈ Set.Icc 0 k) : root x ∈ Set.Icc x k :=
  (root_data hx).2.2.1
lemma root_eq_zero {x : ℝ} (hx : x ∈ Set.Icc 0 k) : F x (root x) = 0 :=
  (root_data hx).2.2.2
lemma root_mem_full {x : ℝ} (hx : x ∈ Set.Icc 0 k) : root x ∈ Set.Icc 0 k :=
  ⟨le_trans hx.1 (root_mem hx).1,(root_mem hx).2⟩

lemma root_at_zero : root 0 = 0 := by simp [root,c]
lemma root_at_k : root k = k := by
  have hm := root_mem (show k ∈ Set.Icc 0 k from ⟨k_pos.le,le_rfl⟩)
  exact le_antisymm hm.2 hm.1

lemma root_continuous : ContinuousOn root (Set.Icc 0 k) := by
  apply ContinuousOn.div
  · unfold c; fun_prop
  · simp only [b,disc,a,c]; fun_prop
  · intro x hx
    exact ne_of_gt (root_data hx).2.1

lemma root_strictMono : StrictMonoOn root (Set.Icc 0 k) := by
  intro x hx y hy hxy
  have hf : F x (root x) < F y (root x) :=
    F_left_strictMono (root_mem_full hx) hx hy hxy
  have hpos : 0 < F y (root x) := by simpa [root_eq_zero hx] using hf
  by_contra! hle
  have hleF := (F_right_strictAnti hy).antitoneOn (root_mem_full hy) (root_mem_full hx) hle
  rw [root_eq_zero hy] at hleF
  linarith

/-- 半角变量下的共同分量倍率。 -/
noncomputable def value (x z : ℝ) : ℝ :=
  ((1-x^2)*(1-z^2)+4*x*z+2*z*(1+x^2))/((1+x^2)*(1+z^2))
noncomputable def gain (x : ℝ) : ℝ := value x (root x)

lemma value_diff_x (x y z : ℝ) :
    value y z-value x z =
    2*(y-x)*((z-x)*(1+y*z)+(z-y)*(1+x*z))/((1+x^2)*(1+y^2)*(1+z^2)) := by
  unfold value
  field_simp
  <;> ring

lemma value_diff_z (x z w : ℝ) :
    value x w-value x z =
    2*(w-z)*(1+x)*((1+x)*(1-w*z)-(1-x)*(w+z))/
      ((1+x^2)*(1+z^2)*(1+w^2)) := by
  unfold value
  field_simp
  <;> ring

lemma value_mono_x {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    value x z ≤ value y z := by
  rw [← sub_nonneg, value_diff_x]
  have hy : 0 ≤ y := le_trans hx hxy
  have hz : 0 ≤ z := le_trans hy hyz
  have hzx : 0 ≤ z-x := sub_nonneg.mpr (le_trans hxy hyz)
  have hzy : 0 ≤ z-y := sub_nonneg.mpr hyz
  have hyx : 0 ≤ y-x := sub_nonneg.mpr hxy
  positivity

lemma value_strictMono_z {x z w : ℝ} (hx : 0 ≤ x) (hz : z ∈ Set.Icc 0 k)
    (hw : w ∈ Set.Icc 0 k) (hzw : z < w) : value x z < value x w := by
  have hz0 := hz.1
  have hw0 := hw.1
  have hzlt : z < k := lt_of_lt_of_le hzw hw.2
  have hprod := mul_le_mul hz.2 hw.2 hw0 k_pos.le
  have hsmall : 0 < 1-w*z-w-z := by nlinarith [k_sq,hw.2]
  have hbracket : 0 < (1+x)*(1-w*z)-(1-x)*(w+z) := by
    have hid : (1+x)*(1-w*z)-(1-x)*(w+z) =
        (1+x)*(1-w*z-w-z)+2*x*(w+z) := by ring
    rw [hid]; positivity
  rw [← sub_pos,value_diff_z]
  have : 0 < w-z := sub_pos.mpr hzw
  positivity

/-- 不需要对隐式根求导，直接比较两个正有理差分。 -/
lemma gain_strictMono : StrictMonoOn gain (Set.Icc 0 k) := by
  intro x hx y hy hxy
  have hroot := root_strictMono hx hy hxy
  have hv1 := value_strictMono_z hx.1 (root_mem_full hx) (root_mem_full hy) hroot
  have hv2 := value_mono_x hx.1 hxy.le (root_mem hy).1
  exact lt_of_lt_of_le hv1 hv2

lemma gain_continuous : ContinuousOn gain (Set.Icc 0 k) := by
  unfold gain value
  have hc := root_continuous
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    positivity

lemma gain_zero : gain 0 = 1 := by simp [gain,root_at_zero,value]

lemma gain_k : gain k = 1+1/Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  rw [gain,root_at_k]
  unfold value k
  field_simp
  nlinarith

lemma gain_image : gain '' Set.Icc 0 k = Set.Icc 1 (1+1/Real.sqrt 2) := by
  simpa only [gain_zero,gain_k] using
    ContinuousOn.image_Icc_of_monotoneOn k_pos.le gain_continuous gain_strictMono.monotoneOn

lemma sin_two_arctan (x : ℝ) : Real.sin (2*Real.arctan x) = 2*x/(1+x^2) := by
  rw [Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
  calc
    2 * (x / Real.sqrt (1+x^2)) * (1 / Real.sqrt (1+x^2)) =
        2*x/(Real.sqrt (1+x^2))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]

lemma cos_two_arctan (x : ℝ) : Real.cos (2*Real.arctan x) = (1-x^2)/(1+x^2) := by
  rw [Real.cos_two_mul,Real.cos_sq_arctan]
  field_simp
  <;> ring

lemma value_trig (x z : ℝ) : value x z =
    Real.cos (2*Real.arctan x-2*Real.arctan z)+Real.sin (2*Real.arctan z) := by
  rw [Real.cos_sub,sin_two_arctan,sin_two_arctan,cos_two_arctan,cos_two_arctan]
  unfold value
  field_simp
  <;> ring

lemma atan_k : 2*Real.arctan k = Real.pi/4 := by
  rw [Real.two_mul_arctan (by linarith [k_pos]) k_lt_one]
  have hden : 1-k^2 = 2*k := by linarith [k_sq]
  rw [hden,div_self (mul_ne_zero (by norm_num) (ne_of_gt k_pos)),Real.arctan_one]

noncomputable def angle (x : ℝ) : ℝ := 2*Real.arctan x
noncomputable def delta (x : ℝ) : ℝ := -2*Real.arctan (root x)

lemma angle_zero : angle 0 = 0 := by simp [angle]
lemma angle_k : angle k = Real.pi/4 := atan_k
lemma delta_zero : delta 0 = 0 := by simp [delta,root_at_zero]
lemma delta_k : delta k = -(Real.pi/4) := by
  rw [delta,root_at_k]
  linarith [atan_k]

lemma angle_strictMono : StrictMono angle := by
  intro x y hxy
  have h := Real.arctan_strictMono hxy
  dsimp [angle]
  linarith
lemma angle_continuous : Continuous angle := by unfold angle; fun_prop
lemma angle_image : angle '' Set.Icc 0 k = Set.Icc 0 (Real.pi/4) := by
  simpa only [angle_zero,angle_k] using
    ContinuousOn.image_Icc_of_monotoneOn k_pos.le angle_continuous.continuousOn
      (angle_strictMono.monotone.monotoneOn _)

lemma gain_trig (x : ℝ) : gain x =
    Real.cos (angle x+delta x)-Real.sin (delta x) := by
  rw [gain,value_trig]
  simp only [angle,delta,neg_mul,Real.sin_neg,sub_neg_eq_add]
  congr 2 <;> ring

/-- 精确方程确保全部期望一致，尚未调用物理桥。 -/
lemma H_eq_T {x : ℝ} (hx : x ∈ Set.Icc 0 k) :
    Real.cos (angle x)+2*Real.sin (delta x)*Real.cos (angle x)+
      4*Real.sin (angle x)*Real.cos (angle x) =
    Real.cos (angle x+delta x)-Real.sin (delta x) := by
  have hF := root_eq_zero hx
  have hxden : 1+x^2 ≠ 0 := by positivity
  have hzden : 1+(root x)^2 ≠ 0 := by positivity
  rw [← gain_trig,gain]
  simp only [angle,delta,neg_mul,Real.sin_neg,sin_two_arctan,cos_two_arctan,value]
  field_simp
  unfold F at hF
  linear_combination 2*(x+1)*hF

noncomputable def A (u : ℝ) : ℝ := Real.cos u*(1+2*Real.sin u)
noncomputable def B (u : ℝ) : ℝ := 2*Real.cos u+Real.sin u+1
noncomputable def C (u : ℝ) : ℝ := 2*Real.sin u*Real.cos u
noncomputable def paperDisc (u : ℝ) : ℝ := (B u)^2-4*A u*C u
noncomputable def paperRoot (u : ℝ) : ℝ := 2*C u/(B u+Real.sqrt (paperDisc u))
noncomputable def paperDelta (u : ℝ) : ℝ := -2*Real.arctan (paperRoot u)
noncomputable def paperGain (u : ℝ) : ℝ := Real.cos (u+paperDelta u)-Real.sin (paperDelta u)
noncomputable def scale (x : ℝ) : ℝ := (x+1)/(1+x^2)^2

lemma coeff_angle (x : ℝ) : A (angle x)=scale x*a x ∧
    B (angle x)=scale x*b x ∧ C (angle x)=scale x*c x := by
  simp only [A,B,C,angle,sin_two_arctan,cos_two_arctan,scale,a,b,c]
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

lemma paperDisc_angle (x : ℝ) : paperDisc (angle x)=(scale x)^2*disc x := by
  rcases coeff_angle x with ⟨ha,hb,hc⟩
  rw [paperDisc,ha,hb,hc,disc]
  ring

lemma scale_pos {x : ℝ} (hx : x ∈ Set.Icc 0 k) : 0 < scale x := by
  have hx0 := hx.1
  unfold scale
  positivity

lemma paperRoot_angle {x : ℝ} (hx : x ∈ Set.Icc 0 k) : paperRoot (angle x)=root x := by
  rcases coeff_angle x with ⟨ha,hb,hc⟩
  have hscale := scale_pos hx
  have hden := (root_data hx).2.1
  rw [paperRoot,hc,hb,paperDisc_angle,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hscale.le]
  unfold root
  field_simp
  <;> ring

lemma paperDelta_angle {x : ℝ} (hx : x ∈ Set.Icc 0 k) : paperDelta (angle x)=delta x := by
  rw [paperDelta,paperRoot_angle hx]
  rfl

lemma paperGain_angle {x : ℝ} (hx : x ∈ Set.Icc 0 k) : paperGain (angle x)=gain x := by
  rw [paperGain,paperDelta_angle hx,← gain_trig]

lemma paper_data {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.pi/4)) :
    0 < paperDisc u ∧ 0 < B u+Real.sqrt (paperDisc u) := by
  rw [← angle_image] at hu
  obtain ⟨x,hx,rfl⟩ := hu
  have hscale := scale_pos hx
  have hdisc := (root_data hx).1
  have hb := b_pos hx
  constructor
  · rw [paperDisc_angle]; positivity
  · rw [(coeff_angle x).2.1]
    have hs := Real.sqrt_nonneg (paperDisc (angle x))
    positivity

lemma paperDelta_continuous : ContinuousOn paperDelta (Set.Icc 0 (Real.pi/4)) := by
  have hr : ContinuousOn paperRoot (Set.Icc 0 (Real.pi/4)) := by
    unfold paperRoot
    apply ContinuousOn.div
    · unfold C; fun_prop
    · simp only [paperDisc,A,B,C]; fun_prop
    · intro u hu
      exact ne_of_gt (paper_data hu).2
  unfold paperDelta
  fun_prop

lemma paperGain_continuous : ContinuousOn paperGain (Set.Icc 0 (Real.pi/4)) := by
  have hd := paperDelta_continuous
  unfold paperGain
  fun_prop

lemma paperGain_strictMono : StrictMonoOn paperGain (Set.Icc 0 (Real.pi/4)) := by
  intro u hu v hv huv
  rw [← angle_image] at hu hv
  obtain ⟨x,hx,rfl⟩ := hu
  obtain ⟨y,hy,rfl⟩ := hv
  rw [paperGain_angle hx,paperGain_angle hy]
  exact gain_strictMono hx hy (angle_strictMono.lt_iff_lt.mp huv)

lemma paperDelta_zero : paperDelta 0=0 := by
  have h := paperDelta_angle (show (0:ℝ) ∈ Set.Icc 0 k from ⟨le_rfl,k_pos.le⟩)
  simpa only [angle_zero,delta_zero] using h
lemma paperDelta_endpoint : paperDelta (Real.pi/4)=-(Real.pi/4) := by
  have h := paperDelta_angle (show k ∈ Set.Icc 0 k from ⟨k_pos.le,le_rfl⟩)
  simpa only [angle_k,delta_k] using h
lemma paperGain_zero : paperGain 0=1 := by simp [paperGain,paperDelta_zero]
lemma paperGain_endpoint : paperGain (Real.pi/4)=1+1/Real.sqrt 2 := by
  have h := paperGain_angle (show k ∈ Set.Icc 0 k from ⟨k_pos.le,le_rfl⟩)
  simpa only [angle_k,gain_k] using h
lemma paperGain_image : paperGain '' Set.Icc 0 (Real.pi/4) = Set.Icc 1 (1+1/Real.sqrt 2) := by
  simpa only [paperGain_zero,paperGain_endpoint] using
    ContinuousOn.image_Icc_of_monotoneOn (show (0:ℝ) ≤ Real.pi/4 by positivity)
      paperGain_continuous paperGain_strictMono.monotoneOn

lemma paper_H_eq_T {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.pi/4)) :
    Real.cos u+2*Real.sin (paperDelta u)*Real.cos u+4*Real.sin u*Real.cos u = paperGain u := by
  rw [← angle_image] at hu
  obtain ⟨x,hx,rfl⟩ := hu
  rw [paperGain,paperDelta_angle hx]
  exact H_eq_T hx

lemma paperDelta_bounds {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.pi/4)) :
    -(Real.pi/4) ≤ paperDelta u ∧ paperDelta u ≤ -u := by
  rw [← angle_image] at hu
  obtain ⟨x,hx,rfl⟩ := hu
  rw [paperDelta_angle hx]
  have hlo := Real.arctan_mono (root_mem hx).1
  have hhi := Real.arctan_mono (root_mem hx).2
  dsimp [angle,delta]
  constructor <;> linarith [atan_k]

lemma paperRoot_quadratic {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.pi/4)) :
    A u*(paperRoot u)^2-B u*paperRoot u+C u=0 := by
  rw [← angle_image] at hu
  obtain ⟨x,hx,rfl⟩ := hu
  rcases coeff_angle x with ⟨ha,hb,hc⟩
  rw [ha,hb,hc,paperRoot_angle hx]
  have h := root_eq_zero hx
  rw [F_quadratic] at h
  linear_combination scale x*h

lemma delta_half_tan (u : ℝ) : Real.tan (paperDelta u/2) = -paperRoot u := by
  have heq : paperDelta u/2 = -Real.arctan (paperRoot u) := by unfold paperDelta; ring
  rw [heq,Real.tan_neg,Real.tan_arctan]

lemma paperDelta_equation {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.pi/4)) :
    let y := Real.tan (paperDelta u/2)
    A u*y^2+B u*y+C u=0 := by
  simp only [delta_half_tan]
  nlinarith [paperRoot_quadratic hu]

noncomputable def radius (u : ℝ) : ℝ := Real.sqrt 3/8*paperGain u

lemma radius_continuous : ContinuousOn radius (Set.Icc 0 (Real.pi/4)) := by
  have h := paperGain_continuous
  unfold radius
  fun_prop

lemma radius_strictMono : StrictMonoOn radius (Set.Icc 0 (Real.pi/4)) := by
  intro u hu v hv huv
  have h := paperGain_strictMono hu hv huv
  exact mul_lt_mul_of_pos_left h (by positivity)

lemma radius_zero : radius 0=Real.sqrt 3/8 := by simp [radius,paperGain_zero]
lemma radius_endpoint : radius (Real.pi/4)=(1+1/Real.sqrt 2)*(Real.sqrt 3/8) := by
  rw [radius,paperGain_endpoint,mul_comm]

/-- 论文给定闭区间的半径像，两个端点均实际达到。 -/
lemma radius_image : radius '' Set.Icc 0 (Real.pi/4) =
    Set.Icc (Real.sqrt 3/8) ((1+1/Real.sqrt 2)*(Real.sqrt 3/8)) := by
  simpa only [radius_zero,radius_endpoint] using
    ContinuousOn.image_Icc_of_monotoneOn (show (0:ℝ) ≤ Real.pi/4 by positivity)
      radius_continuous radius_strictMono.monotoneOn

lemma radius_positive {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.pi/4)) : 0 < radius u := by
  have h := radius_strictMono.monotoneOn
    (show (0:ℝ) ∈ Set.Icc 0 (Real.pi/4) from ⟨le_rfl,by positivity⟩) hu hu.1
  rw [radius_zero] at h
  exact lt_of_lt_of_le (by positivity) h

end UnifiedEJM.Curved


