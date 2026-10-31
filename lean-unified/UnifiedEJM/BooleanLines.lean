import OddEJM.LocalExpectation
import OddEJM.WeightPhase
import OddEJM.FourWalsh
import OddEJM.Pauli
import OddEJM.Masks
import OddEJM.Orthonormal
import Mathlib.Tactic

/-! 任意 Boolean 相位线的真实有限和及四律。 -/
noncomputable section
namespace UnifiedEJM.BooleanLines
open OddEJM Complex
open scoped BigOperators

/-- 任意布尔背景；q(0)=1时删去唯一物理零点。 -/
def raw {n : ℕ} (q : Bits n → Bit) (u : ℂ) (z : Bits n) : ℂ :=
  if z = 0 then 1 else -I * I ^ weight z * u ^ (q z).val

def background {n : ℕ} (q : Bits n → Bit) (u : ℂ) (z : Bits n) : ℂ :=
  I ^ weight z * u ^ (q z).val

theorem raw_corrected {n : ℕ} (q : Bits n → Bit) (hq : q 0 = 1)
    (u : ℂ) (z : Bits n) :
    raw q u z = -I * (background q u z + (I-u) * deltaZero z) := by
  by_cases hz : z = 0
  · subst z
    simp [raw, background, deltaZero, hq, ZMod.val_one_eq_one_mod]
  · simp [raw, background, deltaZero, hz]
    ring

theorem background_correlation {n : ℕ} (q : Bits n → Bit) (u c : ℂ) (a b : Bits n) :
    pauliExpectation (background q u) a b c =
      (c * star (I ^ weight a)) * phaseCorrelation q (a+b) a u (star u) := by
  simp only [pauliExpectation, background, phaseCorrelation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [star_mul]
  rw [show star (u ^ (q (z+a)).val) * star (I ^ weight (z+a)) * c * character b z *
      (I ^ weight z * u ^ (q z).val) =
      c * (star (I ^ weight (z+a)) * I ^ weight z) * character b z *
      star (u ^ (q (z+a)).val) * u ^ (q z).val by ring]
  rw [weight_phase_ratio, character_add_left]
  simp only [star_pow]
  ring

theorem raw_expectation {n : ℕ} (q : Bits n → Bit) (hq : q 0 = 1)
    (u c : ℂ) (a b : Bits n) (ha : a ≠ 0)
    (hc : c * character b a = star c) :
    pauliExpectation (raw q u) a b c =
      pauliExpectation (background q u) a b c +
      ((2 * (c * star (I ^ weight a) * star (u ^ (q a).val) * (I-u)).re : ℝ) : ℂ) := by
  have hr : raw q u = fun z => -I * (background q u z + (I-u)*deltaZero z) :=
    funext (raw_corrected q hq u)
  rw [hr, pauliExpectation_scale]
  simp only [show star (-I) * -I = 1 by simp, one_mul]
  rw [pauliExpectation_add_delta_hermitian _ _ _ _ _ ha hc]
  congr 3
  simp only [background, star_mul]
  ring

theorem angle_re (t : ℝ) : (anglePhase t).re = Real.cos t := by
  simp [anglePhase, Complex.exp_ofReal_mul_I_re]
theorem angle_im (t : ℝ) : (anglePhase t).im = Real.sin t := by
  simp [anglePhase, Complex.exp_ofReal_mul_I_im]

theorem background_I {n : ℕ} (q : Bits n → Bit) (t : ℝ) (a b : Bits n) (c : ℂ)
    (hh : a+b ≠ 0) (hd : dot (a+b) a = 1)
    (hg : c * star (I ^ weight a) = -I) :
    pauliExpectation (background q (anglePhase t)) a b c =
      -walsh q (a+b) * (Real.sin t : ℂ) := by
  rw [background_correlation, hg]
  have he := four_walsh_expansion q (a+b) a (anglePhase t) (star (anglePhase t))
  rw [character_sum, if_neg hh, walsh_translate, derivative_walsh_zero q _ _ hd] at he
  have hc : character (a+b) a = -1 := by simp [character, hd]
  rw [hc] at he
  have hu : star (anglePhase t) - anglePhase t = -2 * I * (Real.sin t : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, angle_re, angle_im, Complex.sin_ofReal_re, Complex.cos_ofReal_re] <;> ring
  have he' : 4 * phaseCorrelation q (a+b) a (anglePhase t) (star (anglePhase t)) =
      2 * (star (anglePhase t) - anglePhase t) * walsh q (a+b) := by
    rw [he]
    ring
  rw [hu] at he'
  linear_combination (norm := skip) (-I/4) * he'
  ring_nf
  simp [I_sq]

theorem background_II {n : ℕ} (q : Bits n → Bit) (t : ℝ) (a b : Bits n) (c : ℂ)
    (hh : a+b ≠ 0) (hd : dot (a+b) a = 0)
    (hg : c * star (I ^ weight a) = -1) :
    pauliExpectation (background q (anglePhase t)) a b c =
      -(walsh (derivative q a) (a+b) / 2) * (1 - (Real.cos t : ℂ)) := by
  rw [background_correlation, hg]
  have he := four_walsh_expansion q (a+b) a (anglePhase t) (star (anglePhase t))
  rw [character_sum, if_neg hh, walsh_translate] at he
  have hc : character (a+b) a = 1 := by simp [character, hd]
  rw [hc] at he
  have hu := anglePhase_star_mul t
  have hu' : anglePhase t * star (anglePhase t) = 1 := by simpa [mul_comm] using hu
  have hc' : (1-anglePhase t) * (1+star (anglePhase t)) +
      (1+anglePhase t) * (1-star (anglePhase t)) = 0 := by
    linear_combination -2 * hu'
  have hd' : (1-anglePhase t) * (1-star (anglePhase t)) =
      2 * (1-(Real.cos t : ℂ)) := by
    have hs : anglePhase t + star (anglePhase t) = 2 * (Real.cos t : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, angle_re, angle_im, Complex.sin_ofReal_re, Complex.cos_ofReal_re] <;> ring
    linear_combination hu' - hs
  have he' : 4 * phaseCorrelation q (a+b) a (anglePhase t) (star (anglePhase t)) =
      2 * (1-(Real.cos t : ℂ)) * walsh (derivative q a) (a+b) := by
    calc
      _ = ((1-anglePhase t)*(1+star (anglePhase t)) +
          (1+anglePhase t)*(1-star (anglePhase t))) * walsh q (a+b) +
          ((1-anglePhase t)*(1-star (anglePhase t))) * walsh (derivative q a) (a+b) := by
        rw [he]; ring
      _ = _ := by rw [hc', hd']; ring
  linear_combination (-1/4:ℂ) * he'

/-- I类真实未归一期望的实部，不假设背景消失。 -/
theorem raw_I_re {n : ℕ} (q : Bits n → Bit) (hq : q 0 = 1)
    (t : ℝ) (a b : Bits n) (c : ℂ) (ha : a ≠ 0)
    (hc : c * character b a = star c) (hh : a+b ≠ 0)
    (hd : dot (a+b) a = 1) (hg : c * star (I ^ weight a) = -I) :
    (pauliExpectation (raw q (anglePhase t)) a b c).re =
      2*(1-(q a).val) + 2*(q a).val*Real.cos t -
      (2*(1-(q a).val)+(walsh q (a+b)).re)*Real.sin t := by
  rw [raw_expectation q hq _ _ _ _ ha hc, background_I q t a b c hh hd hg]
  rw [hg]
  rcases bit_cases (q a) with h | h <;>
    simp [h, ZMod.val_one_eq_one_mod, Complex.mul_re, angle_re, angle_im, Complex.sin_ofReal_re, Complex.cos_ofReal_re]
  all_goals ring

/-- II类真实未归一期望的实部。 -/
theorem raw_II_re {n : ℕ} (q : Bits n → Bit) (hq : q 0 = 1)
    (t : ℝ) (a b : Bits n) (c : ℂ) (ha : a ≠ 0)
    (hc : c * character b a = star c) (hh : a+b ≠ 0)
    (hd : dot (a+b) a = 0) (hg : c * star (I ^ weight a) = -1) :
    (pauliExpectation (raw q (anglePhase t)) a b c).re =
      2*(q a).val - (walsh (derivative q a) (a+b)).re/2 +
      (2*(1-(q a).val)+(walsh (derivative q a) (a+b)).re/2)*Real.cos t -
      2*(q a).val*Real.sin t := by
  rw [raw_expectation q hq _ _ _ _ ha hc, background_II q t a b c hh hd hg, hg]
  have hu := anglePhase_star_mul t
  rcases bit_cases (q a) with h | h
  · simp [h, Complex.mul_re, angle_re, angle_im, Complex.div_re, Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    ring
  · have he : -star (anglePhase t) * (I-anglePhase t) =
        1-I*star (anglePhase t) := by
      linear_combination hu
    simp only [h, ZMod.val_one_eq_one_mod, Nat.one_mod, pow_one, neg_one_mul]
    rw [he]
    simp [Complex.mul_re, angle_re, angle_im, Complex.div_re, Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    ring




/-- 一阶三角多项式以三个实系数保存，系数来自上面的真实有限和。 -/
@[ext] structure Trig where
  constant : ℝ
  cosine : ℝ
  sine : ℝ

def Trig.eval (p : Trig) (t : ℝ) : ℝ := p.constant + p.cosine * Real.cos t + p.sine * Real.sin t

theorem Trig.continuous (p : Trig) : Continuous p.eval := by
  unfold Trig.eval
  fun_prop

/-- 在任何零点邻域成立的恒等式已决定全部三个系数，无须解析性公理。 -/
theorem trig_unique_local (A B C : ℝ)
    (h : ∀ᶠ t in nhds (0 : ℝ), A+B*Real.cos t+C*Real.sin t=0) :
    A=0 ∧ B=0 ∧ C=0 := by
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp h
  have h0 : A+B=0 := by
    have ht := hb (show (0:ℝ) ∈ Metric.ball 0 ε by simpa using hε)
    simpa using ht
  let x : ℝ := min (ε/2) (Real.pi/2)
  have hx : 0<x := lt_min (by positivity) (by positivity)
  have hxe : x<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hxp : x<Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hp := hb (show x ∈ Metric.ball 0 ε by simpa [Real.dist_eq, abs_of_pos hx] using hxe)
  have hm := hb (show -x ∈ Metric.ball 0 ε by simpa [Real.dist_eq, abs_of_pos hx] using hxe)
  change A+B*Real.cos x+C*Real.sin x=0 at hp
  change A+B*Real.cos (-x)+C*Real.sin (-x)=0 at hm
  simp only [Real.cos_neg, Real.sin_neg] at hm
  have hs : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx hxp
  have hc : Real.cos x < 1 := by
    have hc' := Real.cos_lt_cos_of_nonneg_of_le_pi (show 0 ≤ (0:ℝ) by exact le_rfl) hxp.le hx
    simpa using hc'
  have hC : C=0 := by nlinarith
  have hB : B=0 := by
    rw [hC] at hp
    have hz : B*(Real.cos x-1)=0 := by nlinarith [hp]
    exact (mul_eq_zero.mp hz).resolve_right (by linarith)
  exact ⟨by linarith, hB, hC⟩

theorem Trig.eq_of_eventually_eq (p q : Trig)
    (h : ∀ᶠ t in nhds (0:ℝ), p.eval t=q.eval t) : p=q := by
  have hz : ∀ᶠ t in nhds (0:ℝ),
      (p.constant-q.constant)+(p.cosine-q.cosine)*Real.cos t+
      (p.sine-q.sine)*Real.sin t=0 := by
    filter_upwards [h] with t ht
    simp only [Trig.eval] at ht
    linarith
  obtain ⟨h1,h2,h3⟩ := trig_unique_local _ _ _ hz
  ext <;> linarith

/-- 基点同为正分量时，局部等平方已经迫使全部参数上的signed分量相等。 -/
theorem Trig.eq_of_eventually_sq_eq (p q : Trig) (hp : 0<p.eval 0) (hq : 0<q.eval 0)
    (h : ∀ᶠ t in nhds (0:ℝ), p.eval t ^ 2=q.eval t ^ 2) : p=q := by
  have hpp : ∀ᶠ t in nhds (0:ℝ), 0<p.eval t :=
    p.continuous.continuousAt.eventually (lt_mem_nhds hp)
  have hqq : ∀ᶠ t in nhds (0:ℝ), 0<q.eval t :=
    q.continuous.continuousAt.eventually (lt_mem_nhds hq)
  apply Trig.eq_of_eventually_eq
  filter_upwards [h,hpp,hqq] with t ht hpt hqt
  nlinarith

def coeffI (s : Bit) (W : ℝ) : Trig :=
  ⟨2*(1-s.val), 2*s.val, -(2*(1-s.val)+W)⟩
def coeffII (k : Bit) (V : ℝ) : Trig :=
  ⟨2*k.val-V/2, 2*(1-k.val)+V/2, -2*k.val⟩
def law (s k : Bit) : Trig := ⟨2*(1-s.val),2*s.val,-2*k.val⟩

/-- 两类实际期望的系数相同，等价于论文的两个Walsh等式。 -/
theorem equal_coefficients (s k : Bit) (W V : ℝ) :
    coeffI s W=coeffII k V ↔
      W=2*((s.val:ℝ)+k.val-1) ∧ V=4*((s.val:ℝ)+k.val-1) := by
  constructor
  · intro h
    have h0 := congrArg Trig.constant h
    have h2 := congrArg Trig.sine h
    simp only [coeffI,coeffII] at h0 h2
    constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    ext <;> simp [coeffI,coeffII] <;> ring

theorem common_law (s k : Bit) (W V : ℝ) (h : coeffI s W=coeffII k V) :
    coeffI s W=law s k := by
  obtain ⟨hW,_⟩ := (equal_coefficients s k W V).mp h
  ext <;> simp [coeffI,law,hW] <;> ring

/-- 未归一期望最多为4，即共同半径至多2r_E。 -/
theorem law_abs_le (s k : Bit) (t : ℝ) : |(law s k).eval t| ≤ 4 := by
  have hs := Real.neg_one_le_sin t
  have hs' := Real.sin_le_one t
  have hc := Real.neg_one_le_cos t
  have hc' := Real.cos_le_one t
  rcases bit_cases s with rfl | rfl <;> rcases bit_cases k with rfl | rfl <;>
    simp only [law, Trig.eval, ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.one_mod,
      Nat.cast_zero, Nat.cast_one] <;> rw [abs_le] <;> constructor <;> nlinarith




/-- 与具体相位核无关的I类拉回数据。 -/
structure PullI {n : ℕ} (a b : Bits n) (c : ℂ) : Prop where
  ha : a ≠ 0
  hh : a+b ≠ 0
  hd : dot (a+b) a=1
  hc : c*character b a=star c
  hg : c*star (I^weight a) = -I

structure PullII {n : ℕ} (a b : Bits n) (c : ℂ) : Prop where
  ha : a ≠ 0
  hh : a+b ≠ 0
  hd : dot (a+b) a=0
  hc : c*character b a=star c
  hg : c*star (I^weight a) = -1

theorem first_pullI {n : ℕ} (hn : 0<n) : PullI (unitBit n 0) 0 1 := by
  have hw := MaskFacts.weight_unit (n:=n) 0 hn
  have hd : dot (unitBit n 0+0) (unitBit n 0)=1 := by
    rw [add_zero,MaskFacts.dot_unit _ 0 hn]
    simp [unitBit]
  refine ⟨MaskFacts.nonzero_of_weight (by omega),MaskFacts.nonzero_of_dot_one hd,hd,?_,?_⟩
  · simp [character,dot]
  · simp [hw]

theorem second_pullII {n : ℕ} (hn : 2≤n) : PullII (adjacentMask n 1) 0 1 := by
  have hw : weight (adjacentMask n 1)=2 :=
    MaskFacts.weight_pair 0 1 (by omega) (by omega) (by omega)
  have ha : adjacentMask n 1 ≠ 0 := MaskFacts.nonzero_of_weight (by omega)
  refine ⟨ha,by simpa using ha,?_,?_,?_⟩
  · simp only [add_zero,adjacentMask]
    change dot (unitBit n 0+unitBit n 1) (unitBit n 0+unitBit n 1)=0
    rw [dot_add, MaskFacts.dot_unit _ 0 (by omega), MaskFacts.dot_unit _ 1 (by omega)]
    norm_num [unitBit]
    decide
  · simp [character,dot]
  · norm_num [hw]

theorem raw_I_coeff {n : ℕ} (q : Bits n → Bit) (hq : q 0=1)
    {a b : Bits n} {c : ℂ} (hp : PullI a b c) (t : ℝ) :
    (pauliExpectation (raw q (anglePhase t)) a b c).re =
    (coeffI (q a) (walsh q (a+b)).re).eval t := by
  rw [raw_I_re q hq _ _ _ _ hp.ha hp.hc hp.hh hp.hd hp.hg]
  simp [coeffI, Trig.eval]; ring

theorem raw_II_coeff {n : ℕ} (q : Bits n → Bit) (hq : q 0=1)
    {a b : Bits n} {c : ℂ} (hp : PullII a b c) (t : ℝ) :
    (pauliExpectation (raw q (anglePhase t)) a b c).re =
    (coeffII (q a) (walsh (derivative q a) (a+b)).re).eval t := by
  rw [raw_II_re q hq _ _ _ _ hp.ha hp.hc hp.hh hp.hd hp.hg]
  simp [coeffII, Trig.eval]; ring

/-- 任意一个I行与II行在基点邻域等模，已经迫使真实I期望满足四律。 -/
theorem four_law_from_local_sq {n : ℕ} (q : Bits n → Bit) (hq : q 0=1)
    {a b A B : Bits n} {c C : ℂ} (hI : PullI a b c) (hII : PullII A B C)
    (hreg : ∀ᶠ t in nhds (0:ℝ),
      (pauliExpectation (raw q (anglePhase t)) a b c).re^2 =
      (pauliExpectation (raw q (anglePhase t)) A B C).re^2) :
    (walsh q (a+b)).re=2*((q a).val+(q A).val-1:ℝ) ∧
    (walsh (derivative q A) (A+B)).re=4*((q a).val+(q A).val-1:ℝ) ∧
    ∀ t, (pauliExpectation (raw q (anglePhase t)) a b c).re=
      (law (q a) (q A)).eval t := by
  let p := coeffI (q a) (walsh q (a+b)).re
  let p' := coeffII (q A) (walsh (derivative q A) (A+B)).re
  have hpp : p=p' := by
    apply Trig.eq_of_eventually_sq_eq
    · simp [p,coeffI,Trig.eval]; ring_nf; norm_num
    · simp [p',coeffII,Trig.eval]; ring_nf; norm_num
    · filter_upwards [hreg] with t ht
      simpa only [raw_I_coeff q hq hI,raw_II_coeff q hq hII] using ht
  obtain ⟨hW,hV⟩ := (equal_coefficients _ _ _ _).mp hpp
  refine ⟨hW,hV,?_⟩
  intro t
  rw [raw_I_coeff q hq hI,common_law _ _ _ _ hpp]

/-- 归一化种子仍是原始门电路作用于显式相位向量。 -/
def seed {n : ℕ} (q : Bits n → Bit) (t : ℝ) : Vec n :=
  circuit (fun z => normFactor n * raw q (anglePhase t) z)

def seedX {n : ℕ} (q : Bits n → Bit) (t : ℝ) (j : ℕ) : ℝ :=
  (pauliExpectation (seed q t) (unitBit n j) 0 1).re

theorem normFactor_squared (n : ℕ) :
    star (normFactor n)*normFactor n = ((1/(2:ℝ)^n:ℝ):ℂ) := by
  have hd : (2:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow,Complex.ofReal_ofNat]
  apply (eq_div_iff hd).mpr
  exact normFactor_card n

theorem normalized_expectation_re {n : ℕ} (f : Vec n) (a b : Bits n) (c : ℂ) :
    (pauliExpectation (fun z=>normFactor n*f z) a b c).re =
      (pauliExpectation f a b c).re/(2:ℝ)^n := by
  rw [pauliExpectation_scale,normFactor_squared]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem seedX_first {n : ℕ} (hn : 2≤n) (q : Bits n → Bit) (hq : q 0=1) (t : ℝ) :
    seedX q t 0=(coeffI (q (unitBit n 0)) (walsh q (unitBit n 0)).re).eval t/(2:ℝ)^n := by
  unfold seedX seed
  have h := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z=>normFactor n*raw q (anglePhase t) z) (unitBit n 0) 0 (unitBit n 0) 0 1 1
    (by simpa using (CircuitPauli.localX_beforeLast 0 (by omega : 0<n-1)
      (fun z=>normFactor n*raw q (anglePhase t) z)))
  rw [h,normalized_expectation_re,raw_I_coeff q hq (first_pullI (by omega))]
  simp

theorem seedX_second {n : ℕ} (hn : 3≤n) (q : Bits n → Bit) (hq : q 0=1) (t : ℝ) :
    seedX q t 1=(coeffII (q (adjacentMask n 1))
      (walsh (derivative q (adjacentMask n 1)) (adjacentMask n 1)).re).eval t/(2:ℝ)^n := by
  unfold seedX seed
  have h := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z=>normFactor n*raw q (anglePhase t) z) (unitBit n 1) 0 (adjacentMask n 1) 0 1 1
    (by simpa [adjacentMask,add_comm] using (CircuitPauli.localX_beforeLast 1 (by omega : 1<n-1)
      (fun z=>normFactor n*raw q (anglePhase t) z)))
  rw [h,normalized_expectation_re,raw_II_coeff q hq (second_pullII (by omega))]
  simp

/-- 从实际电路的局部等模条件得全参数四律，所有n≥3。 -/
theorem actual_seed_four_law {n : ℕ} (hn : 3≤n) (q : Bits n → Bit) (hq : q 0=1)
    (hreg : ∀ᶠ t in nhds (0:ℝ), seedX q t 0 ^ 2=seedX q t 1 ^ 2) :
    ∀ t, seedX q t 0=(law (q (unitBit n 0)) (q (adjacentMask n 1))).eval t/(2:ℝ)^n := by
  let p := coeffI (q (unitBit n 0)) (walsh q (unitBit n 0)).re
  let p' := coeffII (q (adjacentMask n 1))
    (walsh (derivative q (adjacentMask n 1)) (adjacentMask n 1)).re
  have hp : p=p' := by
    apply Trig.eq_of_eventually_sq_eq
    · simp [p,coeffI,Trig.eval]; ring_nf; norm_num
    · simp [p',coeffII,Trig.eval]; ring_nf; norm_num
    · filter_upwards [hreg] with t ht
      rw [seedX_first (by omega) q hq,seedX_second hn q hq] at ht
      have hd : (2:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
      change (p.eval t/(2:ℝ)^n)^2=(p'.eval t/(2:ℝ)^n)^2 at ht
      field_simp at ht
      exact ht
  intro t
  rw [seedX_first (by omega) q hq,common_law _ _ _ _ hp]

theorem actual_seed_bound {n : ℕ} (hn : 3≤n) (q : Bits n → Bit) (hq : q 0=1)
    (hreg : ∀ᶠ t in nhds (0:ℝ), seedX q t 0 ^ 2=seedX q t 1 ^ 2) (t : ℝ) :
    |seedX q t 0| ≤ 4/(2:ℝ)^n := by
  rw [actual_seed_four_law hn q hq hreg,abs_div,abs_of_pos (by positivity : 0<(2:ℝ)^n)]
  exact div_le_div_of_nonneg_right (law_abs_le _ _ t) (by positivity)

end UnifiedEJM.BooleanLines

