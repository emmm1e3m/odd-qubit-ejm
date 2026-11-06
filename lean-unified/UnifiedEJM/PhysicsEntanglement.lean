import UnifiedEJM.PhysicsPairs
import UnifiedEJM.PhysicsPairsNew5
import UnifiedEJM.PhysicsEndpoint
import UnifiedEJM.EvenLow
import UnifiedEJM.Main

noncomputable section
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsEntanglement
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PhysicsFinite Multipartite

/-- Laurent系数的实部对应五个真实三角系数，无需对称性假设。 -/
def realCoeffs (q : Fin 5 → G) : Fin 5 → ℤ :=
  ![(q 2).re, (q 1).re + (q 3).re, (q 1).im - (q 3).im,
    (q 0).re + (q 4).re, (q 0).im - (q 4).im]

def trigEval (q : Fin 5 → ℤ) (t : ℝ) : ℝ :=
  q 0 + q 1 * Real.cos t + q 2 * Real.sin t +
    q 3 * Real.cos (2*t) + q 4 * Real.sin (2*t)

theorem laurentEval_re (q : Fin 5 → G) (t : ℝ) :
    (laurentEval q (anglePhase t)).re = trigEval (realCoeffs q) t := by
  simp only [laurentEval, trigEval, realCoeffs, anglePhase,
    Complex.exp_ofReal_mul_I, GaussianInt.toComplex_def₂, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Matrix.cons_val_zero, Real.cos_two_mul',Real.sin_two_mul]
  simp [-GaussianInt.intCast_re,-GaussianInt.intCast_im]
  ring

/-- 每个振荡项的统一上界。 -/
theorem mul_trig_le_abs (a x : ℝ) (hx : |x| ≤ 1) : a*x ≤ |a| := by
  apply (le_abs_self _).trans
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left hx (abs_nonneg a)

theorem trigEval_le (q : Fin 5 → ℤ) (t : ℝ) :
    trigEval q t ≤ (q 0 : ℝ) + |(q 1 : ℝ)| + |(q 2 : ℝ)| +
      |(q 3 : ℝ)| + |(q 4 : ℝ)| := by
  have h1 := mul_trig_le_abs (q 1) (Real.cos t) (Real.abs_cos_le_one t)
  have h2 := mul_trig_le_abs (q 2) (Real.sin t) (Real.abs_sin_le_one t)
  have h3 := mul_trig_le_abs (q 3) (Real.cos (2*t)) (Real.abs_cos_le_one _)
  have h4 := mul_trig_le_abs (q 4) (Real.sin (2*t)) (Real.abs_sin_le_one _)
  unfold trigEval
  linarith

theorem linear_trig_sq_le (a b t : ℝ) :
    (a * Real.cos t + b * Real.sin t)^2 ≤ a^2+b^2 := by
  calc
    _ = (a^2+b^2) * (Real.sin t^2+Real.cos t^2) -
        (a*Real.sin t-b*Real.cos t)^2 := by ring
    _ ≤ a^2+b^2 := by rw [Real.sin_sq_add_cos_sq]; nlinarith [sq_nonneg (a*Real.sin t-b*Real.cos t)]

theorem special_trig_one (t : ℝ) : 14*Real.cos t - 3*Real.sin t ≤ 15 := by
  have h := linear_trig_sq_le 14 (-3) t
  nlinarith [sq_nonneg (14*Real.cos t - 3*Real.sin t - 15)]

theorem special_trig_two (t : ℝ) : 3*Real.cos t - 4*Real.sin t ≤ 5 := by
  have h := linear_trig_sq_le 3 (-4) t
  nlinarith [sq_nonneg (3*Real.cos t - 4*Real.sin t - 5)]

theorem special_five_bound (t : ℝ) :
    (379:ℝ)/1024 + (14*Real.cos t-3*Real.sin t)/128 +
      (3*Real.cos (2*t)-4*Real.sin (2*t))/1024 ≤ 63/128 := by
  have h1 := special_trig_one t
  have h2 := special_trig_two (2*t)
  linarith

/-- 原门单体纯度，与任意子系统接口一致。 -/
theorem seed_singleton_purity {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (j : Fin n) :
    cutPurity {j} (UnifiedEJM.seed n t) = (((1+OddEJM.radius n t^2)/2 : ℝ) : ℂ) := by
  rw [cutPurity_singleton]
  have h := UnifiedEJM.measurement_purity hn t 0 j
  have heq : UnifiedEJM.measurement n t 0 = UnifiedEJM.seed n t :=
    Physical.measurement_zero (UnifiedEJM.rawPhase (anglePhase t))
  simpa only [heq] using h

theorem seed_singleton_purity_re {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (j : Fin n) :
    (cutPurity {j} (UnifiedEJM.seed n t)).re = (1+OddEJM.radius n t^2)/2 := by
  rw [seed_singleton_purity hn]
  rfl

theorem special_trig_abs_one (t : ℝ) :
    |14*Real.cos t-3*Real.sin t| ≤ Real.sqrt 205 := by
  apply Real.abs_le_sqrt
  have h := linear_trig_sq_le 14 (-3) t
  norm_num [sub_eq_add_neg] at h ⊢
  exact h

theorem special_trig_abs_two (t : ℝ) :
    |3*Real.cos t-4*Real.sin t| ≤ 5 := by
  have h := Real.abs_le_sqrt (linear_trig_sq_le 3 (-4) t)
  norm_num at h
  simpa [sub_eq_add_neg] using h

theorem sqrt205_lt_fifteen : Real.sqrt (205:ℝ) < 15 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 205),Real.sqrt_nonneg (205:ℝ)]

/-- 真实纯度和两体纯度总和确为实数，可在实标量和复矩阵接口之间无损转换。 -/
theorem cutPurity_star {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    star (cutPurity S ψ) = cutPurity S ψ := by
  unfold cutPurity PurityInvariant.purity
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem twoBodyPurity_star {n : ℕ} (ψ : Vec n) :
    star (twoBodyPurity ψ) = twoBodyPurity ψ := by
  unfold twoBodyPurity
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro S hS
  change star (if S.card = 2 then cutPurity S ψ else 0) = _
  by_cases h : S.card = 2
  · simp only [ite_eq_left h,cutPurity_star]
  · simp only [ite_eq_right h,star_zero]

theorem twoBodyPurity_eq_ofReal {n : ℕ} (ψ : Vec n) :
    twoBodyPurity ψ = ((twoBodyPurity ψ).re : ℂ) := by
  have hi := congrArg Complex.im (twoBodyPurity_star ψ)
  simp only [Complex.star_def,Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

open Multipartite

/-- 无序二分割中的单比特侧，包括补集表示。 -/
def SingleCut {n : ℕ} (S : Finset (Fin n)) : Prop := S.card = 1 ∨ Sᶜ.card = 1

theorem singleton_mem_cuts {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    ({j} : Finset (Fin n)) ∈ cuts n := by
  simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨Finset.singleton_ne_empty j,?_⟩
  intro h
  have hh := congrArg Finset.card h
  simp only [Finset.card_singleton,Finset.card_univ,Fintype.card_fin] at hh
  omega

theorem singleCut_purity {n : ℕ} (ψ : Vec n) (p : ℝ)
    (h1 : ∀ j, (cutPurity {j} ψ).re = p)
    (S : Finset (Fin n)) (hS : SingleCut S) : (cutPurity S ψ).re = p := by
  rcases hS with hS | hS
  · obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hS
    exact h1 j
  · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hS
    rw [← cutPurity_compl, hj]
    exact h1 j

theorem all_purity_le_singleton {n : ℕ} (ψ : Vec n) (p : ℝ) (hp : 1/2 ≤ p)
    (h1 : ∀ j, (cutPurity {j} ψ).re = p)
    (hother : ∀ S ∈ cuts n, ¬SingleCut S → (cutPurity S ψ).re < 1/2) :
    ∀ S ∈ cuts n, (cutPurity S ψ).re ≤ p := by
  classical
  intro S hS
  by_cases hsingle : SingleCut S
  · exact (singleCut_purity ψ p h1 S hsingle).le
  · exact (hother S hS hsingle).le.trans hp

theorem gme_of_singleton_dominance {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n)
    (p : ℝ) (hp : 1/2 ≤ p) (h1 : ∀ j, (cutPurity {j} ψ).re = p)
    (hother : ∀ S ∈ cuts n, ¬SingleCut S → (cutPurity S ψ).re < 1/2) :
    gme hn ψ = Real.sqrt (2*(1-p)) := by
  apply gme_of_max_purity hn ψ p
  · exact all_purity_le_singleton ψ p hp h1 hother
  · let j : Fin n := ⟨0, by omega⟩
    exact ⟨{j},singleton_mem_cuts hn j,h1 j⟩

theorem purity_maximizers_iff {n : ℕ} (ψ : Vec n) (p : ℝ) (hp : 1/2 ≤ p)
    (h1 : ∀ j, (cutPurity {j} ψ).re = p)
    (hother : ∀ S ∈ cuts n, ¬SingleCut S → (cutPurity S ψ).re < 1/2)
    (S : Finset (Fin n)) (hS : S ∈ cuts n) :
    (cutPurity S ψ).re = p ↔ SingleCut S := by
  classical
  constructor
  · intro h
    by_contra hsingle
    have hh := hother S hS hsingle
    rw [h] at hh
    exact (not_lt_of_ge hp) hh
  · exact singleCut_purity ψ p h1 S

theorem gme_minimizers_iff {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n)
    (p : ℝ) (hp : 1/2 ≤ p) (hp1 : p ≤ 1)
    (h1 : ∀ j, (cutPurity {j} ψ).re = p)
    (hother : ∀ S ∈ cuts n, ¬SingleCut S → (cutPurity S ψ).re < 1/2)
    (S : Finset (Fin n)) (hS : S ∈ cuts n) :
    Real.sqrt (2*(1-(cutPurity S ψ).re)) = gme hn ψ ↔ SingleCut S := by
  rw [gme_of_singleton_dominance hn ψ p hp h1 hother]
  constructor
  · intro h
    have hupper := all_purity_le_singleton ψ p hp h1 hother S hS
    have hsq := congrArg (fun x : ℝ => x^2) h
    rw [Real.sq_sqrt (by linarith),Real.sq_sqrt (by linarith)] at hsq
    apply (purity_maximizers_iff ψ p hp h1 hother S hS).1
    linarith
  · intro h
    rw [singleCut_purity ψ p h1 S h]

/-- 单体达到者和全部较大cut严格界给出实际全参数GME。 -/
theorem seed_gme_of_bounds {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (hother : ∀ S ∈ cuts n, ¬SingleCut S →
      (cutPurity S (UnifiedEJM.seed n t)).re < 1/2) :
    gme (by omega : 2 ≤ n) (UnifiedEJM.seed n t) =
      Real.sqrt (1-OddEJM.radius n t^2) := by
  have h := gme_of_singleton_dominance (by omega : 2 ≤ n) (UnifiedEJM.seed n t)
    ((1+OddEJM.radius n t^2)/2) (by nlinarith [sq_nonneg (OddEJM.radius n t)])
    (seed_singleton_purity_re hn t) hother
  convert h using 1
  congr 1
  ring

open PhysicsFinite Multipartite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- 所有整数系数表与实部三角转换逐项一致。 -/
theorem new5_realCoeffs : ∀ k, realCoeffs (new5Coeff k) = new5Trig k := by decide +kernel
theorem new6_realCoeffs : ∀ k, realCoeffs (new6Coeff k) = new6Trig k := by decide +kernel
theorem pg6_realCoeffs : ∀ k, realCoeffs (pg6Coeff k) = pg6Trig k := by decide +kernel

def trigL1 (q : Fin 5 → ℤ) : ℤ := q 0 + |q 1| + |q 2| + |q 3| + |q 4|

theorem trigEval_le_L1 (q : Fin 5 → ℤ) (t : ℝ) :
    trigEval q t ≤ (trigL1 q : ℝ) := by
  simpa only [trigL1,Int.cast_add,Int.cast_abs] using trigEval_le q t

/-- 排除两种特殊的二体分割后，整数表直接给出其余cut的界。 -/
theorem new5_other_L1 : ∀ k : Fin 15, k ≠ 2 → k ≠ 6 →
    ¬SingleCut (canonicalCut5 k) → trigL1 (new5Trig k) ≤ 1280 := by unfold SingleCut; decide +kernel

theorem new6_larger_L1 : ∀ k : Fin 31,
    ¬SingleCut (canonicalCut6 k) → trigL1 (new6Trig k) ≤ 8056 := by unfold SingleCut; decide +kernel

theorem new5_special_formula (t : ℝ) :
    trigEval (new5Trig 2) t / 4096 =
      379/1024 + (14*Real.cos t-3*Real.sin t)/128 +
        (3*Real.cos (2*t)-4*Real.sin (2*t))/1024 := by
  norm_num [new5Trig,trigEval]
  ring

theorem new5_trig_bound (k : Fin 15) (t : ℝ)
    (hk : ¬SingleCut (canonicalCut5 k)) :
    trigEval (new5Trig k) t / 4096 ≤ 63/128 := by
  by_cases h2 : k = 2
  · subst k
    rw [new5_special_formula]
    exact special_five_bound t
  by_cases h6 : k = 6
  · subst k
    rw [show new5Trig 6 = new5Trig 2 by decide +kernel,new5_special_formula]
    exact special_five_bound t
  have h := trigEval_le_L1 (new5Trig k) t
  have hi := new5_other_L1 k h2 h6 hk
  have hr : (trigL1 (new5Trig k) : ℝ) ≤ 1280 := by exact_mod_cast hi
  linarith

theorem new6_trig_bound (k : Fin 31) (t : ℝ)
    (hk : ¬SingleCut (canonicalCut6 k)) :
    trigEval (new6Trig k) t / 16384 ≤ 1007/2048 := by
  have h := trigEval_le_L1 (new6Trig k) t
  have hi := new6_larger_L1 k hk
  have hr : (trigL1 (new6Trig k) : ℝ) ≤ 8056 := by exact_mod_cast hi
  linarith

theorem pg6_zero_trig_bound (k : Fin 31) :
    trigEval (pg6Trig k) (Real.pi/2) / 16384 ≤ 5/8 := by
  fin_cases k <;> norm_num [trigEval,pg6Trig,show 2*(Real.pi/2)=Real.pi by ring]

theorem pg6_zero_trig_attain :
    trigEval (pg6Trig 2) (Real.pi/2) / 16384 = 5/8 := by
  norm_num [trigEval,pg6Trig,show 2*(Real.pi/2)=Real.pi by ring]

open PhysicsFinite Multipartite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem scaled_laurent_re (d : ℝ) (q : Fin 5 → G) (t : ℝ) :
    (((d : ℂ)⁻¹ * laurentEval q (anglePhase t))).re =
      trigEval (realCoeffs q) t / d := by
  rw [← Complex.ofReal_inv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    sub_zero,laurentEval_re]
  ring

theorem new5_cut_trig (k : Fin 15) (t : ℝ) :
    (cutPurity (canonicalCut5 k) (UnifiedEJM.seed 5 t)).re =
      trigEval (new5Trig k) t / 4096 := by
  rw [new5_cut_laurent]
  simpa only [Complex.ofReal_ofNat,new5_realCoeffs] using scaled_laurent_re 4096 (new5Coeff k) t

theorem new5_larger_cut_bound (t : ℝ) (S : Finset (Fin 5))
    (hS : S ∈ cuts 5) (hs : ¬SingleCut S) :
    (cutPurity S (UnifiedEJM.seed 5 t)).re ≤ 63/128 := by
  obtain ⟨k,hk|hk⟩ := cut5_enumeration S hS
  · subst S
    rw [new5_cut_trig]
    exact new5_trig_bound k t hs
  · subst S
    rw [cutPurity_compl,new5_cut_trig]
    exact new5_trig_bound k t (by simpa [SingleCut,or_comm] using hs)

theorem new5_larger_cut_lt_half (t : ℝ) : ∀ S ∈ cuts 5, ¬SingleCut S →
    (cutPurity S (UnifiedEJM.seed 5 t)).re < 1/2 := by
  intro S hS hs
  have := new5_larger_cut_bound t S hS hs
  linarith

theorem new5_seed_gme (t : ℝ) :
    gme (by decide : 2 ≤ 5) (UnifiedEJM.seed 5 t) = Real.sqrt (1-radius 5 t^2) :=
  seed_gme_of_bounds (by decide) t (new5_larger_cut_lt_half t)

theorem new5_measurement_gme (t : ℝ) (label : Bits 5) :
    gme (by decide : 2 ≤ 5) (UnifiedEJM.measurement 5 t label) =
      Real.sqrt (1-radius 5 t^2) := by
  change gme (by decide : 2 ≤ 5)
    (Physical.measurement (UnifiedEJM.rawPhase (anglePhase t)) label) = _
  rw [gme_measurement]
  exact new5_seed_gme t


theorem radius_sq_lt_one {n : ℕ} (hn : 5 ≤ n) (t : ℝ) : radius n t^2 < 1 := by
  have hlt := PhysicsEndpoint.radius_strictly_lt_one hn t
  have hnonneg : 0 ≤ radius n t := by
    rw [radius_eq_geometry]
    exact Geometry.radius_nonneg n t
  nlinarith

theorem radius_concurrence_pos {n : ℕ} (hn : 5 ≤ n) (t : ℝ) :
    0 < Real.sqrt (1-radius n t^2) := by
  apply Real.sqrt_pos.mpr
  have := radius_sq_lt_one hn t
  linarith

theorem new5_measurement_gme_pos (t : ℝ) (label : Bits 5) :
    0 < gme (by decide : 2 ≤ 5) (UnifiedEJM.measurement 5 t label) := by
  rw [new5_measurement_gme]
  exact radius_concurrence_pos (by decide) t

theorem new5_seed_minimizers (t : ℝ) (S : Finset (Fin 5)) (hS : S ∈ cuts 5) :
    Real.sqrt (2*(1-(cutPurity S (UnifiedEJM.seed 5 t)).re)) =
      gme (by decide : 2 ≤ 5) (UnifiedEJM.seed 5 t) ↔ SingleCut S := by
  apply gme_minimizers_iff (by decide) _ ((1+radius 5 t^2)/2)
  · nlinarith [sq_nonneg (radius 5 t)]
  · have := radius_sq_lt_one (by decide : 5 ≤ 5) t; linarith
  · exact seed_singleton_purity_re (by decide) t
  · exact new5_larger_cut_lt_half t
  · exact hS

theorem new5_measurement_minimizers (t : ℝ) (label : Bits 5)
    (S : Finset (Fin 5)) (hS : S ∈ cuts 5) :
    Real.sqrt (2*(1-(cutPurity S (UnifiedEJM.measurement 5 t label)).re)) =
      gme (by decide : 2 ≤ 5) (UnifiedEJM.measurement 5 t label) ↔ SingleCut S := by
  have hp := cutPurity_measurement (by decide : 0 < 5)
    (UnifiedEJM.rawPhase (anglePhase t)) label S
  have hg := gme_measurement (by decide : 2 ≤ 5)
    (UnifiedEJM.rawPhase (anglePhase t)) label
  change cutPurity S (UnifiedEJM.measurement 5 t label) =
    cutPurity S (UnifiedEJM.seed 5 t) at hp
  change gme (by decide : 2 ≤ 5) (UnifiedEJM.measurement 5 t label) =
    gme (by decide : 2 ≤ 5) (UnifiedEJM.seed 5 t) at hg
  rw [hp,hg]
  exact new5_seed_minimizers t S hS

theorem new5_zero_gme (label : Bits 5) :
    gme (by decide : 2 ≤ 5) (UnifiedEJM.measurement 5 (Real.pi/2) label) = 1 := by
  rw [new5_measurement_gme,radius_eq_geometry,Geometry.radius_at_right]
  norm_num

theorem new5_zero_seed_gme :
    gme (by decide : 2 ≤ 5) (UnifiedEJM.seed 5 (Real.pi/2)) = 1 := by
  rw [new5_seed_gme,radius_eq_geometry,Geometry.radius_at_right]
  norm_num

theorem new5_measurement_entangled (t : ℝ) (label : Bits 5)
    (S : Finset (Fin 5)) (hS : S ∈ cuts 5) :
    ¬ ProductAcross S (UnifiedEJM.measurement 5 t label) :=
  gme_pos_no_product (by decide) _ (new5_measurement_gme_pos t label) S hS

open PhysicsFinite Multipartite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem new6_cut_trig (k : Fin 31) (t : ℝ) :
    (cutPurity (canonicalCut6 k) (UnifiedEJM.seed 6 t)).re =
      trigEval (new6Trig k) t / 16384 := by
  rw [new6_cut_laurent]
  simpa only [Complex.ofReal_ofNat,new6_realCoeffs] using scaled_laurent_re 16384 (new6Coeff k) t

theorem new6_larger_cut_bound (t : ℝ) (S : Finset (Fin 6))
    (hS : S ∈ cuts 6) (hs : ¬SingleCut S) :
    (cutPurity S (UnifiedEJM.seed 6 t)).re ≤ 1007/2048 := by
  obtain ⟨k,hk|hk⟩ := cut6_enumeration S hS
  · subst S
    rw [new6_cut_trig]
    exact new6_trig_bound k t hs
  · subst S
    rw [cutPurity_compl,new6_cut_trig]
    exact new6_trig_bound k t (by simpa [SingleCut,or_comm] using hs)

theorem new6_larger_cut_lt_half (t : ℝ) : ∀ S ∈ cuts 6, ¬SingleCut S →
    (cutPurity S (UnifiedEJM.seed 6 t)).re < 1/2 := by
  intro S hS hs
  have := new6_larger_cut_bound t S hS hs
  linarith

theorem new6_seed_gme (t : ℝ) :
    gme (by decide : 2 ≤ 6) (UnifiedEJM.seed 6 t) = Real.sqrt (1-radius 6 t^2) :=
  seed_gme_of_bounds (by decide) t (new6_larger_cut_lt_half t)

theorem new6_measurement_gme (t : ℝ) (label : Bits 6) :
    gme (by decide : 2 ≤ 6) (UnifiedEJM.measurement 6 t label) =
      Real.sqrt (1-radius 6 t^2) := by
  change gme (by decide : 2 ≤ 6)
    (Physical.measurement (UnifiedEJM.rawPhase (anglePhase t)) label) = _
  rw [gme_measurement]
  exact new6_seed_gme t

theorem new6_measurement_gme_pos (t : ℝ) (label : Bits 6) :
    0 < gme (by decide : 2 ≤ 6) (UnifiedEJM.measurement 6 t label) := by
  rw [new6_measurement_gme]
  exact radius_concurrence_pos (by decide) t

theorem new6_seed_minimizers (t : ℝ) (S : Finset (Fin 6)) (hS : S ∈ cuts 6) :
    Real.sqrt (2*(1-(cutPurity S (UnifiedEJM.seed 6 t)).re)) =
      gme (by decide : 2 ≤ 6) (UnifiedEJM.seed 6 t) ↔ SingleCut S := by
  apply gme_minimizers_iff (by decide) _ ((1+radius 6 t^2)/2)
  · nlinarith [sq_nonneg (radius 6 t)]
  · have := radius_sq_lt_one (by decide : 5 ≤ 6) t; linarith
  · exact seed_singleton_purity_re (by decide) t
  · exact new6_larger_cut_lt_half t
  · exact hS

theorem new6_measurement_minimizers (t : ℝ) (label : Bits 6)
    (S : Finset (Fin 6)) (hS : S ∈ cuts 6) :
    Real.sqrt (2*(1-(cutPurity S (UnifiedEJM.measurement 6 t label)).re)) =
      gme (by decide : 2 ≤ 6) (UnifiedEJM.measurement 6 t label) ↔ SingleCut S := by
  have hp := cutPurity_measurement (by decide : 0 < 6)
    (UnifiedEJM.rawPhase (anglePhase t)) label S
  have hg := gme_measurement (by decide : 2 ≤ 6)
    (UnifiedEJM.rawPhase (anglePhase t)) label
  change cutPurity S (UnifiedEJM.measurement 6 t label) =
    cutPurity S (UnifiedEJM.seed 6 t) at hp
  change gme (by decide : 2 ≤ 6) (UnifiedEJM.measurement 6 t label) =
    gme (by decide : 2 ≤ 6) (UnifiedEJM.seed 6 t) at hg
  rw [hp,hg]
  exact new6_seed_minimizers t S hS

theorem new6_zero_gme (label : Bits 6) :
    gme (by decide : 2 ≤ 6) (UnifiedEJM.measurement 6 (Real.pi/2) label) = 1 := by
  rw [new6_measurement_gme,radius_eq_geometry,Geometry.radius_at_right]
  norm_num

theorem new6_zero_seed_gme :
    gme (by decide : 2 ≤ 6) (UnifiedEJM.seed 6 (Real.pi/2)) = 1 := by
  rw [new6_seed_gme,radius_eq_geometry,Geometry.radius_at_right]
  norm_num

theorem new6_measurement_entangled (t : ℝ) (label : Bits 6)
    (S : Finset (Fin 6)) (hS : S ∈ cuts 6) :
    ¬ ProductAcross S (UnifiedEJM.measurement 6 t label) :=
  gme_pos_no_product (by decide) _ (new6_measurement_gme_pos t label) S hS

open PhysicsFinite Multipartite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pg6_cut_trig (k : Fin 31) (t : ℝ) :
    (cutPurity (canonicalCut6 k) (EvenFamily.seed 6 t 0)).re =
      trigEval (pg6Trig k) t / 16384 := by
  rw [pg6_cut_laurent]
  simpa only [Complex.ofReal_ofNat,pg6_realCoeffs] using scaled_laurent_re 16384 (pg6Coeff k) t

/-- 真实偏迹给出的全参数严格界，包含互补表示。 -/
theorem pg6_zero_gme : gme (by decide : 2 ≤ 6) (EvenFamily.seed 6 (Real.pi/2) 0) =
    Real.sqrt 3 / 2 := by
  have h := gme_of_max_purity (by decide : 2 ≤ 6) (EvenFamily.seed 6 (Real.pi/2) 0) (5/8)
  have hmax : ∀ S ∈ cuts 6, (cutPurity S (EvenFamily.seed 6 (Real.pi/2) 0)).re ≤ 5/8 := by
    intro S hS
    obtain ⟨k,hk|hk⟩ := cut6_enumeration S hS
    · subst S
      rw [pg6_cut_trig]
      exact pg6_zero_trig_bound k
    · subst S
      rw [cutPurity_compl,pg6_cut_trig]
      exact pg6_zero_trig_bound k
  have hattain : ∃ S ∈ cuts 6, (cutPurity S (EvenFamily.seed 6 (Real.pi/2) 0)).re = 5/8 := by
    refine ⟨canonicalCut6 2,by decide +kernel,?_⟩
    rw [pg6_cut_trig]
    exact pg6_zero_trig_attain
  rw [h hmax hattain]
  norm_num [Real.sqrt_div]


theorem pg6_zero_measurement_gme (label : Bits 6) :
    gme (by decide : 2 ≤ 6) (EvenFamily.measurement 6 (Real.pi/2) 0 label) =
      Real.sqrt 3 / 2 := by
  change gme (by decide : 2 ≤ 6)
    (Physical.measurement (EvenFamily.diagonal 6 (Real.pi/2) 0) label) = _
  rw [gme_measurement]
  exact pg6_zero_gme

open PhysicsFinite Multipartite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem new6_pair_trig_formula (t : ℝ) :
    trigEval (realCoeffs new6PairCoeff) t / 16384 =
      16793/4096 + (23/128)*Real.cos t - (5/64)*Real.sin t -
        (39/4096)*Real.cos (2*t) - (1/128)*Real.sin (2*t) := by
  norm_num [trigEval,realCoeffs,new6PairCoeff]
  ring

theorem pg6_pair_trig_formula (t : ℝ) :
    trigEval (realCoeffs pg6PairCoeff) t / 16384 =
      18977/4096 - (15/128)*Real.cos t + (15/256)*Real.sin t -
        (1007/4096)*Real.cos (2*t) := by
  norm_num [trigEval,realCoeffs,pg6PairCoeff]
  ring

theorem new6_pair_nonzero_value :
    trigEval (realCoeffs new6PairCoeff) (Real.pi/6) / 16384 =
      (33227+704*Real.sqrt 3)/8192 := by
  rw [new6_pair_trig_formula]
  norm_num [show 2*(Real.pi/6)=Real.pi/3 by ring,
    Real.cos_pi_div_six,Real.sin_pi_div_six,Real.cos_pi_div_three,Real.sin_pi_div_three]
  ring

theorem pg6_pair_positive_value :
    trigEval (realCoeffs pg6PairCoeff) (Real.pi/3) / 16384 =
      (38481+240*Real.sqrt 3)/8192 := by
  rw [pg6_pair_trig_formula,Real.cos_two_mul]
  norm_num [Real.cos_pi_div_three,Real.sin_pi_div_three]
  ring

theorem pg6_pair_negative_value :
    trigEval (realCoeffs pg6PairCoeff) (-(Real.pi/3)) / 16384 =
      (38481-240*Real.sqrt 3)/8192 := by
  rw [pg6_pair_trig_formula,Real.cos_two_mul]
  norm_num [Real.cos_pi_div_three,Real.sin_pi_div_three,Real.cos_neg,Real.sin_neg]
  ring

theorem pair_gap_positive :
    (33227+704*Real.sqrt 3)/8192 < (38481+240*Real.sqrt 3)/8192 := by
  have hs : Real.sqrt (3:ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]
  linarith

theorem pair_gap_negative :
    (33227+704*Real.sqrt 3)/8192 < (38481-240*Real.sqrt 3)/8192 := by
  have hs : Real.sqrt (3:ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]
  linarith

/-- 非零比较点的实际单比特约化矩阵逐列相同。 -/
theorem equal_single_reductions_positive (label : Bits 6) (j : Fin 6) :
    OddEJM.reduced (UnifiedEJM.measurement 6 (Real.pi/6) label) j =
      OddEJM.reduced (EvenFamily.measurement 6 (Real.pi/3) 0 label) j := by
  rw [UnifiedEJM.measurement_reduced (by decide),
    EvenLow.measurement_reduced_all (by decide) (by decide)]
  rw [radius_eq_geometry]
  norm_num [Geometry.radiusFormula,Real.sin_pi_div_six,Real.cos_pi_div_three]

theorem equal_single_reductions_negative (label : Bits 6) (j : Fin 6) :
    OddEJM.reduced (UnifiedEJM.measurement 6 (Real.pi/6) label) j =
      OddEJM.reduced (EvenFamily.measurement 6 (-(Real.pi/3)) 0 label) j := by
  rw [UnifiedEJM.measurement_reduced (by decide),
    EvenLow.measurement_reduced_all (by decide) (by decide)]
  rw [radius_eq_geometry]
  norm_num [Geometry.radiusFormula,Real.sin_pi_div_six,Real.cos_pi_div_three,Real.cos_neg]

theorem equal_radius_positive :
    radius 6 (Real.pi/6) = EvenEmbedding.radius 6 (Real.pi/3) 0 := by
  rw [radius_eq_geometry]
  norm_num [Geometry.radiusFormula,EvenEmbedding.radius,Real.sin_pi_div_six,Real.cos_pi_div_three]

theorem equal_radius_negative :
    radius 6 (Real.pi/6) = EvenEmbedding.radius 6 (-(Real.pi/3)) 0 := by
  rw [radius_eq_geometry]
  norm_num [Geometry.radiusFormula,EvenEmbedding.radius,Real.sin_pi_div_six,Real.cos_pi_div_three,Real.cos_neg]

open PhysicsFinite Multipartite

/-- 五比特十个真实两体偏迹纯度的全参数总和。 -/
theorem new5_twoBody_formula (t : ℝ) :
    (twoBodyPurity (UnifiedEJM.seed 5 t)).re =
      751/256 + (7/32)*Real.cos t - (51/256)*Real.sin t -
        (5/64)*Real.cos (2*t) - (1/64)*Real.sin (2*t) := by
  rw [new5_twoBody_laurent]
  rw [show (4096:ℂ) = ((4096:ℝ):ℂ) by norm_num,scaled_laurent_re]
  norm_num [trigEval,realCoeffs,new5PairCoeff]
  ring

theorem new5_zero_twoBody :
    (twoBodyPurity (UnifiedEJM.seed 5 (Real.pi/2))).re = 45/16 := by
  rw [new5_twoBody_formula]
  norm_num [show 2*(Real.pi/2)=Real.pi by ring]

theorem new5_zero_measurement_twoBody (label : Bits 5) :
    (twoBodyPurity (UnifiedEJM.measurement 5 (Real.pi/2) label)).re = 45/16 := by
  have h := twoBodyPurity_measurement (by decide : 0 < 5)
    (UnifiedEJM.rawPhase (anglePhase (Real.pi/2))) label
  change twoBodyPurity (UnifiedEJM.measurement 5 (Real.pi/2) label) =
    twoBodyPurity (UnifiedEJM.seed 5 (Real.pi/2)) at h
  rw [h]
  exact new5_zero_twoBody

theorem new5_zero_twoBody_exact :
    twoBodyPurity (UnifiedEJM.seed 5 (Real.pi/2)) = (45/16 : ℂ) := by
  rw [twoBodyPurity_eq_ofReal,new5_zero_twoBody]
  norm_num

open PhysicsFinite Multipartite

/-- 下面P2均取自原门种子的真实全部两体偏迹。 -/
theorem new6_twoBody_formula (t : ℝ) :
    (twoBodyPurity (UnifiedEJM.seed 6 t)).re =
      16793/4096 + (23/128)*Real.cos t - (5/64)*Real.sin t -
        (39/4096)*Real.cos (2*t) - (1/128)*Real.sin (2*t) := by
  rw [new6_twoBody_laurent]
  rw [show (16384:ℂ) = ((16384:ℝ):ℂ) by norm_num,scaled_laurent_re]
  exact new6_pair_trig_formula t

theorem pg6_twoBody_formula (t : ℝ) :
    (twoBodyPurity (EvenFamily.seed 6 t 0)).re =
      18977/4096 - (15/128)*Real.cos t + (15/256)*Real.sin t -
        (1007/4096)*Real.cos (2*t) := by
  rw [pg6_twoBody_laurent]
  rw [show (16384:ℂ) = ((16384:ℝ):ℂ) by norm_num,scaled_laurent_re]
  exact pg6_pair_trig_formula t

theorem new6_twoBody_nonzero :
    (twoBodyPurity (UnifiedEJM.seed 6 (Real.pi/6))).re =
      (33227+704*Real.sqrt 3)/8192 := by
  rw [new6_twoBody_laurent]
  rw [show (16384:ℂ) = ((16384:ℝ):ℂ) by norm_num,scaled_laurent_re]
  exact new6_pair_nonzero_value

theorem pg6_twoBody_positive :
    (twoBodyPurity (EvenFamily.seed 6 (Real.pi/3) 0)).re =
      (38481+240*Real.sqrt 3)/8192 := by
  rw [pg6_twoBody_laurent]
  rw [show (16384:ℂ) = ((16384:ℝ):ℂ) by norm_num,scaled_laurent_re]
  exact pg6_pair_positive_value

theorem pg6_twoBody_negative :
    (twoBodyPurity (EvenFamily.seed 6 (-(Real.pi/3)) 0)).re =
      (38481-240*Real.sqrt 3)/8192 := by
  rw [pg6_twoBody_laurent]
  rw [show (16384:ℂ) = ((16384:ℝ):ℂ) by norm_num,scaled_laurent_re]
  exact pg6_pair_negative_value

theorem new6_zero_twoBody :
    (twoBodyPurity (UnifiedEJM.seed 6 (Real.pi/2))).re = 129/32 := by
  rw [new6_twoBody_formula]
  norm_num [show 2*(Real.pi/2)=Real.pi by ring]

theorem pg6_zero_twoBody :
    (twoBodyPurity (EvenFamily.seed 6 (Real.pi/2) 0)).re = 79/16 := by
  rw [pg6_twoBody_formula]
  norm_num [show 2*(Real.pi/2)=Real.pi by ring]

/-- 同半径的完整测量在任意LU、比特置换、结果标签及逐列相位下不等价。 -/
theorem equal_radius_measurements_inequivalent_positive :
    ¬ EquivalentMeasurements (UnifiedEJM.rawPhase (anglePhase (Real.pi/6)))
      (EvenFamily.diagonal 6 (Real.pi/3) 0) := by
  apply not_equivalent_of_twoBodyPurity (by decide : 0 < 6)
  intro h
  have hr := congrArg Complex.re h
  change (twoBodyPurity (UnifiedEJM.seed 6 (Real.pi/6))).re =
    (twoBodyPurity (EvenFamily.seed 6 (Real.pi/3) 0)).re at hr
  rw [new6_twoBody_nonzero,pg6_twoBody_positive] at hr
  exact (ne_of_lt pair_gap_positive) hr

theorem equal_radius_measurements_inequivalent_negative :
    ¬ EquivalentMeasurements (UnifiedEJM.rawPhase (anglePhase (Real.pi/6)))
      (EvenFamily.diagonal 6 (-(Real.pi/3)) 0) := by
  apply not_equivalent_of_twoBodyPurity (by decide : 0 < 6)
  intro h
  have hr := congrArg Complex.re h
  change (twoBodyPurity (UnifiedEJM.seed 6 (Real.pi/6))).re =
    (twoBodyPurity (EvenFamily.seed 6 (-(Real.pi/3)) 0)).re at hr
  rw [new6_twoBody_nonzero,pg6_twoBody_negative] at hr
  exact (ne_of_lt pair_gap_negative) hr

theorem zero_radius_measurements_inequivalent :
    ¬ EquivalentMeasurements (UnifiedEJM.rawPhase (anglePhase (Real.pi/2)))
      (EvenFamily.diagonal 6 (Real.pi/2) 0) := by
  apply not_equivalent_of_twoBodyPurity (by decide : 0 < 6)
  intro h
  have hr := congrArg Complex.re h
  change (twoBodyPurity (UnifiedEJM.seed 6 (Real.pi/2))).re =
    (twoBodyPurity (EvenFamily.seed 6 (Real.pi/2) 0)).re at hr
  rw [new6_zero_twoBody,pg6_zero_twoBody] at hr
  norm_num at hr

theorem new6_zero_twoBody_exact :
    twoBodyPurity (UnifiedEJM.seed 6 (Real.pi/2)) = (129/32 : ℂ) := by
  rw [twoBodyPurity_eq_ofReal,new6_zero_twoBody]
  norm_num

theorem pg6_zero_twoBody_exact :
    twoBodyPurity (EvenFamily.seed 6 (Real.pi/2) 0) = (79/16 : ℂ) := by
  rw [twoBodyPurity_eq_ofReal,pg6_zero_twoBody]
  norm_num

theorem new6_zero_measurement_twoBody (label : Bits 6) :
    (twoBodyPurity (UnifiedEJM.measurement 6 (Real.pi/2) label)).re = 129/32 := by
  change (twoBodyPurity (Physical.measurement
    (UnifiedEJM.rawPhase (anglePhase (Real.pi/2))) label)).re = _
  rw [twoBodyPurity_measurement (by decide)]
  exact new6_zero_twoBody

theorem pg6_zero_measurement_twoBody (label : Bits 6) :
    (twoBodyPurity (EvenFamily.measurement 6 (Real.pi/2) 0 label)).re = 79/16 := by
  change (twoBodyPurity (Physical.measurement
    (EvenFamily.diagonal 6 (Real.pi/2) 0) label)).re = _
  rw [twoBodyPurity_measurement (by decide)]
  exact pg6_zero_twoBody

end UnifiedEJM.PhysicsEntanglement
