import UnifiedEJM.LowDimensionalDefs
noncomputable section
namespace UnifiedEJM.LowDimensional
open scoped BigOperators
open Filter Topology
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

theorem signal_hasDerivAt (d : Direction) (p : Fin 12) (t : ℝ) :
    HasDerivAt (signal d p) (signalD1 d p t) t := by
  unfold signal signalD1
  apply HasDerivAt.fun_sum
  intro z hz
  convert (((hasDerivAt_id t).const_mul (frequency d p z)).cos.const_mul (coeffR p z)).sub
    (((hasDerivAt_id t).const_mul (frequency d p z)).sin.const_mul (coeffI p z)) using 1
  · rfl
  · dsimp; ring

theorem signalD1_hasDerivAt (d : Direction) (p : Fin 12) (t : ℝ) :
    HasDerivAt (signalD1 d p) (signalD2 d p t) t := by
  unfold signalD1 signalD2
  apply HasDerivAt.fun_sum
  intro z hz
  convert (((hasDerivAt_id t).const_mul (frequency d p z)).sin.const_mul
    (-coeffR p z * frequency d p z)).sub
    (((hasDerivAt_id t).const_mul (frequency d p z)).cos.const_mul
    (coeffI p z * frequency d p z)) using 1
  · rfl
  · dsimp; ring

theorem signalD2_hasDerivAt (d : Direction) (p : Fin 12) (t : ℝ) :
    HasDerivAt (signalD2 d p) (signalD3 d p t) t := by
  unfold signalD2 signalD3
  apply HasDerivAt.fun_sum
  intro z hz
  convert (((hasDerivAt_id t).const_mul (frequency d p z)).cos.const_mul
    (-coeffR p z * frequency d p z ^ 2)).add
    (((hasDerivAt_id t).const_mul (frequency d p z)).sin.const_mul
    (coeffI p z * frequency d p z ^ 2)) using 1
  · rfl
  · dsimp; ring

theorem signal_deriv (d : Direction) (p : Fin 12) : deriv (signal d p) = signalD1 d p :=
  funext fun t => (signal_hasDerivAt d p t).deriv

theorem signalD1_deriv (d : Direction) (p : Fin 12) : deriv (signalD1 d p) = signalD2 d p :=
  funext fun t => (signalD1_hasDerivAt d p t).deriv

theorem signalD2_deriv (d : Direction) (p : Fin 12) : deriv (signalD2 d p) = signalD3 d p :=
  funext fun t => (signalD2_hasDerivAt d p t).deriv

/-- 在基点邻域的实际分量相等，强制前三阶矩逐项相等。 -/
theorem moments_of_regular (d : Direction)
    (h : ∀ p, signal d p =ᶠ[𝓝 0] signal d 0) :
    (∀ p, moment1 d p = moment1 d 0) ∧
    (∀ p, moment2 d p = moment2 d 0) ∧
    (∀ p, moment3 d p = moment3 d 0) := by
  have h1 (p : Fin 12) : signalD1 d p =ᶠ[𝓝 0] signalD1 d 0 := by
    simpa only [signal_deriv] using (h p).deriv
  have h2 (p : Fin 12) : signalD2 d p =ᶠ[𝓝 0] signalD2 d 0 := by
    simpa only [signalD1_deriv] using (h1 p).deriv
  have h3 (p : Fin 12) : signalD3 d p =ᶠ[𝓝 0] signalD3 d 0 := by
    simpa only [signalD2_deriv] using (h2 p).deriv
  refine ⟨?_, ?_, ?_⟩
  · intro p
    simpa [signalD1, moment1] using (h1 p).eq_of_nhds
  · intro p
    simpa [signalD2, moment2] using (h2 p).eq_of_nhds
  · intro p
    simpa [signalD3, moment3] using (h3 p).eq_of_nhds


/-- 一阶矩方程的整个零空间，未预设相位分组。 -/
theorem kernel_of_moment1 (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, moment1 d p = moment1 d 0) :
    d = kernelDirection (d 1) (d 11) (d 6) (d 14) := by
  have h1 := h (1 : Fin 12)
  have h2 := h (2 : Fin 12)
  have h3 := h (3 : Fin 12)
  have h4 := h (4 : Fin 12)
  have h5 := h (5 : Fin 12)
  have h6 := h (6 : Fin 12)
  have h7 := h (7 : Fin 12)
  have h8 := h (8 : Fin 12)
  have h9 := h (9 : Fin 12)
  have h10 := h (10 : Fin 12)
  have h11 := h (11 : Fin 12)
  norm_num [moment1, frequency, coeffI, flip, Fin.sum_univ_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  funext z
  fin_cases z <;> simp [kernelDirection] <;> linarith

theorem second_Y1 (a b c k : ℝ) :
    moment2 (kernelDirection a b c k) 1 - moment2 (kernelDirection a b c k) 0 =
      -2*c*(2*a-c) := by
  norm_num [moment2, frequency, coeffR, coeffI, flip, kernelDirection, Fin.sum_univ_succ]
  <;> ring

theorem second_Y2 (a b c k : ℝ) :
    moment2 (kernelDirection a b c k) 4 - moment2 (kernelDirection a b c k) 0 =
      4*c*(a-2*b+2*c) := by
  norm_num [moment2, frequency, coeffR, coeffI, flip, kernelDirection, Fin.sum_univ_succ]
  <;> ring

theorem second_X2_obstruction (c k : ℝ) :
    moment2 (kernelDirection (c/2) (5*c/4) c k) 3 - moment2 (kernelDirection (c/2) (5*c/4) c k) 0 =
      -c*(c+4*k)/2 := by
  norm_num [moment2, frequency, coeffR, coeffI, flip, kernelDirection, Fin.sum_univ_succ]
  <;> ring

theorem third_Y1_obstruction (c : ℝ) :
    moment3 (kernelDirection (c/2) (5*c/4) c (-c/4)) 1 - moment3 (kernelDirection (c/2) (5*c/4) c (-c/4)) 0 =
      -39*c^3/8 := by
  norm_num [moment3, frequency, coeffR, coeffI, flip, kernelDirection, Fin.sum_univ_succ]
  <;> ring

theorem second_X2_final (a b k : ℝ) :
    moment2 (kernelDirection a b 0 k) 3 - moment2 (kernelDirection a b 0 k) 0 =
      -8*(a-b)*(a-b-k) := by
  norm_num [moment2, frequency, coeffR, coeffI, flip, kernelDirection, Fin.sum_univ_succ]
  <;> ring


/-- 三阶必要条件消去核中两个额外方向。 -/
theorem kernel_moments_force_planes (a b c k : ℝ)
    (h2 : ∀ p, moment2 (kernelDirection a b c k) p = moment2 (kernelDirection a b c k) 0)
    (h3 : ∀ p, moment3 (kernelDirection a b c k) p = moment3 (kernelDirection a b c k) 0) :
    c = 0 ∧ (b = a ∨ k = a - b) := by
  have e1 : -2*c*(2*a-c) = 0 := by
    rw [← second_Y1]; exact sub_eq_zero.mpr (h2 1)
  have e2 : 4*c*(a-2*b+2*c) = 0 := by
    rw [← second_Y2]; exact sub_eq_zero.mpr (h2 4)
  have hc : c = 0 := by
    by_contra hc
    have ha : a = c/2 := by
      have h := (mul_eq_zero.mp e1).resolve_left (mul_ne_zero (by norm_num) hc)
      linarith
    have hb : b = 5*c/4 := by
      have h := (mul_eq_zero.mp e2).resolve_left (mul_ne_zero (by norm_num) hc)
      linarith
    subst a; subst b
    have ek : -c*(c+4*k)/2 = 0 := by
      rw [← second_X2_obstruction]; exact sub_eq_zero.mpr (h2 3)
    have hk : k = -c/4 := by
      have hm : c*(c+4*k) = 0 := by linarith
      have hh := (mul_eq_zero.mp hm).resolve_left hc
      linarith
    subst k
    have ec : -39*c^3/8 = 0 := by
      rw [← third_Y1_obstruction]; exact sub_eq_zero.mpr (h3 1)
    have he : c^3 = 0 := by linarith
    exact hc (eq_zero_of_pow_eq_zero he)
  refine ⟨hc, ?_⟩
  subst c
  have ef : -8*(a-b)*(a-b-k) = 0 := by
    rw [← second_X2_final]; exact sub_eq_zero.mpr (h2 3)
  rcases mul_eq_zero.mp ef with h | h
  · left; rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · linarith
  · right; linarith

/-- 所有局部规则的实方向只能落在两个二维平面。 -/
theorem regular_direction_classified (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, signal d p =ᶠ[𝓝 0] signal d 0) :
    ∃ a b k : ℝ, d = kernelDirection a b 0 k ∧ (b = a ∨ k = a-b) := by
  obtain ⟨h1,h2,h3⟩ := moments_of_regular d h
  have hd := kernel_of_moment1 d h0 h1
  have hp := kernel_moments_force_planes (d 1) (d 11) (d 6) (d 14)
    (by simpa only [← hd] using h2) (by simpa only [← hd] using h3)
  refine ⟨d 1, d 11, d 14, ?_, hp.2⟩
  simpa only [hp.1] using hd


/-- 两个必要平面上，所有有限相位和都精确化为同一余弦。 -/
theorem signal_plane_one (a k t : ℝ) (p : Fin 12) :
    signal (kernelDirection a a 0 k) p t = 2 * Real.cos (a*t) := by
  fin_cases p <;>
    norm_num [signal, frequency, coeffR, coeffI, flip, kernelDirection, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [Real.cos_neg, Real.sin_neg] <;> ring

theorem signal_plane_two (a b t : ℝ) (p : Fin 12) :
    signal (kernelDirection a b 0 (a-b)) p t = 2 * Real.cos (a*t) := by
  fin_cases p <;>
    norm_num [signal, frequency, coeffR, coeffI, flip, kernelDirection, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [Real.cos_neg, Real.sin_neg] <;> ring

/-- 四比特所有局部规则实相位直线的全参数闭式。 -/
theorem regular_signal_cosine (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, signal d p =ᶠ[𝓝 0] signal d 0) :
    ∃ a : ℝ, ∀ p t, signal d p t = 2 * Real.cos (a*t) := by
  obtain ⟨a,b,k,hd,hb | hk⟩ := regular_direction_classified d h0 h
  · subst b; subst d
    exact ⟨a, fun p t => signal_plane_one a k t p⟩
  · subst k; subst d
    exact ⟨a, fun p t => signal_plane_two a b t p⟩

/-- 共同分量除以16恢复归一化后，绝对值不超过1/8。 -/
theorem regular_component_bound (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, signal d p =ᶠ[𝓝 0] signal d 0) (p : Fin 12) (t : ℝ) :
    |signal d p t / 16| ≤ 1/8 := by
  obtain ⟨a,ha⟩ := regular_signal_cosine d h0 h
  rw [ha]
  have hc := Real.abs_cos_le_one (a*t)
  rw [abs_div, abs_mul]
  norm_num
  linarith

end UnifiedEJM.LowDimensional


