import UnifiedEJM.LowDimensional
import UnifiedEJM.LowDimensionalPhysical

noncomputable section
namespace UnifiedEJM.LowDimensional
open OddEJM Complex Filter Topology
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem signal_continuous (d : Direction) (p : Fin 12) : Continuous (signal d p) := by
  unfold signal
  fun_prop

theorem signal_at_zero (d : Direction) (p : Fin 12) : signal d p 0 = 2 := by
  fin_cases p <;> norm_num [signal, coeffR, coeffI, Fin.sum_univ_succ]

/-- 基点的所有signed分量严格为正，因此平方规则性在邻域内等价于signed相等。 -/
theorem squared_signal_to_signed (d : Direction)
    (h : ∀ p, (fun t => (signal d p t)^2) =ᶠ[𝓝 0] (fun t => (signal d 0 t)^2)) :
    ∀ p, signal d p =ᶠ[𝓝 0] signal d 0 := by
  intro p
  have hp : 0 < signal d p 0 := by rw [signal_at_zero]; norm_num
  have hq : 0 < signal d 0 0 := by rw [signal_at_zero]; norm_num
  have hp' := (signal_continuous d p).continuousAt.eventually (lt_mem_nhds hp)
  have hq' := (signal_continuous d 0).continuousAt.eventually (lt_mem_nhds hq)
  filter_upwards [h p, hp', hq'] with t ht hpt hqt
  exact (sq_eq_sq₀ (le_of_lt hpt) (le_of_lt hqt)).mp ht

/-- 任意实相位方向的物理规则性强制两个已给出的方向平面。 -/
theorem physical_direction_classification (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, (fun t => (signedLocal (lineSeed d t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed d t) 0).re)) :
    ∃ a b k : ℝ, d = kernelDirection a b 0 k ∧ (b = a ∨ k = a-b) := by
  apply regular_direction_classified d h0
  intro p
  filter_upwards [h p] with t ht
  simp only [signed_lineSeed_signal] at ht
  linarith

def maskA : Direction := ![0,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0]
def maskB : Direction := ![0,1,1,1,0,0,0,0,1,1,0,0,0,0,1,1]
def maskC : Direction := ![0,0,0,0,1,1,0,0,0,0,0,0,0,0,1,1]

theorem kernel_plane_one_masks (a k : ℝ) :
    kernelDirection a a 0 k = fun z => a * maskA z + k * maskC z := by
  funext z
  fin_cases z <;> simp [kernelDirection, maskA, maskC]

theorem kernel_plane_two_masks (a b : ℝ) :
    kernelDirection a b 0 (a-b) = fun z => b * maskA z + (a-b) * maskB z := by
  funext z
  fin_cases z <;> simp [kernelDirection, maskA, maskB] <;> ring

theorem physical_direction_mask_planes (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, (fun t => (signedLocal (lineSeed d t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed d t) 0).re)) :
    (∃ a k : ℝ, d = fun z => a * maskA z + k * maskC z) ∨
    (∃ a b : ℝ, d = fun z => b * maskA z + (a-b) * maskB z) := by
  obtain ⟨a,b,k,hd,hb | hk⟩ := physical_direction_classification d h0 h
  · subst b
    exact Or.inl ⟨a,k,hd.trans (kernel_plane_one_masks a k)⟩
  · subst k
    exact Or.inr ⟨a,b,hd.trans (kernel_plane_two_masks a b)⟩

/-- 真实对角振幅单位模，供完整测量的通用正交与偏迹定理使用。 -/
theorem lineDiagonal_unit (d : Direction) (t : ℝ) (z : Bits 4) :
    star (lineDiagonal d t z) * lineDiagonal d t z = 1 := by
  have hb : ‖originalDiagonal z‖ = 1 := by
    rw [originalDiagonal_eq_rawPhase_zero (by norm_num)]
    exact rawPhase_angle_norm 0 z
  have hn : ‖lineDiagonal d t z‖ = 1 := by
    simp [lineDiagonal, norm_mul, hb]
  simpa only [Complex.star_def, hn, one_pow, Complex.ofReal_one] using
    Complex.conj_mul' (lineDiagonal d t z)

/-- 两平面条件也充分；并非仅是低阶必要条件的交集。 -/
theorem physical_regular_iff_planes (d : Direction) (h0 : d 0 = 0) :
    (∀ p, (fun t => (signedLocal (lineSeed d t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed d t) 0).re)) ↔
    (∃ a b k : ℝ, d = kernelDirection a b 0 k ∧ (b = a ∨ k = a-b)) := by
  constructor
  · exact physical_direction_classification d h0
  · rintro ⟨a,b,k,rfl,hb | hk⟩ p
    · subst b
      exact Filter.Eventually.of_forall fun t => by
        simp only [signed_lineSeed_signal, signal_plane_one]
    · subst k
      exact Filter.Eventually.of_forall fun t => by
        simp only [signed_lineSeed_signal, signal_plane_two]

/-- 四比特实际物理相位直线在邻域规则时，其每个实际signed分量均为余弦。 -/
theorem physical_regular_cosine (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, (fun t => (signedLocal (lineSeed d t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed d t) 0).re)) :
    ∃ a : ℝ, ∀ p t, (signedLocal (lineSeed d t) p).re = Real.cos (a*t)/8 := by
  have hs (p : Fin 12) : signal d p =ᶠ[𝓝 0] signal d 0 := by
    filter_upwards [h p] with t ht
    simp only [signed_lineSeed_signal] at ht
    linarith
  obtain ⟨a,ha⟩ := regular_signal_cosine d h0 hs
  refine ⟨a, fun p t => ?_⟩
  rw [signed_lineSeed_signal, ha]
  ring

def realBlochRadius (v : Vec 4) (j : Fin 4) : ℝ :=
  Real.sqrt ((localX v j).re ^ 2 + (localY v j).re ^ 2 + (localZ v j).re ^ 2)

theorem radius_of_signed (v : Vec 4) (m : ℝ)
    (h : ∀ p, (signedLocal v p).re = m) (j : Fin 4) :
    realBlochRadius v j = Real.sqrt 3 * |m| := by
  have hx0 := h (0 : Fin 12)
  have hy0 := h (1 : Fin 12)
  have hz0 := h (2 : Fin 12)
  have hx1 := h (3 : Fin 12)
  have hy1 := h (4 : Fin 12)
  have hz1 := h (5 : Fin 12)
  have hx2 := h (6 : Fin 12)
  have hy2 := h (7 : Fin 12)
  have hz2 := h (8 : Fin 12)
  have hx3 := h (9 : Fin 12)
  have hy3 := h (10 : Fin 12)
  have hz3 := h (11 : Fin 12)
  norm_num [signedLocal] at hx0 hy0 hz0 hx1 hy1 hz1 hx2 hy2 hz2 hx3 hy3 hz3
  have hy3' : (localY v 3).re = -m := by linarith
  have hsum : (localX v j).re ^ 2 + (localY v j).re ^ 2 + (localZ v j).re ^ 2 = 3*m^2 := by
    fin_cases j <;> simp_all <;> nlinarith
  unfold realBlochRadius
  rw [hsum, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq_eq_abs]

theorem physical_base_radius (d : Direction) (j : Fin 4) :
    realBlochRadius (lineSeed d 0) j = Real.sqrt 3 / 8 := by
  have h (p : Fin 12) : (signedLocal (lineSeed d 0) p).re = (1/8 : ℝ) := by
    rw [signed_lineSeed_signal, signal_at_zero]
    norm_num
  rw [radius_of_signed _ (1/8) h]
  norm_num
  ring

/-- 所有真实四比特实相位直线的半径上界；量词覆盖任意实方向。 -/
theorem physical_real_line_radius_bound (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, (fun t => (signedLocal (lineSeed d t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed d t) 0).re)) (j : Fin 4) (t : ℝ) :
    realBlochRadius (lineSeed d t) j ≤ Real.sqrt 3 / 8 := by
  obtain ⟨a,ha⟩ := physical_regular_cosine d h0 h
  rw [radius_of_signed _ (Real.cos (a*t)/8) (fun p => ha p t)]
  rw [abs_div]
  norm_num
  have hcos := Real.abs_cos_le_one (a*t)
  have hs := Real.sqrt_nonneg (3:ℝ)
  nlinarith [mul_le_mul_of_nonneg_left hcos hs]

/-- 也可直接从真实分量的平方规则条件导出同一半径界。 -/
theorem physical_squared_regular_radius_bound (d : Direction) (h0 : d 0 = 0)
    (h : ∀ p, (fun t => ((signedLocal (lineSeed d t) p).re)^2) =ᶠ[𝓝 0]
      (fun t => ((signedLocal (lineSeed d t) 0).re)^2)) (j : Fin 4) (t : ℝ) :
    realBlochRadius (lineSeed d t) j ≤ Real.sqrt 3 / 8 := by
  have hs : ∀ p, (fun t => (signal d p t)^2) =ᶠ[𝓝 0]
      (fun t => (signal d 0 t)^2) := by
    intro p
    filter_upwards [h p] with t ht
    simp only [signed_lineSeed_signal] at ht
    nlinarith
  apply physical_real_line_radius_bound d h0
  intro p
  filter_upwards [squared_signal_to_signed d hs p] with t ht
  simp only [signed_lineSeed_signal, ht]

def normalizedDirection (d : Direction) : Direction := fun z => d z - d 0

theorem signal_normalized_direction (d : Direction) (p : Fin 12) (t : ℝ) :
    signal (normalizedDirection d) p t = signal d p t := by
  unfold signal
  apply Finset.sum_congr rfl
  intro z hz
  have hf : frequency (normalizedDirection d) p z = frequency d p z := by
    simp only [frequency, normalizedDirection]
    ring
  rw [hf]

/-- 去掉整体相位规范后，对全部实方向仍成立。 -/
theorem physical_any_real_line_radius_bound (d : Direction)
    (h : ∀ p, (fun t => (signedLocal (lineSeed d t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed d t) 0).re)) (j : Fin 4) (t : ℝ) :
    realBlochRadius (lineSeed d t) j ≤ Real.sqrt 3 / 8 := by
  have hn (p : Fin 12) (t : ℝ) :
      (signedLocal (lineSeed (normalizedDirection d) t) p).re =
        (signedLocal (lineSeed d t) p).re := by
    simp only [signed_lineSeed_signal, signal_normalized_direction]
  have hr : ∀ p, (fun t => (signedLocal (lineSeed (normalizedDirection d) t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed (normalizedDirection d) t) 0).re) := by
    intro p
    simpa only [hn] using h p
  obtain ⟨a,ha⟩ := physical_regular_cosine (normalizedDirection d) (by simp [normalizedDirection]) hr
  have hx : ∀ p, (signedLocal (lineSeed d t) p).re = Real.cos (a*t)/8 := by
    intro p
    rw [← hn]
    exact ha p t
  rw [radius_of_signed _ (Real.cos (a*t)/8) hx]
  rw [abs_div]
  norm_num
  have hcos := Real.abs_cos_le_one (a*t)
  have hs := Real.sqrt_nonneg (3:ℝ)
  nlinarith [mul_le_mul_of_nonneg_left hcos hs]

end UnifiedEJM.LowDimensional



