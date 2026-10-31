import UnifiedEJM.LowDimensionalMain
import UnifiedEJM.Regularity

noncomputable section
namespace UnifiedEJM.LowDimensional
open OddEJM Filter Topology
set_option maxHeartbeats 1000000

/-- 方向和结果标签均不预先固定的真正四面体几何，在基点邻域成立。 -/
def GeometricLine (d : Direction) : Prop :=
  ∀ᶠ t in 𝓝 0, ∃ r : ℝ, Regularity.GeometricRegular (lineDiagonal d t) r

theorem kernel_satisfies_moment1 (a b c k : ℝ) (p : Fin 12) :
    moment1 (kernelDirection a b c k) p = moment1 (kernelDirection a b c k) 0 := by
  fin_cases p <;>
    norm_num [moment1, frequency, coeffI, flip, kernelDirection, Fin.sum_univ_succ] <;> ring

/-- 精确一阶核的充分和必要证书。 -/
theorem moment1_kernel_iff (d : Direction) (h0 : d 0 = 0) :
    (∀ p, moment1 d p = moment1 d 0) ↔ ∃ a b c k : ℝ, d = kernelDirection a b c k := by
  constructor
  · intro h
    exact ⟨d 1,d 11,d 6,d 14,kernel_of_moment1 d h0 h⟩
  · rintro ⟨a,b,c,k,rfl⟩ p
    exact kernel_satisfies_moment1 a b c k p

/-- 四个自由参数可从四个坐标唯一读出。 -/
theorem kernel_parameters_injective (a b c k a' b' c' k' : ℝ)
    (h : kernelDirection a b c k = kernelDirection a' b' c' k') :
    a = a' ∧ b = b' ∧ c = c' ∧ k = k' := by
  have h1 := congrFun h (1 : Fin 16)
  have h11 := congrFun h (11 : Fin 16)
  have h6 := congrFun h (6 : Fin 16)
  have h14 := congrFun h (14 : Fin 16)
  norm_num [kernelDirection] at h1 h11 h6 h14
  exact ⟨h1,h11,h6,h14⟩

theorem geometric_line_squared (d : Direction) (h : GeometricLine d) :
    ∀ p, (fun t => ((signedLocal (lineSeed d t) p).re)^2) =ᶠ[𝓝 0]
      (fun t => ((signedLocal (lineSeed d t) 0).re)^2) := by
  intro p
  filter_upwards [h] with t ht
  obtain ⟨r,hr⟩ := ht
  have hs (j : Fin 4) := Regularity.geometric_seed_squares (by norm_num : 2 ≤ 4) hr j
  change ∀ j : Fin 4, (localX (lineSeed d t) j).re^2 = r^2/3 ∧
    (localY (lineSeed d t) j).re^2 = r^2/3 ∧
    (localZ (lineSeed d t) j).re^2 = r^2/3 at hs
  obtain ⟨hx0,hy0,hz0⟩ := hs 0
  obtain ⟨hx1,hy1,hz1⟩ := hs 1
  obtain ⟨hx2,hy2,hz2⟩ := hs 2
  obtain ⟨hx3,hy3,hz3⟩ := hs 3
  fin_cases p <;> norm_num [signedLocal] <;> nlinarith

theorem geometric_line_signed (d : Direction) (h : GeometricLine d) :
    ∀ p, (fun t => (signedLocal (lineSeed d t) p).re) =ᶠ[𝓝 0]
      (fun t => (signedLocal (lineSeed d t) 0).re) := by
  have hs : ∀ p, (fun t => (signal d p t)^2) =ᶠ[𝓝 0]
      (fun t => (signal d 0 t)^2) := by
    intro p
    filter_upwards [geometric_line_squared d h p] with t ht
    simp only [signed_lineSeed_signal] at ht
    nlinarith
  intro p
  filter_upwards [squared_signal_to_signed d hs p] with t ht
  simp only [signed_lineSeed_signal, ht]

theorem geometric_line_direction_planes (d : Direction) (h0 : d 0 = 0)
    (h : GeometricLine d) :
    (∃ a k : ℝ, d = fun z => a * maskA z + k * maskC z) ∨
    (∃ a b : ℝ, d = fun z => b * maskA z + (a-b) * maskB z) :=
  physical_direction_mask_planes d h0 (geometric_line_signed d h)

theorem geometric_of_common_signed (d : Direction) (t m : ℝ)
    (h : ∀ p, (signedLocal (lineSeed d t) p).re = m) :
    Regularity.GeometricRegular (lineDiagonal d t) (Real.sqrt 3 * |m|) := by
  apply (Regularity.geometric_iff_seed_squares (by norm_num : 2 ≤ 4) _ _).mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _), ?_⟩
  intro j
  have hr : (Real.sqrt 3 * |m|)^2 / 3 = m^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), sq_abs]
    ring
  rw [hr]
  change (localX (lineSeed d t) j).re^2 = m^2 ∧
    (localY (lineSeed d t) j).re^2 = m^2 ∧ (localZ (lineSeed d t) j).re^2 = m^2
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
  have hy3' : (localY (lineSeed d t) 3).re = -m := by linarith
  fin_cases j <;> simp_all

/-- 用真实几何作输入和输出的完整两平面分类。 -/
theorem geometric_line_iff_planes (d : Direction) (h0 : d 0 = 0) :
    GeometricLine d ↔ ∃ a b k : ℝ, d = kernelDirection a b 0 k ∧ (b = a ∨ k = a-b) := by
  constructor
  · intro h
    exact physical_direction_classification d h0 (geometric_line_signed d h)
  · rintro ⟨a,b,k,rfl,hb | hk⟩
    · subst b
      apply Filter.Eventually.of_forall
      intro t
      refine ⟨Real.sqrt 3 * |Real.cos (a*t)/8|, geometric_of_common_signed _ t _ ?_⟩
      intro p
      rw [signed_lineSeed_signal, signal_plane_one]
      ring
    · subst k
      apply Filter.Eventually.of_forall
      intro t
      refine ⟨Real.sqrt 3 * |Real.cos (a*t)/8|, geometric_of_common_signed _ t _ ?_⟩
      intro p
      rw [signed_lineSeed_signal, signal_plane_two]
      ring

theorem radius_eq_realBlochRadius (d : Direction) (t : ℝ) (j : Fin 4) :
    Regularity.radius (Physical.seed (lineDiagonal d t)) j = realBlochRadius (lineSeed d t) j := by
  simp [Regularity.radius, Regularity.dot3, Regularity.bloch, realBlochRadius,
    lineSeed, Physical.seed, pow_two]

/-- 任意实方向、任意测量列及任意物理比特：规则直线不能超过指定基点半径。 -/
theorem geometric_real_line_measurement_radius_bound (d : Direction) (h : GeometricLine d)
    (label : Bits 4) (j : Fin 4) (t : ℝ) :
    Regularity.radius (Physical.measurement (lineDiagonal d t) label) j ≤ Real.sqrt 3 / 8 := by
  rw [Regularity.measurement_radius (by norm_num : 0 < 4), radius_eq_realBlochRadius]
  exact physical_any_real_line_radius_bound d (geometric_line_signed d h) j t

end UnifiedEJM.LowDimensional
