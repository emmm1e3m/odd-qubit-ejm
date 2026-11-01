import UnifiedEJM.SixMeasurement
import UnifiedEJM.Regularity

/-! 六比特四颜色模型的一般几何条件与局部交叉之间的桥。 -/
noncomputable section
namespace UnifiedEJM.SixFamily

open OddEJM Complex
open UnifiedEJM.SixCertificate
open scoped Topology

/-- 最后一位的 Y 符号在平方条件中消失。 -/
lemma actual_Y_sq (j : Fin 6) (α β γ φ : ℝ) :
    (localY (seed α β γ φ) j).re ^ 2 = (total (rowY j) α β γ φ / 64) ^ 2 := by
  have hy := congrArg (fun z : ℂ => z.re ^ 2) (actual_Y j α β γ φ)
  by_cases hj : j.val = 5
  · simp only [hj, ite_true, Complex.neg_re, Complex.ofReal_re] at hy
    nlinarith [hy]
  · simpa [hj] using hy

/-- 不预设顶点方向的真实几何条件控制全部十八个 signed 分量的平方。 -/
lemma geometric_total_squares {α β γ φ r : ℝ}
    (h : Regularity.GeometricRegular (diagonal α β γ φ) r) (p : Fin 18) :
    (total p α β γ φ / 64) ^ 2 = r ^ 2 / 3 := by
  have hs (j : Fin 6) := Regularity.geometric_seed_squares (by omega : 2 ≤ 6) h j
  change ∀ j : Fin 6,
    (localX (seed α β γ φ) j).re ^ 2 = r ^ 2 / 3 ∧
    (localY (seed α β γ φ) j).re ^ 2 = r ^ 2 / 3 ∧
    (localZ (seed α β γ φ) j).re ^ 2 = r ^ 2 / 3 at hs
  simp only [actual_X, actual_Y_sq, actual_Z, Complex.ofReal_re] at hs
  rcases rows_cover p with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (hs j).1
  · exact (hs j).2.1
  · exact (hs j).2.2

/-- 全部 signed 分量为正时，方向自由的共同半径四面体条件等价于等分量。 -/
theorem geometric_iff_actual_of_pos {α β γ φ : ℝ}
    (hpos : ∀ p : Fin 18, 0 < total p α β γ φ) :
    (∃ r : ℝ, Regularity.GeometricRegular (diagonal α β γ φ) r) ↔
      ActualRegular (seed α β γ φ) := by
  constructor
  · rintro ⟨r, hg⟩
    apply (actual_regular_iff_table α β γ φ).mpr
    intro p
    have hp := hpos p
    have h0 := hpos 0
    have he : total p α β γ φ / 64 = total 0 α β γ φ / 64 :=
      (sq_eq_sq₀ (by positivity) (by positivity)).mp
        ((geometric_total_squares hg p).trans (geometric_total_squares hg 0).symm)
    linarith
  · intro h
    have ht := (actual_regular_iff_table α β γ φ).mp h
    refine ⟨Real.sqrt 3 * (total 0 α β γ φ / 64),
      (Regularity.geometric_iff_seed_squares (by omega : 2 ≤ 6) _ _).mpr ⟨?_, ?_⟩⟩
    · have hp := hpos 0
      positivity
    · intro j
      change (localX (seed α β γ φ) j).re ^ 2 = _ ∧
        (localY (seed α β γ φ) j).re ^ 2 = _ ∧
        (localZ (seed α β γ φ) j).re ^ 2 = _
      simp only [actual_X, actual_Y_sq, actual_Z, Complex.ofReal_re, ht,
        mul_pow, Geometry.sqrt_three_sq]
      constructor
      · ring
      constructor <;> ring

/-- 四相位参数的物理原点。 -/
def phaseOrigin : Fin 4 → ℝ := ![0, 0, 0, Real.pi / 2]

lemma continuous_total (p : Fin 18) :
    Continuous (fun x : Fin 4 → ℝ => total p (x 0) (x 1) (x 2) (x 3)) := by
  unfold total backgroundTable defect
  split_ifs <;>
    simp only [backgroundX, backgroundY, backgroundZ, SixLocal.defectI, SixLocal.defectII] <;>
    fun_prop

lemma total_phaseOrigin (p : Fin 18) :
    total p (phaseOrigin 0) (phaseOrigin 1) (phaseOrigin 2) (phaseOrigin 3) = 2 := by
  simp only [phaseOrigin, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  unfold total backgroundTable defect
  split_ifs <;>
    norm_num [backgroundX, backgroundY, backgroundZ, SixLocal.defectI, SixLocal.defectII]

/-- 连续性在物理原点附近同时保留全部十八个 signed 分量的正号。 -/
lemma eventually_total_pos :
    ∀ᶠ x : Fin 4 → ℝ in 𝓝 phaseOrigin,
      ∀ p : Fin 18, 0 < total p (x 0) (x 1) (x 2) (x 3) := by
  apply Filter.eventually_all.mpr
  intro p
  exact continuous_const.continuousAt.eventually_lt (continuous_total p).continuousAt
    (by rw [total_phaseOrigin]; norm_num)

/-- 在某个真实开邻域内，一般四面体几何恰好由两条相交支给出。
该命题没有额外正性假设，也不声称整个 π/12 坐标盒均满足几何等价。 -/
theorem geometric_local_crossing :
    ∃ U : Set (Fin 4 → ℝ), IsOpen U ∧ phaseOrigin ∈ U ∧
      ∀ x ∈ U,
        (∃ r : ℝ, Regularity.GeometricRegular (diagonal (x 0) (x 1) (x 2) (x 3)) r) ↔
          (((x 1 = 0 ∧ x 2 = x 0) ∨ (x 0 = 0 ∧ x 2 = x 1)) ∧
            x 3 = Real.pi / 2) := by
  have hbox : ∀ᶠ x : Fin 4 → ℝ in 𝓝 phaseOrigin,
      ∀ i : Fin 4, |x i - phaseOrigin i| < Real.pi / 12 := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun x : Fin 4 → ℝ => |x i - phaseOrigin i|) := by fun_prop
    exact hc.continuousAt.eventually_lt continuous_const.continuousAt
      (by simp; positivity)
  have he : ∀ᶠ x : Fin 4 → ℝ in 𝓝 phaseOrigin,
      (∃ r : ℝ, Regularity.GeometricRegular (diagonal (x 0) (x 1) (x 2) (x 3)) r) ↔
        (((x 1 = 0 ∧ x 2 = x 0) ∨ (x 0 = 0 ∧ x 2 = x 1)) ∧
          x 3 = Real.pi / 2) := by
    filter_upwards [eventually_total_pos, hbox] with x hp hb
    have h0 : |x 0| ≤ Real.pi / 12 := by simpa [phaseOrigin] using (hb 0).le
    have h1 : |x 1| ≤ Real.pi / 12 := by simpa [phaseOrigin] using (hb 1).le
    have h2 : |x 2| ≤ Real.pi / 12 := by simpa [phaseOrigin] using (hb 2).le
    have h3 : |x 3 - Real.pi / 2| ≤ Real.pi / 12 := by
      simpa [phaseOrigin] using (hb 3).le
    exact (geometric_iff_actual_of_pos hp).trans (actual_local_crossing h0 h1 h2 h3)
  obtain ⟨U, hU, ho, hb⟩ := eventually_nhds_iff.mp he
  exact ⟨U, ho, hb, hU⟩

end UnifiedEJM.SixFamily
