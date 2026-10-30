import OddEJM.Density
import OddEJM.Geometry
import OddEJM.Orthonormal

namespace OddEJM
open scoped BigOperators

/-- 仅最后一个物理位采用Y轴镜像。 -/
def localOrientation {n : ℕ} (j : Fin n) : ℝ :=
  if j.val = n - 1 then -1 else 1

theorem localOrientation_sq {n : ℕ} (j : Fin n) : localOrientation j ^ 2 = 1 := by
  unfold localOrientation
  split_ifs <;> norm_num

theorem radius_eq_geometry (n : ℕ) (t : ℝ) : radius n t = Geometry.radiusFormula n t := by
  unfold radius componentScale Geometry.radiusFormula
  ring

theorem bitSign_eq_real (b : Bit) : bitSign b = (Geometry.signR b : ℂ) := by
  simp only [bitSign, Geometry.signR]
  split_ifs <;> simp

/-- Geometry的r·v恒等式直接连接到Core的共同半径和分量尺度。 -/
theorem radius_vertex_components (n : ℕ) (t ε : ℝ) (q s : Bit) :
    (fun k => radius n t * Geometry.vertex ε q s k) =
      ![componentScale n t * Geometry.signR q,
        componentScale n t * ε * Geometry.signR q * Geometry.signR s,
        componentScale n t * Geometry.signR s] := by
  simpa only [radius_eq_geometry, componentScale] using Geometry.radius_mul_vertex n t ε q s

/-- 固定局部四面体的四个单位方向。 -/
theorem local_vertices_unit {n : ℕ} (j : Fin n) (q s : Bit) :
    Geometry.dot3 (Geometry.vertex (localOrientation j) q s)
      (Geometry.vertex (localOrientation j) q s) = 1 :=
  Geometry.vertex_unit _ (localOrientation_sq j) q s

theorem local_vertices_distinct_dot {n : ℕ} (j : Fin n) (a b : Bit × Bit) (hab : a ≠ b) :
    Geometry.dot3 (Geometry.vertex (localOrientation j) a.1 a.2)
      (Geometry.vertex (localOrientation j) b.1 b.2) = -(1 / 3 : ℝ) :=
  Geometry.vertex_distinct_dot _ (localOrientation_sq j) a.1 a.2 b.1 b.2 hab

theorem local_vertices_injective {n : ℕ} (j : Fin n) :
    Function.Injective (fun a : Bit × Bit => Geometry.vertex (localOrientation j) a.1 a.2) :=
  Geometry.vertex_injective _ (localOrientation_sq j)

/-- 实单位顶点嵌入复数后可直接作为真实偏迹纯度定理的输入。 -/
theorem local_vertex_complex_unit {n : ℕ} (j : Fin n) (q s : Bit) :
    (Geometry.vertex (localOrientation j) q s 0 : ℂ) ^ 2 +
      (Geometry.vertex (localOrientation j) q s 1 : ℂ) ^ 2 +
      (Geometry.vertex (localOrientation j) q s 2 : ℂ) ^ 2 = 1 := by
  have h := local_vertices_unit j q s
  simp only [Geometry.dot3, Fin.sum_univ_three, ← pow_two] at h
  exact_mod_cast h

theorem measurement_normalized {n : ℕ} (hn : 0 < n) (t : ℝ) (label : Bits n) :
    inner (measurement n t label) (measurement n t label) = 1 := by
  simpa using measurement_orthonormal hn t label label

/-- Core共同半径在闭参数区间上的精确像集。 -/
theorem radius_image_exact {n : ℕ} (hn : 2 ≤ n) :
    radius n '' Geometry.parameterInterval = Set.Icc 0 (Geometry.radiusMax n) := by
  simpa only [radius_eq_geometry] using Geometry.radius_image n hn

theorem radius_bounds {n : ℕ} (hn : 5 ≤ n) (t : ℝ) :
    0 ≤ radius n t ∧ radius n t ≤ 1 := by
  rw [radius_eq_geometry]
  exact ⟨Geometry.radius_nonneg n t, Geometry.radius_le_one n hn t⟩

theorem radius_continuous (n : ℕ) : Continuous (radius n) := by
  unfold radius componentScale
  fun_prop

theorem radius_strict_decreasing (n : ℕ) :
    StrictAntiOn (radius n) Geometry.parameterInterval := by
  intro x hx y hy hxy
  rw [radius_eq_geometry, radius_eq_geometry]
  exact Geometry.radius_strictAntiOn n hx hy hxy

end OddEJM
