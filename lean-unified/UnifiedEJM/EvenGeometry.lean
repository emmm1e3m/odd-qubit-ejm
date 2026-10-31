import OddEJM.Geometry
import OddEJM.Phase
import Mathlib.Tactic

namespace UnifiedEJM.EvenEmbedding

open scoped BigOperators
open OddEJM

/-- 母族的非负半径参数域。 -/
def Omega : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ Real.pi / 2 ∧ -(Real.pi / 2) ≤ p.2 ∧
    p.2 ≤ Real.pi / 2 - |p.1|}

noncomputable def radius (n : ℕ) (α β : ℝ) : ℝ :=
  Real.sqrt 3 * (Real.cos α - Real.sin β) / (2 : ℝ) ^ (n - 1)

theorem omega_axis (β : ℝ) (hβ : β ∈ OddEJM.Geometry.parameterInterval) :
    (0, β) ∈ Omega := by
  rcases hβ with ⟨hl, hu⟩
  constructor
  · simp only [abs_zero]; positivity
  · simpa using And.intro hl hu

theorem omega_nonnegative {α β : ℝ} (h : (α, β) ∈ Omega) :
    0 ≤ Real.cos α - Real.sin β := by
  rcases h with ⟨hα, hβ, hu⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two hβ
    (show Real.pi / 2 - |α| ≤ Real.pi / 2 by linarith [abs_nonneg α]) hu
  rw [Real.sin_pi_div_two_sub, Real.cos_abs] at hs
  linarith

theorem radius_nonnegative {n : ℕ} {α β : ℝ} (h : (α, β) ∈ Omega) :
    0 ≤ radius n α β := by
  unfold radius
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (omega_nonnegative h)) (by positivity)

theorem radius_le_max (n : ℕ) (hn : 2 ≤ n) (α β : ℝ) :
    radius n α β ≤ OddEJM.Geometry.radiusMax n := by
  rw [OddEJM.Geometry.radius_max_eq_twice n hn]
  unfold radius
  have hbound : Real.cos α - Real.sin β ≤ 2 := by
    linarith [Real.cos_le_one α, Real.neg_one_le_sin β]
  have hm := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg 3)
  have hd : 0 < (2 : ℝ) ^ (n - 1) := by positivity
  apply (div_le_iff₀ hd).2
  calc
    Real.sqrt 3 * (Real.cos α - Real.sin β) ≤ Real.sqrt 3 * 2 := hm
    _ = 2 * (Real.sqrt 3 / (2 : ℝ) ^ (n - 1)) * (2 : ℝ) ^ (n - 1) := by
      field_simp

@[simp] theorem radius_second_axis (n : ℕ) (β : ℝ) :
    radius n 0 β = OddEJM.Geometry.radiusFormula n β := by
  simp [radius, OddEJM.Geometry.radiusFormula]

@[simp] theorem radius_first_axis (n : ℕ) (α : ℝ) :
    radius n α 0 = Real.sqrt 3 * Real.cos α / (2 : ℝ) ^ (n - 1) := by
  simp [radius]

/-- 整个五边形参数域的像由第二坐标截面已经取尽。 -/
theorem radius_image_exact (n : ℕ) (hn : 2 ≤ n) :
    (fun p : ℝ × ℝ => radius n p.1 p.2) '' Omega =
      Set.Icc 0 (OddEJM.Geometry.radiusMax n) := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨α, β⟩, h, rfl⟩
    exact ⟨radius_nonnegative h, radius_le_max n hn α β⟩
  · intro y hy
    rw [← OddEJM.Geometry.radius_image n hn] at hy
    obtain ⟨β, hβ, rfl⟩ := hy
    exact ⟨(0, β), omega_axis β hβ, radius_second_axis n β⟩

/-- 任意两值生成元的共同相位，直接定义实际对角输入。 -/
noncomputable def twoPhase {n : ℕ} (base : Vec n) (dA dB : Bits n → ℝ)
    (α β : ℝ) (z : Bits n) : ℂ :=
  base z * anglePhase (α * dA z + β * dB z)

@[simp] theorem twoPhase_first_axis {n : ℕ} (base : Vec n)
    (dA dB : Bits n → ℝ) (α : ℝ) :
    twoPhase base dA dB α 0 = fun z => base z * anglePhase (α * dA z) := by
  funext z; simp [twoPhase]

@[simp] theorem twoPhase_second_axis {n : ℕ} (base : Vec n)
    (dA dB : Bits n → ℝ) (β : ℝ) :
    twoPhase base dA dB 0 β = fun z => base z * anglePhase (β * dB z) := by
  funext z; simp [twoPhase]

theorem twoPhase_norm {n : ℕ} (base : Vec n) (dA dB : Bits n → ℝ)
    (hb : ∀ z, ‖base z‖ = 1) (α β : ℝ) (z : Bits n) :
    ‖twoPhase base dA dB α β z‖ = 1 := by
  simp [twoPhase, norm_mul, hb]

/-- 三个输入点的值排除两个相位方向模整体相位的线性相关。 -/
theorem phase_directions_independent {ι : Type*} (dA dB : ι → ℝ)
    (z₀ zA zB : ι) (h₀ : dA z₀ = 0 ∧ dB z₀ = 0)
    (hA : dA zA = 1 ∧ dB zA = 0) (hB : dA zB = 0 ∧ dB zB = 1)
    (a b c : ℝ) (h : ∀ z, a * dA z + b * dB z = c) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hz := h z₀
  have ha := h zA
  have hb := h zB
  simp only [h₀.1, h₀.2, hA.1, hA.2, hB.1, hB.2, mul_zero, mul_one,
    add_zero, zero_add] at hz ha hb
  exact ⟨ha.trans hz.symm, hb.trans hz.symm, hz.symm⟩

/-- 每个Hadamard矩阵元均非零时，逐列相位不能提供额外的对角自由度。 -/
theorem diagonal_column_gauge_scalar {ι κ : Type*} [Nonempty κ]
    (H : ι → κ → ℂ) (hH : ∀ z k, H z k ≠ 0)
    (a : ι → ℂ) (b : κ → ℂ)
    (h : ∀ z k, a z * H z k = H z k * b k) :
    ∃ c : ℂ, (∀ z, a z = c) := by
  obtain ⟨k⟩ := ‹Nonempty κ›
  refine ⟨b k, fun z => ?_⟩
  apply (mul_right_cancel₀ (hH z k))
  simpa [mul_comm] using h z k

end UnifiedEJM.EvenEmbedding
