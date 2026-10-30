import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 固定四面体和实参数范围

所有定理只涉及明确给出的实向量和函数；与实际量子态的等式由物理态模块提供。
-/
namespace OddEJM.Geometry

open scoped BigOperators

noncomputable def radiusFormula (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt 3 * (1 - Real.sin t) / (2 : ℝ) ^ (n - 1)

noncomputable def radiusMax (n : ℕ) : ℝ := Real.sqrt 3 / (2 : ℝ) ^ (n - 2)

def parameterInterval : Set ℝ := Set.Icc (-(Real.pi / 2)) (Real.pi / 2)

lemma sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
lemma sqrt_three_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma radius_nonneg (n : ℕ) (t : ℝ) : 0 ≤ radiusFormula n t := by
  unfold radiusFormula
  positivity [sub_nonneg.mpr (Real.sin_le_one t)]

lemma radius_at_zero (n : ℕ) : radiusFormula n 0 = Real.sqrt 3 / (2 : ℝ) ^ (n - 1) := by
  simp [radiusFormula]

lemma radius_at_right (n : ℕ) : radiusFormula n (Real.pi / 2) = 0 := by
  simp [radiusFormula]

lemma pow_pred (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ (n - 2) * 2 := by
  rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]

lemma radius_at_left (n : ℕ) (hn : 2 ≤ n) :
    radiusFormula n (-(Real.pi / 2)) = radiusMax n := by
  simp only [radiusFormula, Real.sin_neg, Real.sin_pi_div_two]
  rw [pow_pred n hn]
  unfold radiusMax
  ring

lemma radius_max_eq_twice (n : ℕ) (hn : 2 ≤ n) :
    radiusMax n = 2 * (Real.sqrt 3 / (2 : ℝ) ^ (n - 1)) := by
  rw [pow_pred n hn]
  unfold radiusMax
  ring

lemma radius_le_max (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    radiusFormula n t ≤ radiusMax n := by
  rw [radius_max_eq_twice n hn]
  unfold radiusFormula
  have hsin := Real.neg_one_le_sin t
  have hs := sqrt_three_pos.le
  have hd : 0 < (2 : ℝ) ^ (n - 1) := by positivity
  apply (div_le_iff₀ hd).2
  field_simp
  nlinarith

lemma radius_strictAntiOn (n : ℕ) :
    StrictAntiOn (radiusFormula n) parameterInterval := by
  intro x hx y hy hxy
  have hsin := Real.strictMonoOn_sin hx hy hxy
  unfold radiusFormula
  apply div_lt_div_of_pos_right _ (by positivity)
  exact mul_lt_mul_of_pos_left (by linarith) sqrt_three_pos

lemma radius_image (n : ℕ) (hn : 2 ≤ n) :
    radiusFormula n '' parameterInterval = Set.Icc 0 (radiusMax n) := by
  apply Set.Subset.antisymm
  · rintro y ⟨t, ht, rfl⟩
    exact ⟨radius_nonneg n t, radius_le_max n hn t⟩
  · intro y hy
    have hd : 0 < (2 : ℝ) ^ (n - 1) := by positivity
    have hs : 0 < Real.sqrt (3 : ℝ) := sqrt_three_pos
    have hy' : y ≤ 2 * (Real.sqrt 3 / (2 : ℝ) ^ (n - 1)) := by
      simpa only [radius_max_eq_twice n hn] using hy.2
    have hyprod : y * (2 : ℝ) ^ (n - 1) ≤ 2 * Real.sqrt 3 := by
      apply (le_div_iff₀ hd).mp
      convert hy' using 1; ring
    have hz : 1 - y * (2 : ℝ) ^ (n - 1) / Real.sqrt 3 ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · have := (div_le_iff₀ hs).2 hyprod
        linarith
      · have : 0 ≤ y * (2 : ℝ) ^ (n - 1) / Real.sqrt 3 :=
          div_nonneg (mul_nonneg hy.1 hd.le) hs.le
        linarith
    obtain ⟨t, ht, hsin⟩ := Real.surjOn_sin hz
    refine ⟨t, ht, ?_⟩
    unfold radiusFormula
    rw [hsin]
    field_simp
    ring

lemma radius_nonconstant (n : ℕ) :
    ∃ t₁ ∈ parameterInterval, ∃ t₂ ∈ parameterInterval,
      radiusFormula n t₁ ≠ radiusFormula n t₂ := by
  refine ⟨0, ?_, Real.pi / 2, ?_, ?_⟩
  · constructor <;> linarith [Real.pi_pos]
  · constructor <;> linarith [Real.pi_pos]
  · rw [radius_at_zero, radius_at_right]
    exact ne_of_gt (div_pos sqrt_three_pos (by positivity))

lemma radius_le_one (n : ℕ) (hn : 5 ≤ n) (t : ℝ) : radiusFormula n t ≤ 1 := by
  apply (radius_le_max n (by omega) t).trans
  unfold radiusMax
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (n - 2))).2
  have hp : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (n - 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith [sqrt_three_sq, Real.sqrt_nonneg (3 : ℝ)]
  norm_num at hp ⊢
  linarith

/-- 标准 Pauli 符号；末位镜像由 ε=-1 表示。 -/
def signR (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

lemma signR_add (q s : ZMod 2) : signR (q + s) = signR q * signR s := by
  have cases₂ (b : ZMod 2) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases cases₂ q with rfl | rfl
  · simp [signR]
  · rcases cases₂ s with rfl | rfl
    · simp [signR]
    · change (1 : ℝ) = (-1) * (-1)
      norm_num
noncomputable def vertex (ε : ℝ) (q s : ZMod 2) : Fin 3 → ℝ :=
  ![signR q / Real.sqrt 3, ε * signR q * signR s / Real.sqrt 3,
    signR s / Real.sqrt 3]

def dot3 (v w : Fin 3 → ℝ) : ℝ := ∑ i, v i * w i

lemma vertex_dot (ε : ℝ) (hε : ε ^ 2 = 1) (q s q' s' : ZMod 2) :
    dot3 (vertex ε q s) (vertex ε q' s') =
      if q = q' ∧ s = s' then 1 else -(1 / 3 : ℝ) := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt sqrt_three_pos
  have cases₂ (b : ZMod 2) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases cases₂ q with rfl | rfl <;>
    rcases cases₂ s with rfl | rfl <;>
    rcases cases₂ q' with rfl | rfl <;>
    rcases cases₂ s' with rfl | rfl <;>
    norm_num [dot3, vertex, signR, Fin.sum_univ_three] <;>
    field_simp <;> nlinarith [sqrt_three_sq]

lemma vertex_unit (ε : ℝ) (hε : ε ^ 2 = 1) (q s : ZMod 2) :
    dot3 (vertex ε q s) (vertex ε q s) = 1 := by
  simpa using vertex_dot ε hε q s q s

lemma vertex_distinct_dot (ε : ℝ) (hε : ε ^ 2 = 1)
    (q s q' s' : ZMod 2) (h : (q, s) ≠ (q', s')) :
    dot3 (vertex ε q s) (vertex ε q' s') = -(1 / 3 : ℝ) := by
  rw [vertex_dot ε hε]
  have hh : ¬ (q = q' ∧ s = s') := by
    rintro ⟨rfl, rfl⟩
    exact h rfl
  simp [hh]

lemma vertex_injective (ε : ℝ) (hε : ε ^ 2 = 1) :
    Function.Injective (fun a : ZMod 2 × ZMod 2 => vertex ε a.1 a.2) := by
  intro a b hab
  change vertex ε a.1 a.2 = vertex ε b.1 b.2 at hab
  by_contra hne
  have hd := vertex_distinct_dot ε hε a.1 a.2 b.1 b.2 hne
  rw [hab, vertex_unit ε hε] at hd
  norm_num at hd

/-- 把实际三个 Pauli 分量与 r·v 的规范化联系起来。 -/
lemma radius_mul_vertex (n : ℕ) (t ε : ℝ) (q s : ZMod 2) :
    (fun k => radiusFormula n t * vertex ε q s k) =
      ![((1 - Real.sin t) / (2 : ℝ) ^ (n - 1)) * signR q,
        ((1 - Real.sin t) / (2 : ℝ) ^ (n - 1)) * ε * signR q * signR s,
        ((1 - Real.sin t) / (2 : ℝ) ^ (n - 1)) * signR s] := by
  have hs := ne_of_gt sqrt_three_pos
  funext k
  fin_cases k <;> simp [radiusFormula, vertex] <;> field_simp

lemma scaled_vertex_norm_sq (ε : ℝ) (hε : ε ^ 2 = 1) (q s : ZMod 2) (r : ℝ) :
    dot3 (fun k => r * vertex ε q s k) (fun k => r * vertex ε q s k) = r ^ 2 := by
  have h := vertex_unit ε hε q s
  unfold dot3 at h ⊢
  simp only [Fin.sum_univ_three] at h ⊢
  nlinarith [h]
/-- 代入共同半径后，与正文纯度公式中的幂次严格一致。 -/
lemma radius_purity_formula (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (1 + radiusFormula n t ^ 2) / 2 =
      1 / 2 + 3 * (1 - Real.sin t) ^ 2 / (2 : ℝ) ^ (2 * n - 1) := by
  have hp : (2 : ℝ) ^ (2 * n - 1) = ((2 : ℝ) ^ (n - 1)) ^ 2 * 2 := by
    rw [show 2 * n - 1 = (n - 1) * 2 + 1 by omega, pow_succ, pow_mul]
  unfold radiusFormula
  rw [hp]
  simp only [div_pow, mul_pow, sqrt_three_sq]
  field_simp
end OddEJM.Geometry









