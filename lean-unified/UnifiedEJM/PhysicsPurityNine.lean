import UnifiedEJM.PhysicsPuritySqrtPerturbation

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix WithLp
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace UnifiedEJM.PurityTail

theorem cutPurity_re_nonneg {n : ℕ} (S : Finset (Fin n)) (ψ : OddEJM.Vec n) :
    0 ≤ (Multipartite.cutPurity S ψ).re :=
  trace_square_nonneg _
    (Matrix.isHermitian_mul_conjTranspose_self (Multipartite.reshape S ψ))

/-- 同相位实际态与背景的和差距离，直接复用已经证明的物理重叠。 -/
theorem actual_vector_sum_sub_bound {n : ℕ} (hn : 1 ≤ n) (t : ℝ)
    (S : Finset (Fin n)) :
    ‖vectorize (Multipartite.reshape S (seed n t)) +
        vectorize (Multipartite.reshape S (backgroundSeed n t))‖ *
      ‖vectorize (Multipartite.reshape S (seed n t)) -
        vectorize (Multipartite.reshape S (backgroundSeed n t))‖ ≤
      4 * Real.sqrt (defectWeight n * (1 - defectWeight n)) := by
  let A := Multipartite.reshape S (seed n t)
  let B := Multipartite.reshape S (backgroundSeed n t)
  have hA : (A * Aᴴ).trace = 1 := by
    rw [reshape_trace]
    exact actual_seed_normalized (by omega) t
  have hB : (B * Bᴴ).trace = 1 := by
    rw [reshape_trace]
    exact backgroundSeed_normalized (by omega) t
  have hx : ‖vectorize A‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), vectorize_inner, hA]
    rfl
  have hy : ‖vectorize B‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), vectorize_inner, hB]
    rfl
  have ha2 : defectWeight n ≤ 1 / 2 := by
    simpa [defectWeight] using defectWeight_le hn
  have hov : 1 - 2 * defectWeight n ≤ (inner ℂ (vectorize A) (vectorize B)).re := by
    change 1 - 2 * defectWeight n ≤ RCLike.re (inner ℂ (vectorize A) (vectorize B))
    rw [inner_re_symm (𝕜 := ℂ), reshape_inner]
    change 1 - 2 * defectWeight n ≤ (OddEJM.inner (backgroundSeed n t) (seed n t)).re
    rw [background_seed_overlap_re (by omega)]
    have hs := mul_nonneg (defectWeight_pos n).le
      (show 0 ≤ 1 + Real.sin t by linarith [Real.neg_one_le_sin t])
    nlinarith
  exact norm_sum_mul_norm_sub_bound _ _ hx hy _ (defectWeight_pos n).le ha2 hov

/-- 对原始物理态而非抽象替身给出纯度平方根扰动界。 -/
theorem actual_sqrt_cutPurity_perturbation {n : ℕ} (hn : 1 ≤ n) (t : ℝ)
    (S : Finset (Fin n)) :
    |Real.sqrt (Multipartite.cutPurity S (seed n t)).re -
      Real.sqrt (Multipartite.cutPurity S (backgroundSeed n t)).re| ≤
        2 * Real.sqrt (defectWeight n * (1 - defectWeight n)) := by
  let A := Multipartite.reshape S (seed n t)
  let B := Multipartite.reshape S (backgroundSeed n t)
  have hA : (A * Aᴴ).trace = 1 := by
    rw [reshape_trace]
    exact actual_seed_normalized (by omega) t
  have hB : (B * Bᴴ).trace = 1 := by
    rw [reshape_trace]
    exact backgroundSeed_normalized (by omega) t
  have hr := sqrt_purity_difference_bound A B hA hB
  have hd := actual_vector_sum_sub_bound hn t S
  change |Real.sqrt (Multipartite.cutPurity S (seed n t)).re -
    Real.sqrt (Multipartite.cutPurity S (backgroundSeed n t)).re| ≤
      ‖vectorize A + vectorize B‖ * ‖vectorize A - vectorize B‖ / 2 at hr
  change ‖vectorize A + vectorize B‖ * ‖vectorize A - vectorize B‖ ≤ _ at hd
  linarith

theorem actual_cutPurity_le_background_root_square {n : ℕ} (hn : 1 ≤ n) (t : ℝ)
    (S : Finset (Fin n)) :
    (Multipartite.cutPurity S (seed n t)).re ≤
      (Real.sqrt (Multipartite.cutPurity S (backgroundSeed n t)).re +
        2 * Real.sqrt (defectWeight n)) ^ 2 := by
  have hr := actual_sqrt_cutPurity_perturbation hn t S
  have hm : Real.sqrt (defectWeight n * (1 - defectWeight n)) ≤
      Real.sqrt (defectWeight n) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (defectWeight n)]
  have hle : Real.sqrt (Multipartite.cutPurity S (seed n t)).re ≤
      Real.sqrt (Multipartite.cutPurity S (backgroundSeed n t)).re +
        2 * Real.sqrt (defectWeight n) := by
    have hh := (abs_le.mp hr).2
    linarith
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (show 0 ≤ Real.sqrt (Multipartite.cutPurity S (backgroundSeed n t)).re +
      2 * Real.sqrt (defectWeight n) by positivity)).2 hle
  simpa only [Real.sq_sqrt (cutPurity_re_nonneg S (seed n t))] using hsq

/-- n=9的有理余量；交叉项平方为至多3/4096，小于(7/256)²。 -/
theorem root_square_nine_bound (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrsq : r ^ 2 ≤ 3 / 8) (hssq : s ^ 2 ≤ 1 / 512) :
    (r + 2 * s) ^ 2 ≤ 63 / 128 := by
  have hp : r ^ 2 * s ^ 2 ≤ (3 / 8 : ℝ) * (1 / 512) :=
    mul_le_mul hrsq hssq (sq_nonneg s) (by norm_num)
  have hcross : r * s ≤ (7 / 256 : ℝ) := by
    by_contra hnot
    have hbig : (7 / 256 : ℝ) < r * s := lt_of_not_ge hnot
    have hprod := mul_pos (show 0 < r * s - 7 / 256 by linarith)
      (show 0 < r * s + 7 / 256 by nlinarith [mul_nonneg hr hs])
    nlinarith
  nlinarith

theorem tail_root_square_le_sixtythree {n : ℕ} (hn : 9 ≤ n)
    (p : ℝ) (hp : 0 ≤ p) (hbg : p ≤ 3 / 8) :
    (Real.sqrt p + 2 * Real.sqrt (defectWeight n)) ^ 2 ≤ 63 / 128 := by
  have ha : defectWeight n ≤ (1 : ℝ) / 512 := by
    have h := defectWeight_le hn
    norm_num [defectWeight] at h ⊢
    exact h
  apply root_square_nine_bound _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · simpa only [Real.sq_sqrt hp] using hbg
  · simpa only [Real.sq_sqrt (defectWeight_pos n).le] using ha

/-- 实际seed与已定义backgroundSeed之间的n≥9严格半纯度界。 -/
theorem actual_cutPurity_lt_half_nine {n : ℕ} (hn : 9 ≤ n) (t : ℝ)
    (S : Finset (Fin n))
    (hbg : (Multipartite.cutPurity S (backgroundSeed n t)).re ≤ 3 / 8) :
    (Multipartite.cutPurity S (UnifiedEJM.seed n t)).re < 1 / 2 := by
  have hp := actual_cutPurity_le_background_root_square (by omega : 1 ≤ n) t S
  have ht := tail_root_square_le_sixtythree hn _
    (cutPurity_re_nonneg S (backgroundSeed n t)) hbg
  linarith

end UnifiedEJM.PurityTail
