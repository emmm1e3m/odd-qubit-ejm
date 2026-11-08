import UnifiedEJM.PhysicsPuritySqrtSpectral
import UnifiedEJM.PhysicsPurityPerturbation

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix WithLp
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace UnifiedEJM.PurityTail

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

@[simp] theorem lift_smul (c : ℂ) (R : Matrix α α ℂ) :
    lift (β := β) (c • R) = c • lift (β := β) R := Matrix.smul_kronecker _ _ _

/-- 用实际谱上界的中点居中，张量提升不损失常数。 -/
theorem lift_centered_norm_le_half_sum [Nonempty α] [Nonempty β]
    (R T : Matrix α α ℂ) (hR : R.PosSemidef) (hT : T.PosSemidef)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hRle : R ≤ (r : ℂ) • (1 : Matrix α α ℂ))
    (hTle : T ≤ (s : ℂ) • (1 : Matrix α α ℂ)) :
    ‖lift (β := β) (R + T - (((r + s) / 2 : ℝ) : ℂ) • 1)‖ ≤ (r + s) / 2 := by
  let c : ℝ := (r + s) / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpos := (lift_pos (β := β) (hR.add hT)).nonneg
  have hsum : R + T ≤ ((r + s : ℝ) : ℂ) • (1 : Matrix α α ℂ) := by
    simpa only [Complex.ofReal_add, add_smul] using add_le_add hRle hTle
  have hlift : lift (β := β) (R + T) ≤
      ((r + s : ℝ) : ℂ) • (1 : Matrix (α × β) (α × β) ℂ) := by
    have hh := lift_pos (β := β) (show
      (((r + s : ℝ) : ℂ) • (1 : Matrix α α ℂ) - (R + T)).PosSemidef from hsum)
    simpa only [lift_sub, lift_smul, lift_one, ← Matrix.le_iff] using hh
  have hlo : -((c : ℂ) • (1 : Matrix (α × β) (α × β) ℂ)) ≤
      lift (β := β) (R + T - (c : ℂ) • 1) := by
    simpa only [zero_sub, lift_sub, lift_smul, lift_one] using
      sub_le_sub_right hpos ((c : ℂ) • (1 : Matrix (α × β) (α × β) ℂ))
  have he : ((r + s : ℝ) : ℂ) • (1 : Matrix (α × β) (α × β) ℂ) -
      (c : ℂ) • 1 = (c : ℂ) • 1 := by
    rw [← sub_smul]
    congr 1
    dsimp [c]
    push_cast
    ring
  have hhi : lift (β := β) (R + T - (c : ℂ) • 1) ≤
      (c : ℂ) • (1 : Matrix (α × β) (α × β) ℂ) := by
    simpa only [lift_sub, lift_smul, lift_one, he] using
      sub_le_sub_right hlift ((c : ℂ) • (1 : Matrix (α × β) (α × β) ℂ))
  have hh : IsSelfAdjoint (lift (β := β) (R + T - (c : ℂ) • 1)) :=
    lift_hermitian (hR.1.add hT.1 |>.sub (by simp [Matrix.IsHermitian]))
  have hb := hh.norm_le_max_of_le_of_le hlo hhi
  simpa only [norm_neg, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc, max_self] using hb

/-- 原期望差证明的任意算子范数版本。 -/
theorem expectation_difference_bound_scaled {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) (c : ℝ) (hnorm : ‖H‖ ≤ c) (x y : E) :
    |(inner ℂ x (H x)).re - (inner ℂ y (H y)).re| ≤
      c * ‖x + y‖ * ‖x - y‖ := by
  have hcross : (inner ℂ y (H x)).re = (inner ℂ x (H y)).re := by
    change RCLike.re (inner ℂ y (H x)) = RCLike.re (inner ℂ x (H y))
    rw [inner_re_symm (𝕜 := ℂ)]
    exact congrArg RCLike.re (hH x y)
  have he : (inner ℂ (x + y) (H (x - y))).re =
      (inner ℂ x (H x)).re - (inner ℂ y (H y)).re := by
    simp only [map_sub, inner_add_left, inner_sub_right, Complex.add_re, Complex.sub_re]
    linarith
  rw [← he]
  calc
    _ ≤ ‖inner ℂ (x + y) (H (x - y))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x + y‖ * ‖H (x - y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x + y‖ * (‖H‖ * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖x + y‖ * (c * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- 归一化使任意标量中心在两态期望差中严格抵消。 -/
theorem purity_difference_trace_center (A B : Matrix α β ℂ)
    (hA : (A * Aᴴ).trace = 1) (hB : (B * Bᴴ).trace = 1) (c : ℂ) :
    PurityInvariant.purity A - PurityInvariant.purity B =
      ((A * Aᴴ + B * Bᴴ - c • 1) * A * Aᴴ).trace -
        ((A * Aᴴ + B * Bᴴ - c • 1) * B * Bᴴ).trace := by
  simp only [PurityInvariant.purity, Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul,
    smul_mul_assoc, Matrix.one_mul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, hA, hB, smul_eq_mul, mul_one]
  have hcross := Matrix.trace_mul_comm (B * Bᴴ) (A * Aᴴ)
  simp only [Matrix.mul_assoc] at hcross
  rw [hcross]
  ring

/-- 纯度差按两态纯度平方根之和收紧。 -/
theorem purity_difference_bound_sqrt_factor [Nonempty α] [Nonempty β]
    (A B : Matrix α β ℂ) (hA : (A * Aᴴ).trace = 1) (hB : (B * Bᴴ).trace = 1) :
    |(PurityInvariant.purity A).re - (PurityInvariant.purity B).re| ≤
      (Real.sqrt (PurityInvariant.purity A).re +
        Real.sqrt (PurityInvariant.purity B).re) / 2 *
          ‖vectorize A + vectorize B‖ * ‖vectorize A - vectorize B‖ := by
  let r := Real.sqrt (PurityInvariant.purity A).re
  let s := Real.sqrt (PurityInvariant.purity B).re
  let c := (r + s) / 2
  let R := A * Aᴴ + B * Bᴴ - (c : ℂ) • 1
  let H := Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift (β := β) R)
  have hherm : (lift (β := β) R).IsHermitian :=
    lift_hermitian ((Matrix.isHermitian_mul_conjTranspose_self A).add
      (Matrix.isHermitian_mul_conjTranspose_self B) |>.sub
        (by simp [Matrix.IsHermitian]))
  have hsym : H.toLinearMap.IsSymmetric := by
    dsimp [H]
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hherm
  have hn : ‖H‖ ≤ c := by
    change ‖Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift (β := β) R)‖ ≤ c
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact lift_centered_norm_le_half_sum _ _
      (Matrix.posSemidef_self_mul_conjTranspose A) (Matrix.posSemidef_self_mul_conjTranspose B)
      r s (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (density_le_sqrt_trace_square _ (Matrix.posSemidef_self_mul_conjTranspose A))
      (density_le_sqrt_trace_square _ (Matrix.posSemidef_self_mul_conjTranspose B))
  have hb := expectation_difference_bound_scaled H hsym c hn (vectorize A) (vectorize B)
  change |(inner ℂ (vectorize A) (Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ)
      (lift R) (vectorize A))).re -
    (inner ℂ (vectorize B) (Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ)
      (lift R) (vectorize B))).re| ≤ _ at hb
  rw [vectorize_lift_inner, vectorize_lift_inner] at hb
  have he := congrArg Complex.re (purity_difference_trace_center A B hA hB (c : ℂ))
  simp only [Complex.sub_re] at he
  change |((R * A * Aᴴ).trace).re - ((R * B * Bᴴ).trace).re| ≤ _ at hb
  rw [← he] at hb
  exact hb

/-- 消去r+s时不除以可能为零的数，因此也覆盖零纯度边界。 -/
theorem root_difference_of_square_difference (r s δ : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (h : |r ^ 2 - s ^ 2| ≤ (r + s) * δ / 2) : |r - s| ≤ δ / 2 := by
  apply abs_le.mpr
  constructor
  · by_contra hnot
    have hbig : r - s < -(δ / 2) := lt_of_not_ge hnot
    have hsum : 0 < r + s := by linarith
    have hp := mul_pos (show 0 < s - r - δ / 2 by linarith) hsum
    have hh := (abs_le.mp h).1
    nlinarith
  · by_contra hnot
    have hbig : δ / 2 < r - s := lt_of_not_ge hnot
    have hsum : 0 < r + s := by linarith
    have hp := mul_pos (show 0 < r - s - δ / 2 by linarith) hsum
    have hh := (abs_le.mp h).2
    nlinarith

/-- 任意归一化纯态系数矩阵的纯度平方根扰动界。 -/
theorem sqrt_purity_difference_bound [Nonempty α] [Nonempty β]
    (A B : Matrix α β ℂ) (hA : (A * Aᴴ).trace = 1) (hB : (B * Bᴴ).trace = 1) :
    |Real.sqrt (PurityInvariant.purity A).re -
      Real.sqrt (PurityInvariant.purity B).re| ≤
        ‖vectorize A + vectorize B‖ * ‖vectorize A - vectorize B‖ / 2 := by
  have ha : 0 ≤ (PurityInvariant.purity A).re :=
    trace_square_nonneg _ (Matrix.isHermitian_mul_conjTranspose_self A)
  have hb : 0 ≤ (PurityInvariant.purity B).re :=
    trace_square_nonneg _ (Matrix.isHermitian_mul_conjTranspose_self B)
  apply root_difference_of_square_difference _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
  convert purity_difference_bound_sqrt_factor A B hA hB using 1 <;> ring

end UnifiedEJM.PurityTail
