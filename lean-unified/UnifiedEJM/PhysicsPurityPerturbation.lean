import UnifiedEJM.PhysicsPurityTail
import UnifiedEJM.PhysicsBackgroundOverlap

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix WithLp
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace UnifiedEJM.PurityTail

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- 只在第一子系统作用的真实张量积矩阵。 -/
def lift (R : Matrix α α ℂ) : Matrix (α × β) (α × β) ℂ :=
  R ⊗ₖ (1 : Matrix β β ℂ)

@[simp] theorem lift_add (R T : Matrix α α ℂ) :
    lift (β := β) (R + T) = lift R + lift T := Matrix.add_kronecker _ _ _

@[simp] theorem lift_sub (R T : Matrix α α ℂ) :
    lift (β := β) (R - T) = lift R - lift T := by
  ext i j
  simp [lift, Matrix.kroneckerMap, sub_mul]

@[simp] theorem lift_one : lift (β := β) (1 : Matrix α α ℂ) = 1 :=
  Matrix.one_kronecker_one

theorem lift_pos {R : Matrix α α ℂ} (hR : R.PosSemidef) :
    (lift (β := β) R).PosSemidef := hR.kronecker Matrix.PosSemidef.one

theorem lift_hermitian {R : Matrix α α ℂ} (hR : R.IsHermitian) :
    (lift (β := β) R).IsHermitian := by
  change (R ⊗ₖ (1 : Matrix β β ℂ))ᴴ = R ⊗ₖ (1 : Matrix β β ℂ)
  rw [Matrix.conjTranspose_kronecker, hR.eq, Matrix.conjTranspose_one]

theorem lift_centered_norm_le_one [Nonempty α] [Nonempty β]
    (R T : Matrix α α ℂ) (hR : R.PosSemidef) (hT : T.PosSemidef)
    (hr : R.trace = 1) (ht : T.trace = 1) :
    ‖lift (β := β) (R + T - 1)‖ ≤ 1 := by
  have hpos := (lift_pos (β := β) (hR.add hT)).nonneg
  have hRle : (1 - R).PosSemidef := density_le_one R hR hr
  have hTle : (1 - T).PosSemidef := density_le_one T hT ht
  have hneg := (lift_pos (β := β)
    (hRle.add hTle)).nonneg
  have hlo : (-1 : Matrix (α × β) (α × β) ℂ) ≤ lift (R + T - 1) := by
    simpa using sub_le_sub_right hpos 1
  have hhi : lift (β := β) (R + T - 1) ≤ 1 := by
    have he : lift (β := β) ((1 - R) + (1 - T)) =
        1 - lift (β := β) (R + T - 1) := by simp; abel
    rw [he] at hneg
    exact sub_nonneg.mp hneg
  have hh : (lift (β := β) (R + T - 1)).IsHermitian :=
    lift_hermitian (hR.1.add hT.1 |>.sub (by simp [Matrix.IsHermitian]))
  have hself : IsSelfAdjoint (lift (β := β) (R + T - 1)) := hh
  simpa using hself.norm_le_max_of_le_of_le hlo hhi

def vectorize (A : Matrix α β ℂ) : EuclideanSpace ℂ (α × β) :=
  toLp 2 (fun p => A p.1 p.2)

@[simp] theorem vectorize_add (A B : Matrix α β ℂ) :
    vectorize (A + B) = vectorize A + vectorize B := rfl

@[simp] theorem vectorize_sub (A B : Matrix α β ℂ) :
    vectorize (A - B) = vectorize A - vectorize B := rfl

theorem vectorize_inner (A B : Matrix α β ℂ) :
    inner ℂ (vectorize A) (vectorize B) = (B * Aᴴ).trace := by
  simp [vectorize, PiLp.inner_apply, RCLike.inner_apply, Matrix.trace,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]

theorem vectorize_lift (R : Matrix α α ℂ) (B : Matrix α β ℂ) :
    Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift (β := β) R) (vectorize B) = vectorize (R * B) := by
  apply (WithLp.equiv 2 (α × β → ℂ)).injective
  funext p
  simp [vectorize, lift, Matrix.mulVec, dotProduct, Matrix.kroneckerMap,
    Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply]

theorem vectorize_lift_inner (R : Matrix α α ℂ) (A B : Matrix α β ℂ) :
    inner ℂ (vectorize A) (Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift (β := β) R) (vectorize B)) =
      (R * B * Aᴴ).trace := by rw [vectorize_lift, vectorize_inner]

/-- 自伴收缩算符的纯态期望差，用和差向量的Cauchy界控制。 -/
theorem expectation_difference_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (H : E →L[ℂ] E)
    (hH : (H : E →ₗ[ℂ] E).IsSymmetric) (hnorm : ‖H‖ ≤ 1) (x y : E) :
    |(inner ℂ x (H x)).re - (inner ℂ y (H y)).re| ≤ ‖x + y‖ * ‖x - y‖ := by
  have hcross : (inner ℂ y (H x)).re = (inner ℂ x (H y)).re := by
    change RCLike.re (inner ℂ y (H x)) = RCLike.re (inner ℂ x (H y))
    rw [inner_re_symm (𝕜 := ℂ)]
    exact congrArg RCLike.re (hH x y)
  have he : (inner ℂ (x + y) (H (x - y))).re =
      (inner ℂ x (H x)).re - (inner ℂ y (H y)).re := by
    simp only [map_sub, inner_add_left, inner_sub_right, Complex.add_re,
      Complex.sub_re]
    linarith
  rw [← he]
  calc
    _ ≤ ‖inner ℂ (x + y) (H (x - y))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x + y‖ * ‖H (x - y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x + y‖ * (‖H‖ * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖x + y‖ * ‖x - y‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg (x-y))

theorem purity_difference_trace (A B : Matrix α β ℂ)
    (hA : (A * Aᴴ).trace = 1) (hB : (B * Bᴴ).trace = 1) :
    PurityInvariant.purity A - PurityInvariant.purity B =
      ((A * Aᴴ + B * Bᴴ - 1) * A * Aᴴ).trace -
        ((A * Aᴴ + B * Bᴴ - 1) * B * Bᴴ).trace := by
  simp only [PurityInvariant.purity, Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.trace_add, Matrix.trace_sub, hA, hB]
  have hcross := Matrix.trace_mul_comm (B * Bᴴ) (A * Aᴴ)
  simp only [Matrix.mul_assoc] at hcross
  rw [hcross]
  ring

/-- 对真实系数矩阵证明纯度扰动，不把偏迹收缩当作假设。 -/
theorem purity_difference_bound [Nonempty α] [Nonempty β]
    (A B : Matrix α β ℂ) (hA : (A * Aᴴ).trace = 1) (hB : (B * Bᴴ).trace = 1) :
    |(PurityInvariant.purity A).re - (PurityInvariant.purity B).re| ≤
      ‖vectorize A + vectorize B‖ * ‖vectorize A - vectorize B‖ := by
  let R := A * Aᴴ + B * Bᴴ - 1
  let H := Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift (β := β) R)
  have hherm : (lift (β := β) R).IsHermitian :=
    lift_hermitian ((Matrix.isHermitian_mul_conjTranspose_self A).add
      (Matrix.isHermitian_mul_conjTranspose_self B) |>.sub (by simp [Matrix.IsHermitian]))
  have hsym : H.toLinearMap.IsSymmetric := by
    dsimp [H]
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hherm
  have hn : ‖H‖ ≤ 1 := by
    change ‖Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift (β := β) R)‖ ≤ 1
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact lift_centered_norm_le_one _ _ (Matrix.posSemidef_self_mul_conjTranspose A)
      (Matrix.posSemidef_self_mul_conjTranspose B) hA hB
  have hb := expectation_difference_bound H hsym hn (vectorize A) (vectorize B)
  change |(inner ℂ (vectorize A) (Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift R) (vectorize A))).re -
    (inner ℂ (vectorize B) (Matrix.toEuclideanCLM (n := α × β) (𝕜 := ℂ) (lift R) (vectorize B))).re| ≤ _ at hb
  rw [vectorize_lift_inner, vectorize_lift_inner] at hb
  have he := congrArg Complex.re (purity_difference_trace A B hA hB)
  simp only [Complex.sub_re] at he
  change |((R * A * Aᴴ).trace).re - ((R * B * Bᴴ).trace).re| ≤ _ at hb
  rw [← he] at hb
  exact hb

/-- 重排后的Hilbert内积精确对应原物理振幅内积。 -/
theorem reshape_inner {n : ℕ} (S : Finset (Fin n)) (ψ φ : OddEJM.Vec n) :
    inner ℂ (vectorize (Multipartite.reshape S ψ))
      (vectorize (Multipartite.reshape S φ)) = OddEJM.inner ψ φ := by
  rw [vectorize_inner]
  unfold OddEJM.inner
  rw [← (Multipartite.split S).symm.sum_comp (fun z => star (ψ z) * φ z)]
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Multipartite.reshape]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem reshape_trace {n : ℕ} (S : Finset (Fin n)) (ψ : OddEJM.Vec n) :
    (Multipartite.reshape S ψ * (Multipartite.reshape S ψ)ᴴ).trace =
      OddEJM.inner ψ ψ := by rw [← vectorize_inner, reshape_inner]

theorem norm_sum_mul_norm_sub_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x y : E) (hx : ‖x‖ ^ 2 = 1) (hy : ‖y‖ ^ 2 = 1)
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (hov : 1 - 2*a ≤ (inner ℂ x y).re) :
    ‖x + y‖ * ‖x - y‖ ≤ 4 * Real.sqrt (a*(1-a)) := by
  have hp := norm_add_sq (𝕜 := ℂ) x y
  have hm := norm_sub_sq (𝕜 := ℂ) x y
  rw [hx,hy] at hp hm
  change ‖x + y‖ ^ 2 = 1 + 2 * (inner ℂ x y).re + 1 at hp
  change ‖x - y‖ ^ 2 = 1 - 2 * (inner ℂ x y).re + 1 at hm
  have hr : 0 ≤ (inner ℂ x y).re := by linarith
  have hc : 0 ≤ a*(1-a) := mul_nonneg ha (by linarith)
  have hs := Real.sq_sqrt hc
  have hs0 := Real.sqrt_nonneg (a*(1-a))
  have he : (‖x + y‖ * ‖x - y‖)^2 = 4 - 4*((inner ℂ x y).re)^2 := by
    rw [mul_pow, hp, hm]
    ring
  have hh : (1-2*a)^2 ≤ ((inner ℂ x y).re)^2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ 1-2*a) hr).2 hov
  have hp0 := mul_nonneg (norm_nonneg (x+y)) (norm_nonneg (x-y))
  nlinarith

/-- 任意实际物理割的sharp全态修正界。 -/
theorem actual_cutPurity_perturbation {n : ℕ} (hn : 1 ≤ n) (t : ℝ)
    (S : Finset (Fin n)) :
    |(Multipartite.cutPurity S (UnifiedEJM.seed n t)).re -
      (Multipartite.cutPurity S (backgroundSeed n t)).re| ≤
        4 * Real.sqrt (defectWeight n * (1 - defectWeight n)) := by
  let A := Multipartite.reshape S (UnifiedEJM.seed n t)
  let B := Multipartite.reshape S (backgroundSeed n t)
  have hA : (A * Aᴴ).trace = 1 := by
    rw [reshape_trace]
    exact actual_seed_normalized (by omega) t
  have hB : (B * Bᴴ).trace = 1 := by
    rw [reshape_trace]
    exact backgroundSeed_normalized (by omega) t
  have hx : ‖vectorize A‖^2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), vectorize_inner, hA]
    rfl
  have hy : ‖vectorize B‖^2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), vectorize_inner, hB]
    rfl
  have ha2 : defectWeight n ≤ 1/2 := by
    simpa [defectWeight] using defectWeight_le hn
  have hov : 1 - 2*defectWeight n ≤ (inner ℂ (vectorize A) (vectorize B)).re := by
    change 1 - 2*defectWeight n ≤ RCLike.re (inner ℂ (vectorize A) (vectorize B))
    rw [inner_re_symm (𝕜 := ℂ), reshape_inner]
    change 1 - 2*defectWeight n ≤ (OddEJM.inner (backgroundSeed n t) (seed n t)).re
    rw [background_seed_overlap_re (by omega)]
    have hs := mul_nonneg (defectWeight_pos n).le
      (show 0 ≤ 1 + Real.sin t by linarith [Real.neg_one_le_sin t])
    nlinarith
  exact (purity_difference_bound A B hA hB).trans
    (norm_sum_mul_norm_sub_bound _ _ hx hy _ (defectWeight_pos n).le ha2 hov)

/-- 背景上界3/8推出真实种子所有相应物理割的n≥10严格上界。 -/
theorem actual_cutPurity_lt_half {n : ℕ} (hn : 10 ≤ n) (t : ℝ)
    (S : Finset (Fin n))
    (hbg : (Multipartite.cutPurity S (backgroundSeed n t)).re ≤ 3/8) :
    (Multipartite.cutPurity S (UnifiedEJM.seed n t)).re < 1/2 := by
  have h := le_abs_self ((Multipartite.cutPurity S (UnifiedEJM.seed n t)).re -
    (Multipartite.cutPurity S (backgroundSeed n t)).re)
  have hp := actual_cutPurity_perturbation (by omega : 1 ≤ n) t S
  have ht := tail_scalar_lt_half hn
  linarith

end UnifiedEJM.PurityTail
