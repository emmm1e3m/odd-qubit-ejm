import UnifiedEJM.PhysicsSmallBridge

open OddEJM Complex
open scoped BigOperators Matrix
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- 将双副本四重和重排为两个约化矩阵元之积；复杂度因此从4^n降到2^(n+k)。 -/
theorem matrix_swap_factor (v : ι → κ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      v a b * v c d * star (v a d) * star (v c b)) =
    ∑ a, ∑ c, (∑ b, v a b * star (v c b)) *
      (∑ d, v c d * star (v a d)) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- 分别检查每一个基向量的所属侧，足以推出所有双副本的真实物理拼接。 -/
theorem layout_splice {n : ℕ} (S : Finset (Fin n)) (e : ι × κ → Bits n)
    (a₀ : ι) (b₀ : κ)
    (hsep : ∀ a b j, e (a,b) j = if j ∈ S then e (a,b₀) j else e (a₀,b) j)
    (a c : ι) (b d : κ) :
    splice S (e (a,b)) (e (c,d)) = e (a,d) := by
  funext j
  by_cases hj : j ∈ S
  · simp only [splice, if_pos hj]
    rw [hsep a b j, hsep a d j]
    simp only [if_pos hj]
  · simp only [splice, if_neg hj]
    rw [hsep c d j, hsep a d j]
    simp only [if_neg hj]

/-- 该桥的左边是原相位加H/CNOT种子的实际偏迹纯度。 -/
theorem cut_laurent_layout {n : ℕ} (S : Finset (Fin n))
    (e : ι × κ ≃ Bits n) (A B : ι → κ → G)
    (hmix : ∀ a c b d, splice S (e (a,b)) (e (c,d)) = e (a,d))
    (hA : ∀ a b, coeffA UnifiedEJM.q (e (a,b)) = A a b)
    (hB : ∀ a b, coeffB UnifiedEJM.q (e (a,b)) = B a b)
    (u : ℂ) (hu : u * star u = 1) :
    Multipartite.cutPurity S (Physical.seed (UnifiedEJM.rawPhase u)) =
      (((2 : ℂ)^(n+1))⁻¹)^2 *
        laurentEval (traceCoeffs (reducedCoeffs A B)) u := by
  rw [Multipartite.cutPurity_eq_swap_sum]
  change swapPurity S (Physical.seed (UnifiedEJM.rawPhase u)) = _
  have hseed : Physical.seed (UnifiedEJM.rawPhase u) =
      fun z => scale n * ((coeffA UnifiedEJM.q z : ℂ) + u * (coeffB UnifiedEJM.q z : ℂ)) :=
    funext (physical_seed_affine u)
  rw [hseed, swapPurity_smul, scale_norm]
  congr 1
  unfold swapPurity
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [hmix, hA, hB]
  rw [matrix_swap_factor]
  simp_rw [reduced_affine A B _ _ u hu]
  exact trace_reduced (reducedCoeffs A B) u hu

end UnifiedEJM.PhysicsFinite
