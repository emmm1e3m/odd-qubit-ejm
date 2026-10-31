import UnifiedEJM.ThreeQubitModel

set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators Topology
open Filter
namespace UnifiedEJM.ThreeQubit

def zeroRe : Fin 8 → ℝ := ![1/2, 1/4, -1/4, 1/4, 1/4, 1/4, 1/4, 0]
def zeroIm : Fin 8 → ℝ := ![0, -1/4, 1/4, -1/4, 1/4, 1/4, 1/4, 0]
def derivReTable : Matrix (Fin 8) (Fin 7) ℝ := ![![0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, -1, 0], ![0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]]
def derivImTable : Matrix (Fin 8) (Fin 7) ℝ := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0]]
lemma ampRe_zero (j : Fin 8) : ampRe 0 j = zeroRe j := by
  fin_cases j <;> norm_num [ampRe, inputRe, phase, phaseLin,
    gate, baseRe, baseIm, zeroRe, Fin.sum_univ_succ]
lemma ampIm_zero (j : Fin 8) : ampIm 0 j = zeroIm j := by
  fin_cases j <;> norm_num [ampIm, inputIm, phase, phaseLin,
    gate, baseRe, baseIm, zeroIm, Fin.sum_univ_succ]
lemma realDeriv_apply (θ : Space) (j : Fin 8) :
    realDeriv j θ = (1/4:ℝ) * ∑ k, derivReTable j k * θ k := by
  fin_cases j <;> norm_num [realDeriv, gate, baseIm, phaseLin,
    derivReTable, Fin.sum_univ_succ, ContinuousLinearMap.sum_apply] <;> ring
lemma imagDeriv_apply (θ : Space) (j : Fin 8) :
    imagDeriv j θ = (1/4:ℝ) * ∑ k, derivImTable j k * θ k := by
  fin_cases j <;> norm_num [imagDeriv, gate, baseRe, phaseLin,
    derivImTable, Fin.sum_univ_succ, ContinuousLinearMap.sum_apply] <;> ring

/-- 论文给出的4DF(0)，由真实Pauli有限和计算得到。 -/
def jacobianMatrix : Matrix (Fin 7) (Fin 7) ℝ := ![![-2, -2, 0, 1, 1, 0, 2], ![-1, -2, 0, -1, 2, 2, 0], ![-1, -1, -1, 0, 1, 0, 1], ![-1, -1, -1, 0, 1, 1, 0], ![-1, -2, 0, 1, 0, 0, 2], ![-2, -1, 0, 1, 0, 0, 2], ![0, -2, -1, 1, 2, 0, 0]]
lemma jacobian_apply (θ : Space) (p : Fin 7) :
    jacobian θ p = (1/4:ℝ) * ∑ j, jacobianMatrix p j * θ j := by
  simp only [jacobian, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sub_apply,
    expectationDeriv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [ampRe_zero, ampIm_zero, realDeriv_apply, imagDeriv_apply]
  fin_cases p <;>
    norm_num [zeroRe, zeroIm, derivReTable, derivImTable, flip,
      pauliRe, pauliIm, jacobianMatrix, Fin.sum_univ_succ] <;> ring

/-- Jacobian的精确逆矩阵；全部元素为整数。 -/
def inverseMatrix : Matrix (Fin 7) (Fin 7) ℝ := ![![-10, 3, 2, -6, 1, 8, 4], ![-10, 3, 2, -6, -3, 12, 4], ![2, 1, -2, -2, -1, 0, 0], ![-6, 1, -2, -2, -1, 8, 4], ![-6, 3, 2, -6, -3, 8, 4], ![-12, 4, 0, -4, 0, 12, 4], ![-12, 4, 4, -8, 0, 12, 4]]
def inverseMap : Space →L[ℝ] Space := ContinuousLinearMap.pi
  (fun i => ∑ j, inverseMatrix i j • ContinuousLinearMap.proj j)
lemma inverseMap_apply (θ : Space) (i : Fin 7) :
    inverseMap θ i = ∑ j, inverseMatrix i j * θ j := by
  simp [inverseMap, ContinuousLinearMap.sum_apply]
lemma left_inverse (θ : Space) : inverseMap (jacobian θ) = θ := by
  funext i
  rw [inverseMap_apply]
  simp_rw [jacobian_apply]
  fin_cases i <;> norm_num [inverseMatrix, jacobianMatrix, Fin.sum_univ_succ] <;> ring
lemma right_inverse (θ : Space) : jacobian (inverseMap θ) = θ := by
  funext i
  rw [jacobian_apply]
  simp_rw [inverseMap_apply]
  fin_cases i <;> norm_num [inverseMatrix, jacobianMatrix, Fin.sum_univ_succ] <;> ring

def jacobianEquiv : Space ≃L[ℝ] Space :=
  ({ toFun := jacobian, invFun := inverseMap,
     left_inv := left_inverse, right_inv := right_inverse,
     map_add' := jacobian.map_add, map_smul' := jacobian.map_smul } :
       Space ≃ₗ[ℝ] Space).toContinuousLinearEquiv

/-- 由实际相位残差的严格导数和逆函数定理得到局部唯一性。 -/
theorem residual_locally_injective_at_zero :
    ∀ᶠ θ in 𝓝 (0 : Space), residual θ = residual 0 → θ = 0 := by
  have h : HasStrictFDerivAt residual (jacobianEquiv : Space →L[ℝ] Space) 0 :=
    residual_derivative
  filter_upwards [h.eventually_left_inverse] with θ hθ
  intro heq
  rw [heq, h.localInverse_apply_image] at hθ
  exact hθ.symm

lemma expectation_zero (p : Fin 9) : expectation 0 p = 1/4 := by
  fin_cases p <;> norm_num [expectation, ampRe, ampIm, inputRe, inputIm,
    phase, phaseLin, gate, baseRe, baseIm, flip, pauliRe, pauliIm, Fin.sum_univ_succ]
lemma residual_zero : residual 0 = 0 := by
  ext p
  simp [residual, expectation_zero]

/-- 固定Pauli轨道内，指定三比特点的signed规则性在七相位空间局部孤立。 -/
theorem signed_regularity_isolated :
    ∀ᶠ θ in 𝓝 (0 : Space),
      (∀ p, expectation θ p = expectation θ 0) → θ = 0 := by
  filter_upwards [residual_locally_injective_at_zero] with θ hθ
  intro hr
  apply hθ
  ext p
  simp [residual, hr, expectation_zero]

/-- 也覆盖用分量平方定义的规则性；在基点邻域符号由连续性固定。 -/
theorem regularity_isolated :
    ∀ᶠ θ in 𝓝 (0 : Space),
      (∀ p, expectation θ p ^ 2 = expectation θ 0 ^ 2) → θ = 0 := by
  have hp (p : Fin 9) : ∀ᶠ θ in 𝓝 (0 : Space), 0 < expectation θ p := by
    apply (expectation_derivative p).continuousAt.eventually
    apply eventually_gt_nhds
    simpa only [expectation_zero] using (by norm_num : (0:ℝ) < 1/4)
  filter_upwards [signed_regularity_isolated, Filter.eventually_all.mpr hp] with θ hθ hpos
  intro hr
  apply hθ
  intro p
  have hp' := hpos p
  have h0 := hpos 0
  have hs := hr p
  nlinarith

end UnifiedEJM.ThreeQubit
