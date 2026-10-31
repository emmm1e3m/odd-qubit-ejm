import UnifiedEJM.FourQubitMarginal

noncomputable section
open scoped BigOperators Matrix
open Complex
namespace UnifiedEJM.FiniteInvariants

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- 每一实际单比特偏迹的纯度，由原门振幅直接求和。 -/
theorem raw_single_purity (x : ℂ) (hu : x * star x = 1) (j : Fin 4) :
    UnifiedEJM.PurityInvariant.purity (reshape1 j (numerator159 x)) =
      512 + 6 * (x^6+2*x^4+2*x^2+1)^2 / x^6 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hu
  have hs : (starRingEnd ℂ) x = x⁻¹ := star_eq_inv x hu
  fin_cases j <;> simp only [single_purity_eq_sum] <;>
    simp [reshape1,numerator159,Fin.sum_univ_succ,
      star_add,star_sub,star_mul,star_pow,star_inv₀,hs,Complex.star_def] <;>
    field_simp [hx] <;> ring_nf <;>
    simp [Complex.I_sq,Complex.I_pow_three,Complex.I_pow_four] <;> ring

theorem single_purity_smul (A : Matrix (Fin 2) (Fin 8) ℂ) (s : ℂ) :
    UnifiedEJM.PurityInvariant.purity (s • A) =
      (s * star s)^2 * UnifiedEJM.PurityInvariant.purity A := by
  unfold UnifiedEJM.PurityInvariant.purity
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,Matrix.trace_smul,smul_eq_mul]
  ring

theorem singlePuritySum_smul (v : State) (s : ℂ) :
    singlePuritySum (fun k => s * v k) = (s * star s)^2 * singlePuritySum v := by
  have h (j : Fin 4) : reshape1 j (fun k => s * v k) = s • reshape1 j v := by
    fin_cases j <;> ext i l <;> fin_cases i <;> fin_cases l <;> rfl
  simp only [singlePuritySum,h,single_purity_smul,Finset.mul_sum]

end UnifiedEJM.FiniteInvariants
