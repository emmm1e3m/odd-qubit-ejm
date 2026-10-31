import UnifiedEJM.BasepointInvariants
import UnifiedEJM.FiniteInvariants

noncomputable section
open scoped BigOperators Matrix
open Complex
namespace UnifiedEJM.FiniteInvariants
open UnifiedEJM.Inequivalence

theorem line_pair_purity (x : ℂ) (hu : x * star x = 1) :
    sumPurity (state159 x) = puritySumFormula x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hu
  unfold state159
  rw [sumPurity_smul,normalization_norm,raw_purity_sum x hu]
  unfold puritySumFormula
  field_simp [hx]
  ring

theorem line_single_purity (x : ℂ) (hu : x * star x = 1) :
    singlePuritySum (state159 x) = 2 + 6 * commonComponent x ^ 2 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hu
  unfold state159
  rw [singlePuritySum_smul,normalization_norm]
  simp only [singlePuritySum,raw_single_purity x hu,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold commonComponent
  field_simp [hx]
  ring

/-- 真实单体和二体偏迹两个不变量不能同时等于指定基点。 -/
theorem no_matching_actual_invariants (x : ℂ) (hu : x * star x = 1) :
    ¬ (singlePuritySum (state159 x) = singlePuritySum stateBase ∧
      sumPurity (state159 x) = sumPurity stateBase) := by
  rintro ⟨h1,h2⟩
  rw [line_single_purity x hu,base_single_purity] at h1
  rw [line_pair_purity x hu,base_pair_purity] at h2
  have hc : commonComponent x ^ 2 = (1/8 : ℂ)^2 := by
    linear_combination (1/6 : ℂ) * h1
  have hs : commonComponent x = (1/8 : ℂ) ∨ commonComponent x = -(1/8 : ℂ) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hc
  have hx : x ≠ 0 := by intro h; simp [h] at hu
  exact no_matching_formulas x hx hs h2

end UnifiedEJM.FiniteInvariants
