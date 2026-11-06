import UnifiedEJM.PhysicsCoefficientsNew6
import UnifiedEJM.PhysicsCoefficientsPG6
import UnifiedEJM.PhysicsPairTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite

/-- 新族全部15个两体约化纯度之和的精确相位多项式。 -/
theorem new6_twoBody_laurent (t : ℝ) :
    Multipartite.twoBodyPurity (UnifiedEJM.seed 6 t) =
      (16384 : ℂ)⁻¹ * laurentEval new6PairCoeff (anglePhase t) := by
  rw [twoBodyPurity_canonical6]
  simp_rw [new6_cut_laurent]
  rw [← Finset.mul_sum, ← laurentEval_sum, new6_pair_coefficients]

/-- PG余弦族全部15个两体约化纯度之和使用同一归一化约定。 -/
theorem pg6_twoBody_laurent (t : ℝ) :
    Multipartite.twoBodyPurity (EvenFamily.seed 6 t 0) =
      (16384 : ℂ)⁻¹ * laurentEval pg6PairCoeff (anglePhase t) := by
  rw [twoBodyPurity_canonical6]
  simp_rw [pg6_cut_laurent]
  rw [← Finset.mul_sum, ← laurentEval_sum, pg6_pair_coefficients]

end UnifiedEJM.PhysicsFinite
