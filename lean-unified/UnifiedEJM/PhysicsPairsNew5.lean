import UnifiedEJM.PhysicsCoefficientsNew5
import UnifiedEJM.PhysicsPairTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite

theorem new5_twoBody_laurent (t : ℝ) :
    Multipartite.twoBodyPurity (UnifiedEJM.seed 5 t) =
      (4096 : ℂ)⁻¹ * laurentEval new5PairCoeff (anglePhase t) := by
  rw [twoBodyPurity_canonical5]
  simp_rw [new5_cut_laurent]
  rw [← Finset.mul_sum, ← laurentEval_sum, new5_pair_coefficients]

end UnifiedEJM.PhysicsFinite
