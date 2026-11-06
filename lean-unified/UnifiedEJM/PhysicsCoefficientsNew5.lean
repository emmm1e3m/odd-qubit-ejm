import UnifiedEJM.PhysicsCoeffNew5M1
import UnifiedEJM.PhysicsCoeffNew5M2
import UnifiedEJM.PhysicsCoeffNew5M3
import UnifiedEJM.PhysicsCoeffNew5M4
import UnifiedEJM.PhysicsCoeffNew5M5
import UnifiedEJM.PhysicsCoeffNew5M6
import UnifiedEJM.PhysicsCoeffNew5M7
import UnifiedEJM.PhysicsCoeffNew5M8
import UnifiedEJM.PhysicsCoeffNew5M9
import UnifiedEJM.PhysicsCoeffNew5M10
import UnifiedEJM.PhysicsCoeffNew5M11
import UnifiedEJM.PhysicsCoeffNew5M12
import UnifiedEJM.PhysicsCoeffNew5M13
import UnifiedEJM.PhysicsCoeffNew5M14
import UnifiedEJM.PhysicsCoeffNew5M15
import UnifiedEJM.PhysicsCoefficientTables

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem new5_coefficients_checked (k : Fin 15) :
    gCoefficients (fastMix 5 (canonicalMask5 k)) new5A new5B = new5Coeff k := by
  rw [new5A_fast, new5B_fast]
  fin_cases k
  · exact coeff_new5_1
  · exact coeff_new5_2
  · exact coeff_new5_3
  · exact coeff_new5_4
  · exact coeff_new5_5
  · exact coeff_new5_6
  · exact coeff_new5_7
  · exact coeff_new5_8
  · exact coeff_new5_9
  · exact coeff_new5_10
  · exact coeff_new5_11
  · exact coeff_new5_12
  · exact coeff_new5_13
  · exact coeff_new5_14
  · exact coeff_new5_15

theorem new5_cut_laurent (k : Fin 15) (t : ℝ) :
    Multipartite.cutPurity (canonicalCut5 k) (UnifiedEJM.seed 5 t) =
      (4096 : ℂ)⁻¹ * laurentEval (new5Coeff k) (anglePhase t) := by
  change Multipartite.cutPurity (canonicalCut5 k)
    (Physical.seed (UnifiedEJM.rawPhase (anglePhase t))) = _
  unfold canonicalCut5
  rw [cut5_laurent _ _ (EvenFamily.angle_unit t), new5_coefficients_checked]

end UnifiedEJM.PhysicsFinite
