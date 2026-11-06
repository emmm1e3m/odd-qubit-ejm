import UnifiedEJM.PhysicsCoeffNew6M1
import UnifiedEJM.PhysicsCoeffNew6M2
import UnifiedEJM.PhysicsCoeffNew6M3
import UnifiedEJM.PhysicsCoeffNew6M4
import UnifiedEJM.PhysicsCoeffNew6M5
import UnifiedEJM.PhysicsCoeffNew6M6
import UnifiedEJM.PhysicsCoeffNew6M7
import UnifiedEJM.PhysicsCoeffNew6M8
import UnifiedEJM.PhysicsCoeffNew6M9
import UnifiedEJM.PhysicsCoeffNew6M10
import UnifiedEJM.PhysicsCoeffNew6M11
import UnifiedEJM.PhysicsCoeffNew6M12
import UnifiedEJM.PhysicsCoeffNew6M13
import UnifiedEJM.PhysicsCoeffNew6M14
import UnifiedEJM.PhysicsCoeffNew6M15
import UnifiedEJM.PhysicsCoeffNew6M16
import UnifiedEJM.PhysicsCoeffNew6M17
import UnifiedEJM.PhysicsCoeffNew6M18
import UnifiedEJM.PhysicsCoeffNew6M19
import UnifiedEJM.PhysicsCoeffNew6M20
import UnifiedEJM.PhysicsCoeffNew6M21
import UnifiedEJM.PhysicsCoeffNew6M22
import UnifiedEJM.PhysicsCoeffNew6M23
import UnifiedEJM.PhysicsCoeffNew6M24
import UnifiedEJM.PhysicsCoeffNew6M25
import UnifiedEJM.PhysicsCoeffNew6M26
import UnifiedEJM.PhysicsCoeffNew6M27
import UnifiedEJM.PhysicsCoeffNew6M28
import UnifiedEJM.PhysicsCoeffNew6M29
import UnifiedEJM.PhysicsCoeffNew6M30
import UnifiedEJM.PhysicsCoeffNew6M31
import UnifiedEJM.PhysicsCoefficientTables

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem new6_coefficients_checked (k : Fin 31) :
    gCoefficients (fastMix 6 (canonicalMask6 k)) new6A new6B = new6Coeff k := by
  rw [new6A_fast, new6B_fast]
  fin_cases k
  · exact coeff_new6_1
  · exact coeff_new6_2
  · exact coeff_new6_3
  · exact coeff_new6_4
  · exact coeff_new6_5
  · exact coeff_new6_6
  · exact coeff_new6_7
  · exact coeff_new6_8
  · exact coeff_new6_9
  · exact coeff_new6_10
  · exact coeff_new6_11
  · exact coeff_new6_12
  · exact coeff_new6_13
  · exact coeff_new6_14
  · exact coeff_new6_15
  · exact coeff_new6_16
  · exact coeff_new6_17
  · exact coeff_new6_18
  · exact coeff_new6_19
  · exact coeff_new6_20
  · exact coeff_new6_21
  · exact coeff_new6_22
  · exact coeff_new6_23
  · exact coeff_new6_24
  · exact coeff_new6_25
  · exact coeff_new6_26
  · exact coeff_new6_27
  · exact coeff_new6_28
  · exact coeff_new6_29
  · exact coeff_new6_30
  · exact coeff_new6_31

theorem new6_cut_laurent (k : Fin 31) (t : ℝ) :
    Multipartite.cutPurity (canonicalCut6 k) (UnifiedEJM.seed 6 t) =
      (16384 : ℂ)⁻¹ * laurentEval (new6Coeff k) (anglePhase t) := by
  change Multipartite.cutPurity (canonicalCut6 k)
    (Physical.seed (UnifiedEJM.rawPhase (anglePhase t))) = _
  unfold canonicalCut6
  rw [cut6_laurent _ _ (EvenFamily.angle_unit t), new6_coefficients_checked]

end UnifiedEJM.PhysicsFinite
