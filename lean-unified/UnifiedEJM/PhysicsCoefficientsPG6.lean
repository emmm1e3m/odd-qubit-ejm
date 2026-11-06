import UnifiedEJM.PhysicsCoeffPG6M1
import UnifiedEJM.PhysicsCoeffPG6M2
import UnifiedEJM.PhysicsCoeffPG6M3
import UnifiedEJM.PhysicsCoeffPG6M4
import UnifiedEJM.PhysicsCoeffPG6M5
import UnifiedEJM.PhysicsCoeffPG6M6
import UnifiedEJM.PhysicsCoeffPG6M7
import UnifiedEJM.PhysicsCoeffPG6M8
import UnifiedEJM.PhysicsCoeffPG6M9
import UnifiedEJM.PhysicsCoeffPG6M10
import UnifiedEJM.PhysicsCoeffPG6M11
import UnifiedEJM.PhysicsCoeffPG6M12
import UnifiedEJM.PhysicsCoeffPG6M13
import UnifiedEJM.PhysicsCoeffPG6M14
import UnifiedEJM.PhysicsCoeffPG6M15
import UnifiedEJM.PhysicsCoeffPG6M16
import UnifiedEJM.PhysicsCoeffPG6M17
import UnifiedEJM.PhysicsCoeffPG6M18
import UnifiedEJM.PhysicsCoeffPG6M19
import UnifiedEJM.PhysicsCoeffPG6M20
import UnifiedEJM.PhysicsCoeffPG6M21
import UnifiedEJM.PhysicsCoeffPG6M22
import UnifiedEJM.PhysicsCoeffPG6M23
import UnifiedEJM.PhysicsCoeffPG6M24
import UnifiedEJM.PhysicsCoeffPG6M25
import UnifiedEJM.PhysicsCoeffPG6M26
import UnifiedEJM.PhysicsCoeffPG6M27
import UnifiedEJM.PhysicsCoeffPG6M28
import UnifiedEJM.PhysicsCoeffPG6M29
import UnifiedEJM.PhysicsCoeffPG6M30
import UnifiedEJM.PhysicsCoeffPG6M31
import UnifiedEJM.PhysicsCoefficientTables
import UnifiedEJM.PhysicsPGIndexed

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pg6_coefficients_checked (k : Fin 31) :
    gCoefficients (fastMix 6 (canonicalMask6 k)) pg6A pg6B = pg6Coeff k := by
  rw [pg6A_fast, pg6B_fast]
  fin_cases k
  · exact coeff_pg6_1
  · exact coeff_pg6_2
  · exact coeff_pg6_3
  · exact coeff_pg6_4
  · exact coeff_pg6_5
  · exact coeff_pg6_6
  · exact coeff_pg6_7
  · exact coeff_pg6_8
  · exact coeff_pg6_9
  · exact coeff_pg6_10
  · exact coeff_pg6_11
  · exact coeff_pg6_12
  · exact coeff_pg6_13
  · exact coeff_pg6_14
  · exact coeff_pg6_15
  · exact coeff_pg6_16
  · exact coeff_pg6_17
  · exact coeff_pg6_18
  · exact coeff_pg6_19
  · exact coeff_pg6_20
  · exact coeff_pg6_21
  · exact coeff_pg6_22
  · exact coeff_pg6_23
  · exact coeff_pg6_24
  · exact coeff_pg6_25
  · exact coeff_pg6_26
  · exact coeff_pg6_27
  · exact coeff_pg6_28
  · exact coeff_pg6_29
  · exact coeff_pg6_30
  · exact coeff_pg6_31

theorem pg6_cut_laurent (k : Fin 31) (t : ℝ) :
    Multipartite.cutPurity (canonicalCut6 k) (EvenFamily.seed 6 t 0) =
      (16384 : ℂ)⁻¹ * laurentEval (pg6Coeff k) (anglePhase t) := by
  rw [pg_seed_eq]
  unfold canonicalCut6
  rw [pgcut6_laurent _ _ (EvenFamily.angle_unit t), pg6_coefficients_checked]

end UnifiedEJM.PhysicsFinite
