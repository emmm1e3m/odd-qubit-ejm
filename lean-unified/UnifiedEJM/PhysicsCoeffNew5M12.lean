import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new5_12 :
    gCoefficients (fastMix 5 12) fastnew5A fastnew5B = ![⟨-22, -8⟩, ⟨0, -40⟩, ⟨1124, 0⟩, ⟨0, 40⟩, ⟨-22, 8⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
