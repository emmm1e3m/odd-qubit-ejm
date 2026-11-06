import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new5_14 :
    gCoefficients (fastMix 5 14) fastnew5A fastnew5B = ![⟨-2, 0⟩, ⟨0, -32⟩, ⟨1084, 0⟩, ⟨0, 32⟩, ⟨-2, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
