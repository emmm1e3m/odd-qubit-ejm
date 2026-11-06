import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new5_1 :
    gCoefficients (fastMix 5 1) fastnew5A fastnew5B = ![⟨-6, 0⟩, ⟨0, -24⟩, ⟨2084, 0⟩, ⟨0, 24⟩, ⟨-6, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
