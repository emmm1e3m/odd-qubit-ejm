import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new5_9 :
    gCoefficients (fastMix 5 9) fastnew5A fastnew5B = ![⟨-34, 0⟩, ⟨0, -32⟩, ⟨1148, 0⟩, ⟨0, 32⟩, ⟨-34, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
