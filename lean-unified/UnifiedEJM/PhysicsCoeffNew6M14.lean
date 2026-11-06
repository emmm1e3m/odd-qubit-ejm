import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new6_14 :
    gCoefficients (fastMix 6 14) fastnew6A fastnew6B = ![⟨-54, 0⟩, ⟨480, -8⟩, ⟨3236, 0⟩, ⟨480, 8⟩, ⟨-54, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
