import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new6_21 :
    gCoefficients (fastMix 6 21) fastnew6A fastnew6B = ![⟨-162, 8⟩, ⟨-368, -48⟩, ⟨3228, 0⟩, ⟨-368, 48⟩, ⟨-162, -8⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
