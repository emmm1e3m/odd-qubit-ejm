import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_pg6_21 :
    gCoefficients (fastMix 6 21) fastpg6A fastpg6B = ![⟨-2, 0⟩, ⟨-480, -32⟩, ⟨3132, 0⟩, ⟨-480, 32⟩, ⟨-2, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
