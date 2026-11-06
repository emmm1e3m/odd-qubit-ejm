import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_pg6_18 :
    gCoefficients (fastMix 6 18) fastpg6A fastpg6B = ![⟨6, 0⟩, ⟨0, -16⟩, ⟨4140, 0⟩, ⟨0, 16⟩, ⟨6, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
