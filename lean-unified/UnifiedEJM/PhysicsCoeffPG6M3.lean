import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_pg6_3 :
    gCoefficients (fastMix 6 3) fastpg6A fastpg6B = ![⟨-450, 0⟩, ⟨0, 224⟩, ⟨8892, 0⟩, ⟨0, -224⟩, ⟨-450, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
