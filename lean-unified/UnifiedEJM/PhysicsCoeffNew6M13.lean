import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new6_13 :
    gCoefficients (fastMix 6 13) fastnew6A fastnew6B = ![⟨90, 0⟩, ⟨256, -72⟩, ⟨3396, 0⟩, ⟨256, 72⟩, ⟨90, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
