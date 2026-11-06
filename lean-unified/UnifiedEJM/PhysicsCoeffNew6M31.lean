import UnifiedEJM.PhysicsFastTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- 原相位振幅的精确Fourier系数，使用Lean内核逐项约化。 -/
theorem coeff_new6_31 :
    gCoefficients (fastMix 6 31) fastnew6A fastnew6B = ![⟨-6, 0⟩, ⟨0, -24⟩, ⟨8228, 0⟩, ⟨0, 24⟩, ⟨-6, 0⟩] := by
  funext k
  fin_cases k <;> decide +kernel
end UnifiedEJM.PhysicsFinite
