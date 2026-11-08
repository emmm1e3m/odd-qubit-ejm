import UnifiedEJM.PrefixDataKernel
open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
namespace UnifiedEJM.PrefixKernel.P12Block0133
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def expectedData : Data15 := (((⟨-3, 0⟩ : G), (⟨0, -20⟩ : G), (⟨34, 0⟩ : G), (⟨0, 20⟩ : G), (⟨-3, 0⟩ : G)), ((⟨4, 0⟩ : G), (⟨-16, 40⟩ : G), (⟨-72, 0⟩ : G), (⟨-16, -40⟩ : G), (⟨4, 0⟩ : G)), ((⟨-8, 0⟩ : G), (⟨64, 0⟩ : G), (⟨400, 0⟩ : G), (⟨64, 0⟩ : G), (⟨-8, 0⟩ : G)))
def expected : Fin 3 → Fin 5 → G := coefficient15 expectedData

/-- 全部分量共享原始分类项的计算，最终仍由内核逐项验证等式。 -/
theorem checkedData : p12BlockData 0 true 3 3 = expectedData := by
  decide +kernel

theorem checked (i : Fin 3) (k : Fin 5) :
    p12Block 0 true 3 3 i k = expected i k := by
  rw [← p12BlockData_spec, checkedData]
  rfl

end UnifiedEJM.PrefixKernel.P12Block0133
