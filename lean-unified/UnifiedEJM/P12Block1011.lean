import UnifiedEJM.PrefixDataKernel
open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
namespace UnifiedEJM.PrefixKernel.P12Block1011
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def expectedData : Data15 := (((⟨0, 0⟩ : G), (⟨0, -4⟩ : G), (⟨8, 0⟩ : G), (⟨0, 4⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)))
def expected : Fin 3 → Fin 5 → G := coefficient15 expectedData

/-- 全部分量共享原始分类项的计算，最终仍由内核逐项验证等式。 -/
theorem checkedData : p12BlockData 1 false 1 1 = expectedData := by
  decide +kernel

theorem checked (i : Fin 3) (k : Fin 5) :
    p12Block 1 false 1 1 i k = expected i k := by
  rw [← p12BlockData_spec, checkedData]
  rfl

end UnifiedEJM.PrefixKernel.P12Block1011
