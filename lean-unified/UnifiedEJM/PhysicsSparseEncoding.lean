import UnifiedEJM.PhysicsSparseCertificate

open OddEJM
namespace UnifiedEJM.WeightedTransfer.SparseCertificate

/-- 四个逻辑二元坐标的低位整数编码。 -/
def index4 (d : Bits 4) : ℕ :=
  (d 0).val + 2 * (d 1).val + 4 * (d 2).val + 8 * (d 3).val

theorem index4_lt : ∀ d : Bits 4, index4 d < 16 := by decide +kernel

theorem bits4_index : ∀ d : Bits 4, bits4 (index4 d) = d := by decide +kernel

def indexFin4 (d : Bits 4) : Fin 16 := ⟨index4 d, index4_lt d⟩

theorem bits4_indexFin4 (d : Bits 4) : bits4 (indexFin4 d).val = d := bits4_index d

end UnifiedEJM.WeightedTransfer.SparseCertificate
