import UnifiedEJM.LongContext120
import UnifiedEJM.LongContext121
import UnifiedEJM.LongContext122
import UnifiedEJM.LongContext123
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase12
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨-128, 112⟩, ⟨-352, 416⟩, ⟨-1088, 0⟩, ⟨-352, -416⟩, ⟨-128, -112⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨9472, 0⟩, ⟨23552, 0⟩, ⟨65024, 0⟩, ⟨23552, 0⟩, ⟨9472, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock1200.expected, LongBlock1201.expected, LongBlock1202.expected, LongBlock1203.expected], ![LongBlock1210.expected, LongBlock1211.expected, LongBlock1212.expected, LongBlock1213.expected], ![LongBlock1220.expected, LongBlock1221.expected, LongBlock1222.expected, LongBlock1223.expected], ![LongBlock1230.expected, LongBlock1231.expected, LongBlock1232.expected, LongBlock1233.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) (some 1) f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock1200.checked i j k
  · exact LongBlock1201.checked i j k
  · exact LongBlock1202.checked i j k
  · exact LongBlock1203.checked i j k
  · exact LongBlock1210.checked i j k
  · exact LongBlock1211.checked i j k
  · exact LongBlock1212.checked i j k
  · exact LongBlock1213.checked i j k
  · exact LongBlock1220.checked i j k
  · exact LongBlock1221.checked i j k
  · exact LongBlock1222.checked i j k
  · exact LongBlock1223.checked i j k
  · exact LongBlock1230.checked i j k
  · exact LongBlock1231.checked i j k
  · exact LongBlock1232.checked i j k
  · exact LongBlock1233.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff (some 0) (some 1) i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum (some 0) (some 1) X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase12
