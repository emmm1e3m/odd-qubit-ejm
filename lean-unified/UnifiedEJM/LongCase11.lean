import UnifiedEJM.LongContext110
import UnifiedEJM.LongContext111
import UnifiedEJM.LongContext112
import UnifiedEJM.LongContext113
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase11
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨-128, 112⟩, ⟨-352, 416⟩, ⟨-1088, 0⟩, ⟨-352, -416⟩, ⟨-128, -112⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨9472, 0⟩, ⟨23552, 0⟩, ⟨65024, 0⟩, ⟨23552, 0⟩, ⟨9472, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock1100.expected, LongBlock1101.expected, LongBlock1102.expected, LongBlock1103.expected], ![LongBlock1110.expected, LongBlock1111.expected, LongBlock1112.expected, LongBlock1113.expected], ![LongBlock1120.expected, LongBlock1121.expected, LongBlock1122.expected, LongBlock1123.expected], ![LongBlock1130.expected, LongBlock1131.expected, LongBlock1132.expected, LongBlock1133.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) (some 0) f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock1100.checked i j k
  · exact LongBlock1101.checked i j k
  · exact LongBlock1102.checked i j k
  · exact LongBlock1103.checked i j k
  · exact LongBlock1110.checked i j k
  · exact LongBlock1111.checked i j k
  · exact LongBlock1112.checked i j k
  · exact LongBlock1113.checked i j k
  · exact LongBlock1120.checked i j k
  · exact LongBlock1121.checked i j k
  · exact LongBlock1122.checked i j k
  · exact LongBlock1123.checked i j k
  · exact LongBlock1130.checked i j k
  · exact LongBlock1131.checked i j k
  · exact LongBlock1132.checked i j k
  · exact LongBlock1133.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff (some 0) (some 0) i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum (some 0) (some 0) X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase11
