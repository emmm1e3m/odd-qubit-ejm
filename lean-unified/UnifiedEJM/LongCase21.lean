import UnifiedEJM.LongContext210
import UnifiedEJM.LongContext211
import UnifiedEJM.LongContext212
import UnifiedEJM.LongContext213
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase21
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨-128, 112⟩, ⟨-352, 416⟩, ⟨-1088, 0⟩, ⟨-352, -416⟩, ⟨-128, -112⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨9472, 0⟩, ⟨23552, 0⟩, ⟨65024, 0⟩, ⟨23552, 0⟩, ⟨9472, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock2100.expected, LongBlock2101.expected, LongBlock2102.expected, LongBlock2103.expected], ![LongBlock2110.expected, LongBlock2111.expected, LongBlock2112.expected, LongBlock2113.expected], ![LongBlock2120.expected, LongBlock2121.expected, LongBlock2122.expected, LongBlock2123.expected], ![LongBlock2130.expected, LongBlock2131.expected, LongBlock2132.expected, LongBlock2133.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) (some 0) f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock2100.checked i j k
  · exact LongBlock2101.checked i j k
  · exact LongBlock2102.checked i j k
  · exact LongBlock2103.checked i j k
  · exact LongBlock2110.checked i j k
  · exact LongBlock2111.checked i j k
  · exact LongBlock2112.checked i j k
  · exact LongBlock2113.checked i j k
  · exact LongBlock2120.checked i j k
  · exact LongBlock2121.checked i j k
  · exact LongBlock2122.checked i j k
  · exact LongBlock2123.checked i j k
  · exact LongBlock2130.checked i j k
  · exact LongBlock2131.checked i j k
  · exact LongBlock2132.checked i j k
  · exact LongBlock2133.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff (some 1) (some 0) i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum (some 1) (some 0) X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase21
