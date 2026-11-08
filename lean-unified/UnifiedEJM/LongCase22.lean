import UnifiedEJM.LongContext220
import UnifiedEJM.LongContext221
import UnifiedEJM.LongContext222
import UnifiedEJM.LongContext223
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase22
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, -128⟩, ⟨256, 0⟩, ⟨0, 128⟩, ⟨0, 0⟩], ![⟨-128, 112⟩, ⟨-352, 416⟩, ⟨-1088, 0⟩, ⟨-352, -416⟩, ⟨-128, -112⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨9472, 0⟩, ⟨23552, 0⟩, ⟨65024, 0⟩, ⟨23552, 0⟩, ⟨9472, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock2200.expected, LongBlock2201.expected, LongBlock2202.expected, LongBlock2203.expected], ![LongBlock2210.expected, LongBlock2211.expected, LongBlock2212.expected, LongBlock2213.expected], ![LongBlock2220.expected, LongBlock2221.expected, LongBlock2222.expected, LongBlock2223.expected], ![LongBlock2230.expected, LongBlock2231.expected, LongBlock2232.expected, LongBlock2233.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) (some 1) f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock2200.checked i j k
  · exact LongBlock2201.checked i j k
  · exact LongBlock2202.checked i j k
  · exact LongBlock2203.checked i j k
  · exact LongBlock2210.checked i j k
  · exact LongBlock2211.checked i j k
  · exact LongBlock2212.checked i j k
  · exact LongBlock2213.checked i j k
  · exact LongBlock2220.checked i j k
  · exact LongBlock2221.checked i j k
  · exact LongBlock2222.checked i j k
  · exact LongBlock2223.checked i j k
  · exact LongBlock2230.checked i j k
  · exact LongBlock2231.checked i j k
  · exact LongBlock2232.checked i j k
  · exact LongBlock2233.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff (some 1) (some 1) i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum (some 1) (some 1) X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase22
