import UnifiedEJM.LongContext100
import UnifiedEJM.LongContext101
import UnifiedEJM.LongContext102
import UnifiedEJM.LongContext103
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase10
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, -64⟩, ⟨124, 0⟩, ⟨0, 64⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-32, 32⟩, ⟨-128, 192⟩, ⟨-448, 0⟩, ⟨-128, -192⟩, ⟨-32, -32⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨1280, 0⟩, ⟨5120, 0⟩, ⟨19968, 0⟩, ⟨5120, 0⟩, ⟨1280, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock1000.expected, LongBlock1001.expected, LongBlock1002.expected, LongBlock1003.expected], ![LongBlock1010.expected, LongBlock1011.expected, LongBlock1012.expected, LongBlock1013.expected], ![LongBlock1020.expected, LongBlock1021.expected, LongBlock1022.expected, LongBlock1023.expected], ![LongBlock1030.expected, LongBlock1031.expected, LongBlock1032.expected, LongBlock1033.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock1000.checked i j k
  · exact LongBlock1001.checked i j k
  · exact LongBlock1002.checked i j k
  · exact LongBlock1003.checked i j k
  · exact LongBlock1010.checked i j k
  · exact LongBlock1011.checked i j k
  · exact LongBlock1012.checked i j k
  · exact LongBlock1013.checked i j k
  · exact LongBlock1020.checked i j k
  · exact LongBlock1021.checked i j k
  · exact LongBlock1022.checked i j k
  · exact LongBlock1023.checked i j k
  · exact LongBlock1030.checked i j k
  · exact LongBlock1031.checked i j k
  · exact LongBlock1032.checked i j k
  · exact LongBlock1033.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff (some 0) none i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum (some 0) none X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase10
