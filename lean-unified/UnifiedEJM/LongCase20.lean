import UnifiedEJM.LongContext200
import UnifiedEJM.LongContext201
import UnifiedEJM.LongContext202
import UnifiedEJM.LongContext203
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase20
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, -64⟩, ⟨124, 0⟩, ⟨0, 64⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-80, 48⟩, ⟨-192, 32⟩, ⟨-224, 0⟩, ⟨-192, -32⟩, ⟨-80, -48⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨2304, 0⟩, ⟨5120, 0⟩, ⟨17920, 0⟩, ⟨5120, 0⟩, ⟨2304, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock2000.expected, LongBlock2001.expected, LongBlock2002.expected, LongBlock2003.expected], ![LongBlock2010.expected, LongBlock2011.expected, LongBlock2012.expected, LongBlock2013.expected], ![LongBlock2020.expected, LongBlock2021.expected, LongBlock2022.expected, LongBlock2023.expected], ![LongBlock2030.expected, LongBlock2031.expected, LongBlock2032.expected, LongBlock2033.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) none f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock2000.checked i j k
  · exact LongBlock2001.checked i j k
  · exact LongBlock2002.checked i j k
  · exact LongBlock2003.checked i j k
  · exact LongBlock2010.checked i j k
  · exact LongBlock2011.checked i j k
  · exact LongBlock2012.checked i j k
  · exact LongBlock2013.checked i j k
  · exact LongBlock2020.checked i j k
  · exact LongBlock2021.checked i j k
  · exact LongBlock2022.checked i j k
  · exact LongBlock2023.checked i j k
  · exact LongBlock2030.checked i j k
  · exact LongBlock2031.checked i j k
  · exact LongBlock2032.checked i j k
  · exact LongBlock2033.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff (some 1) none i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum (some 1) none X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase20
