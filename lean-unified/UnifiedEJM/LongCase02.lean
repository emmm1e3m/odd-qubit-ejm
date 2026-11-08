import UnifiedEJM.LongContext020
import UnifiedEJM.LongContext021
import UnifiedEJM.LongContext022
import UnifiedEJM.LongContext023
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase02
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, -64⟩, ⟨124, 0⟩, ⟨0, 64⟩, ⟨-2, 0⟩], ![⟨-80, 48⟩, ⟨-192, 32⟩, ⟨-224, 0⟩, ⟨-192, -32⟩, ⟨-80, -48⟩], ![⟨2304, 0⟩, ⟨5120, 0⟩, ⟨17920, 0⟩, ⟨5120, 0⟩, ⟨2304, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock0200.expected, LongBlock0201.expected, LongBlock0202.expected, LongBlock0203.expected], ![LongBlock0210.expected, LongBlock0211.expected, LongBlock0212.expected, LongBlock0213.expected], ![LongBlock0220.expected, LongBlock0221.expected, LongBlock0222.expected, LongBlock0223.expected], ![LongBlock0230.expected, LongBlock0231.expected, LongBlock0232.expected, LongBlock0233.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock none (some 1) f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock0200.checked i j k
  · exact LongBlock0201.checked i j k
  · exact LongBlock0202.checked i j k
  · exact LongBlock0203.checked i j k
  · exact LongBlock0210.checked i j k
  · exact LongBlock0211.checked i j k
  · exact LongBlock0212.checked i j k
  · exact LongBlock0213.checked i j k
  · exact LongBlock0220.checked i j k
  · exact LongBlock0221.checked i j k
  · exact LongBlock0222.checked i j k
  · exact LongBlock0223.checked i j k
  · exact LongBlock0230.checked i j k
  · exact LongBlock0231.checked i j k
  · exact LongBlock0232.checked i j k
  · exact LongBlock0233.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff none (some 1) i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum none (some 1) X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase02
