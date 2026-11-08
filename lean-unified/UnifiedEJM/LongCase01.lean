import UnifiedEJM.LongContext010
import UnifiedEJM.LongContext011
import UnifiedEJM.LongContext012
import UnifiedEJM.LongContext013
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase01
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-2, 0⟩, ⟨0, -64⟩, ⟨124, 0⟩, ⟨0, 64⟩, ⟨-2, 0⟩], ![⟨-80, 48⟩, ⟨-192, 32⟩, ⟨-224, 0⟩, ⟨-192, -32⟩, ⟨-80, -48⟩], ![⟨2304, 0⟩, ⟨5120, 0⟩, ⟨17920, 0⟩, ⟨5120, 0⟩, ⟨2304, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock0100.expected, LongBlock0101.expected, LongBlock0102.expected, LongBlock0103.expected], ![LongBlock0110.expected, LongBlock0111.expected, LongBlock0112.expected, LongBlock0113.expected], ![LongBlock0120.expected, LongBlock0121.expected, LongBlock0122.expected, LongBlock0123.expected], ![LongBlock0130.expected, LongBlock0131.expected, LongBlock0132.expected, LongBlock0133.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock none (some 0) f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock0100.checked i j k
  · exact LongBlock0101.checked i j k
  · exact LongBlock0102.checked i j k
  · exact LongBlock0103.checked i j k
  · exact LongBlock0110.checked i j k
  · exact LongBlock0111.checked i j k
  · exact LongBlock0112.checked i j k
  · exact LongBlock0113.checked i j k
  · exact LongBlock0120.checked i j k
  · exact LongBlock0121.checked i j k
  · exact LongBlock0122.checked i j k
  · exact LongBlock0123.checked i j k
  · exact LongBlock0130.checked i j k
  · exact LongBlock0131.checked i j k
  · exact LongBlock0132.checked i j k
  · exact LongBlock0133.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff none (some 0) i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum none (some 0) X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase01
