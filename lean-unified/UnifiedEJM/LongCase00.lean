import UnifiedEJM.LongContext000
import UnifiedEJM.LongContext001
import UnifiedEJM.LongContext002
import UnifiedEJM.LongContext003
import UnifiedEJM.PrefixExpansion
open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel.LongCase00
def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨190, 8⟩, ⟨1072, -16⟩, ⟨5404, 0⟩, ⟨1072, 16⟩, ⟨190, -8⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]
/-- 仅收录已证原块的expected字面表。 -/
def blockExpected : Fin 4 → Fin 4 → Fin 3 → Fin 3 → Fin 5 → G :=
  ![![LongBlock0000.expected, LongBlock0001.expected, LongBlock0002.expected, LongBlock0003.expected], ![LongBlock0010.expected, LongBlock0011.expected, LongBlock0012.expected, LongBlock0013.expected], ![LongBlock0020.expected, LongBlock0021.expected, LongBlock0022.expected, LongBlock0023.expected], ![LongBlock0030.expected, LongBlock0031.expected, LongBlock0032.expected, LongBlock0033.expected]]

/-- 在任何Fin下标枚举前，用完整通用接口替换原longBlock。 -/
theorem block_expected (f s : Fin 4) (i j : Fin 3) (k : Fin 5) :
    longBlock none none f s i j k = blockExpected f s i j k := by
  fin_cases f <;> fin_cases s
  · exact LongBlock0000.checked i j k
  · exact LongBlock0001.checked i j k
  · exact LongBlock0002.checked i j k
  · exact LongBlock0003.checked i j k
  · exact LongBlock0010.checked i j k
  · exact LongBlock0011.checked i j k
  · exact LongBlock0012.checked i j k
  · exact LongBlock0013.checked i j k
  · exact LongBlock0020.checked i j k
  · exact LongBlock0021.checked i j k
  · exact LongBlock0022.checked i j k
  · exact LongBlock0023.checked i j k
  · exact LongBlock0030.checked i j k
  · exact LongBlock0031.checked i j k
  · exact LongBlock0032.checked i j k
  · exact LongBlock0033.checked i j k

/-- 此处只计算16个小expected表，原longBlock不会进入归约。 -/
theorem expected_sum (i j : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, blockExpected f s i j k) = expected i j k := by
  revert i j k
  decide +kernel

theorem coefficients (i j : Fin 3) (k : Fin 5) :
    longCoeff none none i j k = expected i j k := by
  rw [longCoeff_blocks]
  simp only [block_expected]
  exact expected_sum i j k

theorem polynomial (X Y : ℤ) (k : Fin 5) :
    longSum none none X Y k = biEval (fun i j => expected i j k) X Y := by
  rw [longSum_expansion]
  simp only [coefficients]
#print axioms coefficients
#print axioms polynomial
end UnifiedEJM.PrefixKernel.LongCase00
