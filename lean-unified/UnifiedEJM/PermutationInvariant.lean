import UnifiedEJM.BipartiteInvariant
import UnifiedEJM.PermutationCore

noncomputable section
open scoped BigOperators Matrix
open OddEJM
namespace UnifiedEJM.BipartiteInvariant
open FiniteInvariants

/-- 有序测量逐列施加同一局域酉及比特置换后，不变量逐列保持。 -/
theorem sumPurity_localAction_permute (U : Fin 4 → Matrix Bit Bit ℂ)
    (hU : ∀ j, (U j)ᴴ * U j = 1) (p : Equiv.Perm (Fin 4)) (v : State) :
    sumPurity (localAction U (permute p v)) = sumPurity v := by
  rw [sumPurity_localAction U hU, sumPurity_permute]


/-- 不变量由实际态等价关系推出，不把不变量相等作为额外假设。 -/
theorem sumPurity_of_equivalence (U : Fin 4 → Matrix Bit Bit ℂ)
    (hU : ∀ j, (U j)ᴴ * U j = 1) (p : Equiv.Perm (Fin 4))
    (c : ℂ) (hc : star c * c = 1) (v w : State)
    (heq : w = c • localAction U (permute p v)) :
    sumPurity w = sumPurity v := by
  rw [heq,sumPurity_phase c hc,sumPurity_localAction_permute U hU]

end UnifiedEJM.BipartiteInvariant

