import UnifiedEJM.FourQubit
import UnifiedEJM.PurityInvariant

noncomputable section
open scoped BigOperators Matrix
open Complex
namespace UnifiedEJM.FiniteInvariants

/-- 对物理位j作1|3重排的真实系数矩阵。 -/
def reshape1 (j : Fin 4) (v : State) : Matrix (Fin 2) (Fin 8) ℂ :=
  ![!![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7; v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15],
    !![v 0,v 1,v 2,v 3,v 8,v 9,v 10,v 11; v 4,v 5,v 6,v 7,v 12,v 13,v 14,v 15],
    !![v 0,v 1,v 4,v 5,v 8,v 9,v 12,v 13; v 2,v 3,v 6,v 7,v 10,v 11,v 14,v 15],
    !![v 0,v 2,v 4,v 6,v 8,v 10,v 12,v 14; v 1,v 3,v 5,v 7,v 9,v 11,v 13,v 15]] j

def singlePuritySum (v : State) : ℂ :=
  ∑ j : Fin 4, UnifiedEJM.PurityInvariant.purity (reshape1 j v)

theorem single_purity_eq_sum (A : Matrix (Fin 2) (Fin 8) ℂ) :
    UnifiedEJM.PurityInvariant.purity A =
      ∑ i, ∑ j, (∑ k, A i k * star (A j k)) * (∑ l, A j l * star (A i l)) := by
  rfl

end UnifiedEJM.FiniteInvariants
