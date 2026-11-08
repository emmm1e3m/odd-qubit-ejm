import UnifiedEJM.PrefixKernelBlocks

open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

/-- 进一步固定跨割的两个物理位对，每个子块剩余4096项。 -/
def longCrossBlock (la lb : Option Bit) (f s a b : Fin 4)
    (i j : Fin 3) (k : Fin 5) : G :=
  ∑ p : Fin 4, ∑ l : Fin 4, ∑ ca : Fin 4, ∑ da : Fin 4,
    ∑ cb : Fin 4, ∑ db : Fin 4,
      let w := runPairWeight la ca da i * runPairWeight lb cb db j
      if w = 0 then 0 else (w : G) * longTerm la lb f s a b p l ca da cb db k

theorem longBlock_crossBlocks (la lb : Option Bit) (f s : Fin 4)
    (i j : Fin 3) (k : Fin 5) :
    longBlock la lb f s i j k =
      ∑ a : Fin 4, ∑ b : Fin 4, longCrossBlock la lb f s a b i j k := rfl

end UnifiedEJM.PrefixKernel
