import UnifiedEJM.PrefixKernel

open OddEJM
open UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p12Block (nu : Bit) (suffix : Bool) (f s : Fin 4)
    (i : Fin 3) (k : Fin 5) : G :=
  ∑ t : Fin 4, ∑ p : Fin 4, ∑ l : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
    let w := pairWeight (1 + nu) c d i
    if w = 0 then 0 else (w : G) * p12Term nu suffix f s t p l c d k

theorem p12Coeff_blocks (nu : Bit) (suffix : Bool) (i : Fin 3) (k : Fin 5) :
    p12Coeff nu suffix i k = ∑ f : Fin 4, ∑ s : Fin 4, p12Block nu suffix f s i k := by
  unfold p12Coeff p12Block
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  dsimp only
  split_ifs with h
  · simp [h]
  · rfl

/-- 按前两个固定位置分块，零类别权重在计算振幅之前删除。 -/
def longBlock (la lb : Option Bit) (f s : Fin 4)
    (i j : Fin 3) (k : Fin 5) : G :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ p : Fin 4, ∑ l : Fin 4,
    ∑ ca : Fin 4, ∑ da : Fin 4, ∑ cb : Fin 4, ∑ db : Fin 4,
      let w := runPairWeight la ca da i * runPairWeight lb cb db j
      if w = 0 then 0 else (w : G) * longTerm la lb f s a b p l ca da cb db k

theorem longCoeff_blocks (la lb : Option Bit) (i j : Fin 3) (k : Fin 5) :
    longCoeff la lb i j k = ∑ f : Fin 4, ∑ s : Fin 4, longBlock la lb f s i j k := by
  unfold longCoeff longBlock
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro ca _
  apply Finset.sum_congr rfl
  intro da _
  apply Finset.sum_congr rfl
  intro cb _
  apply Finset.sum_congr rfl
  intro db _
  dsimp only
  split_ifs with h
  · simp [h]
  · rfl

end UnifiedEJM.PrefixKernel
