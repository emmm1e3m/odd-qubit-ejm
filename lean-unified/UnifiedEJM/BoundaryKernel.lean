import UnifiedEJM.BoundaryAmplitude
import UnifiedEJM.PrefixKernel

open OddEJM Complex
open UnifiedEJM.PhysicsFinite
open UnifiedEJM.PrefixKernel

namespace UnifiedEJM.BoundaryAmplitude

/-- 有限核采用的分段式就是原始四特征多项式。 -/
theorem kernel_eq_F (x b c s : Bit) :
    PrefixKernel.kernel x b c s = F ![x,b,c,s] := by
  revert x b c s
  decide +kernel

private theorem boundary_affine_bits (f₀ f₁ d : Bit) (constant : Bool) (u : ℂ) :
    u^f₀.val + I*bitSign d*u^f₁.val + (I-u)*(if constant then 1 else 0) =
      (((if f₀.val = 0 then 1 else 0) +
        (if f₁.val = 0 then gi*gsign d else 0) +
        (if constant then gi else 0) : G) : ℂ) +
      u * (((if f₀.val = 1 then 1 else 0) +
        (if f₁.val = 1 then gi*gsign d else 0) +
        (if constant then -1 else 0) : G) : ℂ) := by
  rcases OddEJM.bit_cases f₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases f₁ with rfl | rfl <;> cases constant <;>
    simp [ZMod.val_one_eq_one_mod, map_add, map_mul, gi_complex, gsign_complex] <;> ring

/-- 221证书的两个高斯整数系数等于实际边界振幅的常数项与一次项。 -/
theorem boundaryValue_H (nu : Bit) (e : Bits 4) (p : Bit) (constant : Bool) (u : ℂ) :
    boundaryValue nu e p constant u =
      ((H e p constant nu 0 : G) : ℂ) + u * ((H e p constant nu 1 : G) : ℂ) := by
  let x := e 0 + e 1 + e 2 + e 3
  let b := e 1 + p + if nu = 0 then e 2 else 0
  let c := p + if nu = 0 then 0 else e 2
  let s := e 0 + e 1
  simpa [boundaryValue, reducedFeature, H, kernel_eq_F, x, b, c, s] using
    boundary_affine_bits (F ![x,b,c,s]) (F ![x,b,c,s+1]) (e 3) constant u

/-- 实际统一种子直接接入有限高斯整数核H。 -/
theorem seed_H {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (y : Bits n) :
    UnifiedEJM.seed n t y = scale n * pathPhase y *
      (((H (boundary y) (middleParity y) (decide (∀ j, y j = coord y 0))
          (lengthParity n) 0 : G) : ℂ) +
        anglePhase t * ((H (boundary y) (middleParity y) (decide (∀ j, y j = coord y 0))
          (lengthParity n) 1 : G) : ℂ)) := by
  rw [seed_boundary hn, boundaryValue_H]

end UnifiedEJM.BoundaryAmplitude
