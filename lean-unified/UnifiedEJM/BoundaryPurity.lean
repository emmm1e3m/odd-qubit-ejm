import UnifiedEJM.BoundaryPhase

open OddEJM OddEJM.CircuitPauli Complex
open UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.BoundaryAmplitude

/-- 对实际输出串评估的有限边界核。 -/
def evaluatedBoundary {n : ℕ} (u : ℂ) (y : Bits n) : ℂ :=
  boundaryValue (lengthParity n) (boundary y) (middleParity y)
    (decide (∀ j, y j = coord y 0)) u

/-- 174.2：真实态的交换纯度归约为边界核与路径跨边字符的有限和。 -/
theorem actual_swapPurity_boundary {n : ℕ} (hn : 5 ≤ n)
    (S : Finset (Fin n)) (u : ℂ) :
    swapPurity S (Physical.seed (UnifiedEJM.rawPhase u)) =
      (((2 : ℂ) ^ (n+1))⁻¹)^2 *
        ∑ y : Bits n, ∑ v : Bits n,
          bitSign (∑ j : Fin n, crossingTerm S y v j) *
            evaluatedBoundary u y * evaluatedBoundary u v *
              star (evaluatedBoundary u (splice S y v)) *
              star (evaluatedBoundary u (splice S v y)) := by
  have hseed : Physical.seed (UnifiedEJM.rawPhase u) =
      fun y : Bits n => scale n * (pathPhase y * evaluatedBoundary u y) := by
    funext y
    rw [actual_seed_boundary hn]
    simp only [evaluatedBoundary, mul_assoc]
  rw [hseed, swapPurity_smul, scale_norm]
  congr 1
  unfold swapPurity
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  simp only [star_mul]
  calc
    _ = (pathPhase y * pathPhase v * star (pathPhase (splice S y v)) *
        star (pathPhase (splice S v y))) *
          (evaluatedBoundary u y * evaluatedBoundary u v *
            star (evaluatedBoundary u (splice S y v)) *
            star (evaluatedBoundary u (splice S v y))) := by ring
    _ = _ := by rw [pathPhase_four_splice]; ring

end UnifiedEJM.BoundaryAmplitude
