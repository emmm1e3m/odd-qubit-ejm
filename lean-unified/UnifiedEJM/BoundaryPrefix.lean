import UnifiedEJM.BoundaryPhase

open OddEJM OddEJM.CircuitPauli Complex
open UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.BoundaryAmplitude

/-- 首k位构成的前缀割。 -/
def prefixSet (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => j.val < k)

/-- 前缀割的四副本符号只涉及第k与第k+1个物理位。 -/
theorem crossing_sum_prefix {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (y v : Bits n) :
    (∑ j : Fin n, crossingTerm (prefixSet n k) y v j) =
      (coord y (k-1)+coord v (k-1))*(coord y k+coord v k) := by
  let j₀ : Fin n := ⟨k-1, by omega⟩
  have hj₀ : j₀.val+1 = k := by dsimp [j₀]; omega
  rw [Finset.sum_eq_single j₀]
  · simp [crossingTerm, prefixSet, j₀, hj₀, hkn, coord,
      show k-1 < k by omega, show k-1 < n by omega,
      show k-1+1 = k by omega]
  · intro j _ hj
    have hne : j.val ≠ k-1 := by
      intro he
      apply hj
      exact Fin.ext he
    by_cases hnxt : j.val+1 < n
    · have hs : j.val < k ↔ j.val+1 < k := by omega
      simp [crossingTerm, prefixSet, hnxt, hs]
    · simp [crossingTerm, hnxt]
  · simp

theorem pathPhase_four_prefix {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (y v : Bits n) :
    pathPhase y * pathPhase v *
      star (pathPhase (splice (prefixSet n k) y v)) *
      star (pathPhase (splice (prefixSet n k) v y)) =
      bitSign ((coord y (k-1)+coord v (k-1))*(coord y k+coord v k)) := by
  rw [pathPhase_four_splice, crossing_sum_prefix hk hkn]

end UnifiedEJM.BoundaryAmplitude
