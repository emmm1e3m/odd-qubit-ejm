import UnifiedEJM.PrefixCounts
import UnifiedEJM.BoundaryPurity
import UnifiedEJM.BoundaryPrefix

open OddEJM Complex
open UnifiedEJM.PhysicsFinite UnifiedEJM.BoundaryAmplitude
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

/-- 实际连续位块拼接的全体求和恒等式。 -/
theorem sum_append {R : Type*} [AddCommMonoid R] (m n : ℕ)
    (f : Bits (m+n) → R) :
    (∑ z : Bits (m+n), f z) = ∑ x : Bits m, ∑ y : Bits n, f (Fin.append x y) := by
  rw [← (Fin.appendEquiv (α := Bit) m n).sum_comp f]
  exact Fintype.sum_prod_type _

@[simp] theorem parity_append {m n : ℕ} (x : Bits m) (y : Bits n) :
    parityHom (m+n) (Fin.append x y) = parityHom m x + parityHom n y := by
  simp [parityHom, Fin.sum_univ_add]

@[simp] theorem parity_cons {L : ℕ} (b : Bit) (x : Bits L) :
    parityHom (L+1) (Fin.cons b x) = b + parityHom L x := by
  simp [parityHom, Fin.sum_univ_succ]

@[simp] theorem parity_snoc {L : ℕ} (x : Bits L) (b : Bit) :
    parityHom (L+1) (Fin.snoc x b) = parityHom L x + b := by
  simp [parityHom, Fin.sum_univ_castSucc]

theorem constant_append {m n : ℕ} (x : Bits m) (y : Bits n) (b : Bit) :
    (∀ j, Fin.append x y j = b) ↔ (∀ j, x j = b) ∧ (∀ j, y j = b) := by
  constructor
  · intro h
    exact ⟨fun j => by simpa using h (Fin.castAdd n j),
      fun j => by simpa using h (Fin.natAdd m j)⟩
  · rintro ⟨hx, hy⟩ j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hx i
    · simpa using hy i

theorem constant_cons {L : ℕ} (a b : Bit) (x : Bits L) :
    (∀ j : Fin (L+1), (Fin.cons a x : Bits (L+1)) j = b) ↔
      a = b ∧ (∀ j, x j = b) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun j => by simpa using h j.succ⟩
  · rintro ⟨ha, hx⟩ j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using ha
    · simpa using hx i

theorem constant_snoc {L : ℕ} (x : Bits L) (a b : Bit) :
    (∀ j : Fin (L+1), (Fin.snoc x a : Bits (L+1)) j = b) ↔
      (∀ j, x j = b) ∧ a = b := by
  constructor
  · intro h
    exact ⟨fun j => by simpa using h j.castSucc, by simpa using h (Fin.last L)⟩
  · rintro ⟨hx, ha⟩ j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using ha
    · simpa using hx i

/-- 前缀交换作用正好在实际位块边界处重组两份串。 -/
theorem splice_append {m n : ℕ} (a c : Bits m) (b d : Bits n) :
    splice (prefixSet (m+n) m) (Fin.append a b) (Fin.append c d) = Fin.append a d := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [splice, prefixSet, i.isLt]
  · simp [splice, prefixSet]

/-- 真实四副本和按物理前缀/后缀的重索引，不引入系数公式假设。 -/
theorem prefix_swap_boundary_blocks {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : 5 ≤ m+n) (u : ℂ) :
    swapPurity (prefixSet (m+n) m) (Physical.seed (UnifiedEJM.rawPhase u)) =
      (((2 : ℂ) ^ (m+n+1))⁻¹)^2 *
        ∑ a : Bits m, ∑ b : Bits n, ∑ c : Bits m, ∑ d : Bits n,
          bitSign ((coord (Fin.append a b) (m-1) + coord (Fin.append c d) (m-1)) *
            (coord (Fin.append a b) m + coord (Fin.append c d) m)) *
          evaluatedBoundary u (Fin.append a b) * evaluatedBoundary u (Fin.append c d) *
          star (evaluatedBoundary u (Fin.append a d)) *
          star (evaluatedBoundary u (Fin.append c b)) := by
  rw [actual_swapPurity_boundary hmn]
  simp_rw [crossing_sum_prefix (n := m+n) (k := m) hm (by omega),
    sum_append m n, splice_append]

/-- 中央奇偶由总奇偶去掉四端点得到，适用于任意长实际位串。 -/
theorem middleParity_of_total {n : ℕ} (hn : 4 ≤ n) (y : Bits n) :
    middleParity y = parityHom n y + coord y 0 + coord y 1 +
      coord y (n-2) + coord y (n-1) := by
  let j0 : Fin n := ⟨0, by omega⟩
  let j1 : Fin n := ⟨1, by omega⟩
  let j2 : Fin n := ⟨n-2, by omega⟩
  let j3 : Fin n := ⟨n-1, by omega⟩
  have hp (j : Fin n) :
      y j = (if 2 ≤ j.val ∧ j.val < n-2 then y j else 0) +
        (if j = j0 then y j else 0) + (if j = j1 then y j else 0) +
        (if j = j2 then y j else 0) + (if j = j3 then y j else 0) := by
    by_cases h0 : j = j0
    · subst j
      simp [j0, j1, j2, j3, show 0 ≠ n-2 by omega, show 0 ≠ n-1 by omega]
    · by_cases h1 : j = j1
      · subst j
        simp [j0, j1, j2, j3, show 1 ≠ n-2 by omega, show 1 ≠ n-1 by omega]
      · by_cases h2 : j = j2
        · subst j
          simp [j0, j1, j2, j3, show n-2 ≠ 0 by omega,
            show n-2 ≠ 1 by omega, show n-2 ≠ n-1 by omega]
        · by_cases h3 : j = j3
          · subst j
            simp [j0, j1, j2, j3, show ¬ n-1 < n-2 by omega,
              show n-1 ≠ 0 by omega, show n-1 ≠ 1 by omega,
              show n ≠ 2 by omega, show n-1 ≠ n-2 by omega]
          · have hmid : 2 ≤ j.val ∧ j.val < n-2 := by
              have hv0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
              have hv1 : j.val ≠ 1 := fun h => h1 (Fin.ext h)
              have hv2 : j.val ≠ n-2 := fun h => h2 (Fin.ext h)
              have hv3 : j.val ≠ n-1 := fun h => h3 (Fin.ext h)
              omega
            simp [hmid, h0, h1, h2, h3]
  have hsum := congrArg (fun f : Fin n → Bit => ∑ j, f j) (funext hp)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  change parityHom n y = middleParity y + y j0 + y j1 + y j2 + y j3 at hsum
  simp only [coord, show 0 < n by omega, show 1 < n by omega,
    show n-2 < n by omega, show n-1 < n by omega, dite_true]
  rw [hsum]
  change middleParity y = middleParity y + y j0 + y j1 + y j2 + y j3 +
    y j0 + y j1 + y j2 + y j3
  ring_nf <;> simp [show (2 : Bit) = 0 by decide]

end UnifiedEJM.PrefixCounts
