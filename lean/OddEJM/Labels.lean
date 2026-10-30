import OddEJM.Pauli
import OddEJM.Counting

namespace OddEJM
open scoped BigOperators

/-- 输入列在指定物理位上的两个四面体标签。 -/
def localOutcome {n : ℕ} (j : Fin n) (label : Bits n) : Bit × Bit :=
  (CircuitPauli.localParity label j.val, coord label (n - 1))

/-- 相邻边求和标号与实际Pauli轨道的局部符号完全一致。 -/
theorem fullLabel_eq_localOutcome (m : ℕ) (j : Fin (m + 1)) (label : Bits (m + 1)) :
    Geometry.fullLabelHom m j label = localOutcome j label := by
  apply Prod.ext
  · change Geometry.edgeParityHom m j (fun k => label k.castSucc) =
      CircuitPauli.localParity label j.val
    rw [← CircuitPauli.orbitZ_coord label j.val j.isLt]
    have hc : coord (CircuitPauli.orbitZ label) j.val = CircuitPauli.orbitZ label j := by
      simp only [coord, dite_eq_left j.isLt]
    rw [hc]
    change (∑ k : Fin m, if k.val = j.val ∨ k.val + 1 = j.val then label k.castSucc else 0) =
      ∑ k : Fin (m + 1), setBit label m 0 k *
        (unitBit (m + 1) k.val j + unitBit (m + 1) (k.val + 1) j)
    rw [Fin.sum_univ_castSucc]
    simp only [setBit, Fin.val_last, ite_true, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k.val ≠ m := ne_of_lt k.isLt
    simp only [Fin.val_castSucc, hkm, ite_false]
    by_cases h0 : k.val = j.val
    · have h1 : j.val ≠ k.val + 1 := by omega
      simp [unitBit, h0]
    · by_cases h1 : k.val + 1 = j.val
      · have h2 : j.val ≠ k.val := Ne.symm h0
        simp [unitBit, h0, h1, h2]
      · have h2 : j.val ≠ k.val := Ne.symm h0
        have h3 : j.val ≠ k.val + 1 := Ne.symm h1
        simp [unitBit, h0, h1, h2, h3]
  · change label (Fin.last m) = coord label (m + 1 - 1)
    simp only [Nat.add_sub_cancel, coord, dite_eq_left (Nat.lt_succ_self m)]
    rfl

/-- 每个实际局部四面体标签的输入列数为2^(n−2)。 -/
theorem localOutcome_fiber_card {n : ℕ} (hn : 2 ≤ n) (j : Fin n) (a : Bit × Bit) :
    Nat.card {label : Bits n // localOutcome j label = a} = 2 ^ (n - 2) := by
  cases n with
  | zero => omega
  | succ m =>
    have h := Geometry.fullLabel_fiber_card m (by omega) j a
    change Nat.card {label : Bits (m + 1) // localOutcome j label = a} = 2 ^ (m + 1 - 2)
    rw [show m + 1 - 2 = m - 1 by omega]
    simpa only [fullLabel_eq_localOutcome] using h

end OddEJM

