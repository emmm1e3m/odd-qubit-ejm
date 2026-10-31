import UnifiedEJM.Physical

namespace UnifiedEJM.Physical
open OddEJM OddEJM.CircuitPauli
open scoped Matrix BigOperators

/-- 原Pauli约定的单比特矩阵：计算基平移并乘输入字符。 -/
def pauliMatrix (a b : Bit) : Matrix Bit Bit ℂ :=
  Matrix.of (fun row col => if col = row + a then bitSign (b * col) else 0)

theorem pauliMatrix_unitary (a b : Bit) : (pauliMatrix a b)ᴴ * pauliMatrix a b = 1 := by
  ext row col
  change (∑ k : Bit,
    star (if row = k + a then bitSign (b * row) else 0) *
      (if col = k + a then bitSign (b * col) else 0)) = if row = col then 1 else 0
  rw [sum_bit]
  rcases CircuitPauli.bit_cases a with rfl | rfl <;> rcases CircuitPauli.bit_cases b with rfl | rfl <;>
    rcases CircuitPauli.bit_cases row with rfl | rfl <;> rcases CircuitPauli.bit_cases col with rfl | rfl <;>
    simp [bitSign, show (1 : Bit) + 1 = 0 by decide]

theorem pauliMatrix_tensor_entry {n : ℕ} (a b z w : Bits n) :
    (∏ j, pauliMatrix (a j) (b j) (z j) (w j)) =
      if w = z + a then character b w else 0 := by
  classical
  by_cases hw : w = z + a
  · subst w
    simp only [pauliMatrix, Matrix.of_apply, Pi.add_apply, ite_true]
    rw [character, dot, bitSign_sum]
    rfl
  · rw [if_neg hw]
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ z j + a j := by
      by_contra h
      push Not at h
      exact hw (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [pauliMatrix, hj]

/-- 任意n的实际Pauli振幅作用等于局域单比特矩阵的张量作用。 -/
theorem pauliAction_tensor {n : ℕ} (a b : Bits n) (ψ : Vec n) (z : Bits n) :
    pauliAction a b 1 ψ z =
      ∑ w : Bits n, (∏ j, pauliMatrix (a j) (b j) (z j) (w j)) * ψ w := by
  classical
  simp only [pauliMatrix_tensor_entry, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [pauliAction, one_mul]

end UnifiedEJM.Physical




