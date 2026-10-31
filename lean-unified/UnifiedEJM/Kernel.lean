import OddEJM.Walsh

namespace UnifiedEJM
open OddEJM
open scoped BigOperators

/-- 同一内部奇偶块的双翻转属于压缩映射的核。 -/
theorem compress_pair_same {n : ℕ} (i j : Fin n)
    (hi : 1 ≤ i.val) (hin : i.val < n - 2)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2)
    (hp : i.val % 2 = j.val % 2) :
    compress (unitBit n i.val + unitBit n j.val) = 0 := by
  rw [compress_add]
  by_cases he : i.val % 2 = 0
  · rw [compress_internal_even i hi hin he,
      compress_internal_even j hj hjn (by omega), bits_add_self]
  · have ho : i.val % 2 = 1 := by omega
    rw [compress_internal_odd i hi hin ho,
      compress_internal_odd j hj hjn (by omega), bits_add_self]

/-- 压缩核上的异号平移消去任意压缩布尔函数的字符。 -/
theorem walsh_comp_zero_of_kernel {n : ℕ} (Q : Bits 5 → Bit) (h w : Bits n)
    (hc : compress w = 0) (hd : dot h w = 1) :
    walsh (fun z => Q (compress z)) h = 0 := by
  apply walsh_zero_of_affine_shift _ h w 0
  · intro z
    simp only [compress_add, hc, add_zero]
  · simpa using hd

/-- 同一个核平移也消去任意方向导数的字符。 -/
theorem walsh_derivative_comp_zero_of_kernel {n : ℕ}
    (Q : Bits 5 → Bit) (a h w : Bits n)
    (hc : compress w = 0) (hd : dot h w = 1) :
    walsh (derivative (fun z => Q (compress z)) a) h = 0 := by
  apply walsh_zero_of_affine_shift _ h w 0
  · intro z
    simp only [derivative, compress_add, hc, add_zero]
  · simpa using hd

end UnifiedEJM
