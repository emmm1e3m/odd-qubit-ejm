import UnifiedEJM.Core
import UnifiedEJM.Kernel

namespace UnifiedEJM
open OddEJM
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- 整数字符和用于有限维证书；复数等式由标准强制转换导出。 -/
def intWalsh {n : ℕ} (f : Bits n → Bit) (h : Bits n) : ℤ :=
  ∑ z, intSign (f z + dot h z)

theorem walsh_of_int_zero {n : ℕ} (f : Bits n → Bit) (h : Bits n)
    (hz : intWalsh f h = 0) : walsh f h = 0 := by
  have hc := congrArg (fun k : ℤ => (k : ℂ)) hz
  simpa only [intWalsh, walsh, Int.cast_sum, intSign_cast, Int.cast_zero] using hc

/-- 固定核在19方向的周期，等价于四特征压缩。 -/
theorem Q20_period : ∀ v : Bits 5, Q20 (v + decode5 19) = Q20 v := by decide

def endpointShift (n : ℕ) : Bits n :=
  unitBit n 0 + unitBit n (n - 2) + unitBit n (n - 1)

theorem compress_endpointShift {n : ℕ} (hn : 5 ≤ n) :
    compress (endpointShift n) = decode5 19 := by
  simp only [endpointShift, compress_add, compress_first hn,
    compress_penultimate hn, compress_last hn]
  decide

theorem q_endpoint_period {n : ℕ} (hn : 5 ≤ n) (z : Bits n) :
    q (z + endpointShift n) = q z := by
  simp only [q, compress_add, compress_endpointShift hn, Q20_period]

theorem walsh_Q_zero_endpoint {n : ℕ} (hn : 5 ≤ n) (h : Bits n)
    (hd : dot h (endpointShift n) = 1) : walsh q h = 0 := by
  apply walsh_zero_of_affine_shift _ h (endpointShift n) 0
  · intro z
    simpa only [add_zero] using q_endpoint_period hn z
  · simpa only [zero_add] using hd

theorem walsh_DQ_zero_endpoint {n : ℕ} (hn : 5 ≤ n) (a h : Bits n)
    (hd : dot h (endpointShift n) = 1) : walsh (derivative q a) h = 0 := by
  apply walsh_zero_of_affine_shift _ h (endpointShift n) 0
  · intro z
    have he : z + endpointShift n + a = z + a + endpointShift n := by abel
    simp only [derivative, he, q_endpoint_period hn, add_zero]
  · simpa only [zero_add] using hd

theorem dot_endpointShift {n : ℕ} (hn : 5 ≤ n) (h : Bits n) :
    dot h (endpointShift n) = h ⟨0, by omega⟩ + h ⟨n - 2, by omega⟩ + h ⟨n - 1, by omega⟩ := by
  simp only [endpointShift, dot_add, dot_unitBit h (⟨0, by omega⟩ : Fin n),
    dot_unitBit h (⟨n - 2, by omega⟩ : Fin n),
    dot_unitBit h (⟨n - 1, by omega⟩ : Fin n)]

theorem walsh_Q_first {n : ℕ} (hn : 5 ≤ n) : walsh q (unitBit n 0) = 0 := by
  apply walsh_Q_zero_endpoint hn
  rw [dot_endpointShift hn]
  simp [unitBit, show n - 2 ≠ 0 by omega, show n - 1 ≠ 0 by omega]

theorem walsh_Q_penultimate {n : ℕ} (hn : 5 ≤ n) :
    walsh q (unitBit n (n - 2)) = 0 := by
  apply walsh_Q_zero_endpoint hn
  rw [dot_endpointShift hn]
  simp [unitBit, show (0 : ℕ) ≠ n - 2 by omega, show n - 1 ≠ n - 2 by omega]

/-- 全维尾字符中仅两个固定提升与五比特例外不由核平移消去。 -/
theorem q20_walsh_fixed : ∀ h ∈ ({15,3} : Finset ℕ),
    intWalsh Q20 (decode5 h) = 0 := by decide

theorem tailMask_penultimate_lift {n : ℕ} (hn : 5 ≤ n) :
    tailMask n (n - 2) = liftMask n (decode5 3) := by
  ext i
  have hi := i.isLt
  by_cases h2 : i.val = n - 2
  · simp [tailMask, liftMask, decode5, unitBit, h2,
      show n - 2 ≠ n - 1 by omega]
  by_cases h1 : i.val = n - 1
  · simp [tailMask, liftMask, decode5, unitBit, h1,
      show n - 1 ≠ n - 2 by omega, show n - 2 ≤ n - 1 by omega]
    decide
  · simp [tailMask, liftMask, decode5, unitBit, h2, h1,
      show ¬ n - 2 ≤ i.val by omega]

theorem q5_tail_int : ∀ j : Fin 5, intWalsh q (tailMask 5 j) = 0 := by decide

theorem walsh_Q_tail {n : ℕ} (hn : 5 ≤ n) (j : ℕ) (hjn : j < n) :
    walsh q (tailMask n j) = 0 := by
  by_cases hn5 : n = 5
  · subst n
    exact walsh_of_int_zero q _ (q5_tail_int ⟨j, hjn⟩)
  have hn6 : 6 ≤ n := by omega
  by_cases hj0 : j = 0
  · subst j
    apply walsh_Q_zero_endpoint hn
    rw [dot_endpointShift hn]
    simp [tailMask]
    decide
  by_cases hj1 : j = 1
  · subst j
    rw [tailMask_one_eq_lift hn]
    exact walsh_lift_zero hn Q20 _ (walsh_of_int_zero _ _ (q20_walsh_fixed 15 (by simp)))
  by_cases hj2 : j = n - 2
  · subst j
    rw [tailMask_penultimate_lift hn]
    exact walsh_lift_zero hn Q20 _ (walsh_of_int_zero _ _ (q20_walsh_fixed 3 (by simp)))
  by_cases hjlast : j = n - 1
  · subst j
    apply walsh_Q_zero_endpoint hn
    rw [dot_endpointShift hn]
    simp [tailMask, show ¬ n - 1 ≤ 0 by omega, show ¬ n - 1 ≤ n - 2 by omega]
  have hjlo : 2 ≤ j := by omega
  have hjhi : j < n - 2 := by omega
  by_cases hj4 : j < 4
  · apply walsh_comp_zero_of_kernel Q20 _ (unitBit n 1 + unitBit n 3)
    · exact compress_pair_same ⟨1, by omega⟩ ⟨3, by omega⟩ (by simp) (by simp; omega)
        (by simp) (by simp; omega) (by simp)
    · rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n), dot_unitBit _ (⟨3, by omega⟩ : Fin n)]
      simp [tailMask, show ¬ j ≤ 1 by omega, show j ≤ 3 by omega]
  · by_cases he : j % 2 = 0
    · apply walsh_comp_zero_of_kernel Q20 _ (unitBit n 2 + unitBit n j)
      · exact compress_pair_same ⟨2, by omega⟩ ⟨j, by omega⟩ (by simp) (by simp; omega)
          (by simp; omega) (by simp; omega) (by simp; omega)
      · rw [dot_add, dot_unitBit _ (⟨2, by omega⟩ : Fin n), dot_unitBit _ (⟨j, by omega⟩ : Fin n)]
        simp [tailMask, show ¬ j ≤ 2 by omega]
    · apply walsh_comp_zero_of_kernel Q20 _ (unitBit n 1 + unitBit n j)
      · exact compress_pair_same ⟨1, by omega⟩ ⟨j, by omega⟩ (by simp) (by simp; omega)
          (by simp; omega) (by simp; omega) (by simp; omega)
      · rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n), dot_unitBit _ (⟨j, by omega⟩ : Fin n)]
        simp [tailMask, show ¬ j ≤ 1 by omega]

/-- 五比特是X导数字符无法在压缩核内配对的唯一小维例外。 -/
theorem q5_DX_int : ∀ j : Fin 5, 1 ≤ j.val → j.val < 4 →
    intWalsh (derivative q (adjacentMask 5 j)) (adjacentMask 5 j) = 0 := by decide

theorem walsh_DQ_X {n : ℕ} (hn : 5 ≤ n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) :
    walsh (derivative q (adjacentMask n j)) (adjacentMask n j) = 0 := by
  by_cases hn5 : n = 5
  · subst n
    exact walsh_of_int_zero _ _ (q5_DX_int ⟨j, by omega⟩ hj (by omega))
  have hn6 : 6 ≤ n := by omega
  by_cases hj1 : j = 1
  · subst j
    apply walsh_DQ_zero_endpoint hn
    rw [dot_endpointShift hn]
    simp [adjacentMask, unitBit, show n - 2 ≠ 0 by omega,
      show n - 2 ≠ 1 by omega, show n - 1 ≠ 0 by omega, show n - 1 ≠ 1 by omega]
  by_cases hjlast : j = n - 2
  · subst j
    apply walsh_DQ_zero_endpoint hn
    rw [dot_endpointShift hn]
    simp [adjacentMask, unitBit, show (0 : ℕ) ≠ n - 2 - 1 by omega,
      show (0 : ℕ) ≠ n - 2 by omega, show n - 2 ≠ n - 2 - 1 by omega,
      show n - 1 ≠ n - 2 - 1 by omega, show n - 1 ≠ n - 2 by omega]
  have hjlo : 2 ≤ j := by omega
  have hjhi : j < n - 2 := by omega
  by_cases hj2 : j = 2
  · subst j
    apply walsh_derivative_comp_zero_of_kernel Q20 _ _ (unitBit n 1 + unitBit n 3)
    · exact compress_pair_same ⟨1, by omega⟩ ⟨3, by omega⟩ (by simp) (by simp; omega)
        (by simp) (by simp; omega) (by simp)
    · rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n), dot_unitBit _ (⟨3, by omega⟩ : Fin n)]
      simp [adjacentMask, unitBit]
  have hj3 : 3 ≤ j := by omega
  by_cases he : j % 2 = 1
  · apply walsh_derivative_comp_zero_of_kernel Q20 _ _ (unitBit n 1 + unitBit n j)
    · exact compress_pair_same ⟨1, by omega⟩ ⟨j, by omega⟩ (by simp) (by simp; omega)
        (by simp; omega) (by simp; omega) (by simp; omega)
    · rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n), dot_unitBit _ (⟨j, by omega⟩ : Fin n)]
      simp [adjacentMask, unitBit, show (1 : ℕ) ≠ j - 1 by omega,
        show (1 : ℕ) ≠ j by omega, show j ≠ j - 1 by omega]
  · apply walsh_derivative_comp_zero_of_kernel Q20 _ _ (unitBit n 1 + unitBit n (j - 1))
    · exact compress_pair_same ⟨1, by omega⟩ ⟨j - 1, by omega⟩ (by simp) (by simp; omega)
        (by simp; omega) (by simp; omega) (by simp; omega)
    · rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n), dot_unitBit _ (⟨j - 1, by omega⟩ : Fin n)]
      simp [adjacentMask, unitBit, show (1 : ℕ) ≠ j - 1 by omega,
        show (1 : ℕ) ≠ j by omega, show j - 1 ≠ j by omega]

/-- 三个小维数仅作固定有限证书；任意更高维数另有核平移证明。 -/
theorem q_low_DY_int : ∀ n : Fin 8, 5 ≤ n.val → ∀ j : Fin n.val,
    1 ≤ j.val → j.val < n.val - 1 →
    intWalsh (derivative q (internalYMask n.val j.val))
      (internalYCharacter n.val j.val) = 0 := by decide

theorem walsh_DQ_Y {n : ℕ} (hn : 5 ≤ n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) :
    walsh (derivative q (internalYMask n j)) (internalYCharacter n j) = 0 := by
  by_cases hn8 : n < 8
  · exact walsh_of_int_zero _ _ (q_low_DY_int ⟨n, hn8⟩ hn
      ⟨j, by change j < n; omega⟩ hj hjn)
  have hnlarge : 8 ≤ n := by omega
  by_cases hj1 : j = 1
  · subst j
    apply walsh_DQ_zero_endpoint hn
    rw [dot_endpointShift hn]
    simp [internalYCharacter, unitBit, tailMask, show n - 2 ≠ 0 by omega,
      show n - 1 ≠ 0 by omega, show 2 ≤ n - 2 by omega, show 2 ≤ n - 1 by omega]
    decide
  by_cases hjlast : j = n - 2
  · subst j
    apply walsh_DQ_zero_endpoint hn
    rw [dot_endpointShift hn]
    simp [internalYCharacter, unitBit, tailMask, show (0 : ℕ) ≠ n - 2 - 1 by omega,
      show ¬ n - 2 + 1 ≤ 0 by omega, show n - 2 ≠ n - 2 - 1 by omega,
      show n - 1 ≠ n - 2 - 1 by omega, show n - 2 + 1 ≤ n - 1 by omega]
  have hjlo : 2 ≤ j := by omega
  have hjhi : j < n - 2 := by omega
  by_cases hj2 : j = 2
  · subst j
    apply walsh_derivative_comp_zero_of_kernel Q20 _ _ (unitBit n 2 + unitBit n 4)
    · exact compress_pair_same ⟨2, by omega⟩ ⟨4, by omega⟩ (by simp) (by simp; omega)
        (by simp) (by simp; omega) (by simp)
    · rw [dot_add, dot_unitBit _ (⟨2, by omega⟩ : Fin n), dot_unitBit _ (⟨4, by omega⟩ : Fin n)]
      simp [internalYCharacter, unitBit, tailMask]
  by_cases hj3 : j = 3
  · subst j
    apply walsh_derivative_comp_zero_of_kernel Q20 _ _ (unitBit n 1 + unitBit n 5)
    · exact compress_pair_same ⟨1, by omega⟩ ⟨5, by omega⟩ (by simp) (by simp; omega)
        (by simp) (by simp; omega) (by simp)
    · rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n), dot_unitBit _ (⟨5, by omega⟩ : Fin n)]
      simp [internalYCharacter, unitBit, tailMask]
  have hj4 : 4 ≤ j := by omega
  by_cases he : (j - 1) % 2 = 0
  · apply walsh_derivative_comp_zero_of_kernel Q20 _ _ (unitBit n 2 + unitBit n (j - 1))
    · exact compress_pair_same ⟨2, by omega⟩ ⟨j - 1, by omega⟩ (by simp) (by simp; omega)
        (by simp; omega) (by simp; omega) (by simp; omega)
    · rw [dot_add, dot_unitBit _ (⟨2, by omega⟩ : Fin n), dot_unitBit _ (⟨j - 1, by omega⟩ : Fin n)]
      simp [internalYCharacter, unitBit, tailMask, show (2 : ℕ) ≠ j - 1 by omega,
        show ¬ j + 1 ≤ 2 by omega, show ¬ j + 1 ≤ j - 1 by omega]
  · apply walsh_derivative_comp_zero_of_kernel Q20 _ _ (unitBit n 1 + unitBit n (j - 1))
    · exact compress_pair_same ⟨1, by omega⟩ ⟨j - 1, by omega⟩ (by simp) (by simp; omega)
        (by simp; omega) (by simp; omega) (by simp; omega)
    · rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n), dot_unitBit _ (⟨j - 1, by omega⟩ : Fin n)]
      simp [internalYCharacter, unitBit, tailMask, show (1 : ℕ) ≠ j - 1 by omega,
        show ¬ j + 1 ≤ 1 by omega, show ¬ j + 1 ≤ j - 1 by omega]

end UnifiedEJM

