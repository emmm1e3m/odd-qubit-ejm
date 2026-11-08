import UnifiedEJM.Features
import OddEJM.Pauli
import OddEJM.Walsh
import Mathlib.Tactic

open OddEJM OddEJM.CircuitPauli
open scoped BigOperators

namespace UnifiedEJM.BoundaryAmplitude

/-- 输出串中除首末各两位之外的总奇偶。 -/
def middleParity {n : ℕ} (y : Bits n) : Bit :=
  ∑ j : Fin n, if 2 ≤ j.val ∧ j.val < n - 2 then y j else 0

def middleMask (n : ℕ) : Bits n :=
  fun j => if 2 ≤ j.val ∧ j.val < n - 2 then 1 else 0

/-- 边界位按首、次、倒二、末排列。 -/
def boundary {n : ℕ} (y : Bits n) : Bits 4 :=
  ![coord y 0, coord y 1, coord y (n-2), coord y (n-1)]

/-- 末位Hadamard的两条输入支路。 -/
def inputBranch {n : ℕ} (y : Bits n) (b : Bit) : Bits n :=
  setBit (difference y) (n-1) b

private theorem edge_block_indicator (n j p : ℕ)
    (hn : 5 ≤ n) (hj : j < n) (hp : p ≤ 1) :
    ((if 1 ≤ j ∧ j < n-2 ∧ j % 2 = p then 1 else 0) : Bit) +
      (if j = 0 then 0 else if 1 ≤ j-1 ∧ j-1 < n-2 ∧ (j-1)%2 = p then 1 else 0) =
    (if 2 ≤ j ∧ j < n-2 then 1 else 0) +
      (if p = 1 then (if j = 1 then 1 else 0) else 0) +
      (if (n-3)%2 = p then (if j = n-2 then 1 else 0) else 0) := by
  interval_cases p <;>
    split_ifs <;> norm_num at * <;> omega

/-- 交替输入差分求和后成为连续输出区间，端点由长度奇偶决定。 -/
theorem edgeMask_blockMask {n : ℕ} (hn : 5 ≤ n) (p : ℕ) (hp : p ≤ 1) :
    edgeMask (blockMask n p) = middleMask n +
      (if p = 1 then unitBit n 1 else 0) +
      (if (n-3)%2 = p then unitBit n (n-2) else 0) := by
  ext j
  have h := coord_edgeMask (blockMask n p) j.val j.isLt
  have hjprev : j.val - 1 < n := by omega
  simp only [coord, dite_eq_left j.isLt, dite_eq_left hjprev, blockMask] at h
  simpa [middleMask, unitBit, Pi.add_apply, ite_apply]
    using h.trans (edge_block_indicator n j.val p hn j.isLt hp)

theorem dot_middleMask {n : ℕ} (y : Bits n) :
    dot (middleMask n) y = middleParity y := by
  unfold dot middleMask middleParity
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem blockParity_difference {n : ℕ} (hn : 5 ≤ n) (y : Bits n)
    (p : ℕ) (hp : p ≤ 1) :
    blockParity (difference y) p = middleParity y +
      (if p = 1 then coord y 1 else 0) +
      (if (n-3)%2 = p then coord y (n-2) else 0) := by
  rw [← dot_blockMask, ← dot_edgeMask, edgeMask_blockMask hn p hp,
    CircuitPauli.dot_add_left, CircuitPauli.dot_add_left, dot_middleMask]
  have hz : dot (0 : Bits n) y = 0 := by simp [dot]
  split_ifs <;> simp only [CircuitPauli.dot_unit_left, hz, add_zero]

theorem blockParity_inputBranch {n : ℕ} (y : Bits n) (b : Bit) (p : ℕ) :
    blockParity (inputBranch y b) p = blockParity (difference y) p := by
  unfold blockParity inputBranch
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : 1 ≤ j.val ∧ j.val < n-2 ∧ j.val%2 = p
  · have hj : j.val ≠ n-1 := by omega
    simp [h, setBit, hj]
  · simp [h]

theorem coord_inputBranch {n : ℕ} (hn : 0 < n) (y : Bits n) (b : Bit)
    (j : ℕ) (hj : j < n) :
    coord (inputBranch y b) j =
      if j = n-1 then b else coord y j + coord y (j+1) := by
  simp [coord, inputBranch, setBit, difference, hj]

/-- 任意n的实际电路支路特征，只依赖四个端点及中段总奇偶。 -/
theorem features_inputBranch {n : ℕ} (hn : 5 ≤ n) (y : Bits n) (b : Bit) :
    features (inputBranch y b) =
      ![coord y 0 + coord y 1 + coord y (n-2) + coord y (n-1),
        coord y 1 + middleParity y + (if n%2 = 0 then coord y (n-2) else 0),
        middleParity y + (if n%2 = 0 then 0 else coord y (n-2)),
        coord y 0 + coord y 1 + b] := by
  have he : (n-3)%2 = 1 ↔ n%2 = 0 := by omega
  have ho : (n-3)%2 = 0 ↔ ¬ n%2 = 0 := by omega
  rw [features_formula]
  simp only [blockParity_inputBranch, blockParity_difference hn y 1 (by omega),
    blockParity_difference hn y 0 (by omega)]
  simp only [coord_inputBranch (by omega) y b 0 (by omega),
    coord_inputBranch (by omega) y b (n-2) (by omega),
    coord_inputBranch (by omega) y b (n-1) (by omega)]
  have h01 : ¬ 0 = n-1 := by omega
  have h21 : ¬ n-2 = n-1 := by omega
  have hs : n-2+1 = n-1 := by omega
  by_cases hne : n%2 = 0
  · have hm : (n-3)%2 = 1 := by omega
    ext j
    fin_cases j <;> simp [h01, h21, hs, hne, hm] <;> ring
  · have hm : (n-3)%2 = 0 := by omega
    ext j
    fin_cases j <;> simp [h01, h21, hs, hne, hm] <;> ring

end UnifiedEJM.BoundaryAmplitude





