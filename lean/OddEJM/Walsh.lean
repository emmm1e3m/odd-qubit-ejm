import OddEJM.Compress
import OddEJM.Character
import OddEJM.Finite

namespace OddEJM
open scoped BigOperators

/-- 从第 j 个零基坐标开始的尾字符。 -/
def tailMask (n j : ℕ) : Bits n := fun i => if j ≤ i.val then 1 else 0

def blockMask (n p : ℕ) : Bits n :=
  fun i => if 1 ≤ i.val ∧ i.val < n - 2 ∧ i.val % 2 = p then 1 else 0

/-- 压缩映射的转置；字符在每条压缩纤维上恒定。 -/
def liftMask (n : ℕ) (H : Bits 5) : Bits n :=
  H 0 • unitBit n 0 + H 1 • blockMask n 1 + H 2 • blockMask n 0 +
    H 3 • unitBit n (n - 2) + H 4 • unitBit n (n - 1)

theorem dot_smul_left {n : ℕ} (r : Bit) (k z : Bits n) :
    dot (r • k) z = r * dot k z := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_blockMask {n : ℕ} (z : Bits n) (p : ℕ) :
    dot (blockMask n p) z = blockParity z p := by
  unfold dot blockMask blockParity
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem dot_liftMask {n : ℕ} (hn : 5 ≤ n) (H : Bits 5) (z : Bits n) :
    dot (liftMask n H) z = dot H (compress z) := by
  simp only [liftMask, dot_add_left, dot_smul_left, dot_blockMask]
  rw [unitBit_dot z (⟨0, by omega⟩ : Fin n),
    unitBit_dot z (⟨n - 2, by omega⟩ : Fin n),
    unitBit_dot z (⟨n - 1, by omega⟩ : Fin n)]
  simp [dot, Fin.sum_univ_succ, compress, coord, show 0 < n by omega,
    show n - 2 < n by omega, show n - 1 < n by omega, add_assoc]

theorem walsh_lift_zero {n : ℕ} (hn : 5 ≤ n) (q : Bits 5 → Bit)
    (H : Bits 5) (h : walsh q H = 0) :
    walsh (fun z : Bits n => q (compress z)) (liftMask n H) = 0 := by
  unfold walsh at *
  simp only [dot_liftMask hn]
  exact sum_compress_zero hn (fun v => bitSign (q v + dot H v)) h

theorem walsh_Q_zero_of_even_coordinate {n : ℕ} (k : Bits n) (j : Fin n)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2) (he : j.val % 2 = 0)
    (hk : k j = 0) : walsh (fun z => Q (compress z)) k = 0 := by
  apply walsh_zero_of_affine_shift _ k (unitBit n j.val) 1
  · exact fun z => Q_compress_flip_even z j hj hjn he
  · simp only [dot_unitBit, hk, add_zero]

theorem walsh_DQ_zero_of_even_coordinate {n : ℕ} (a k : Bits n) (j : Fin n)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2) (he : j.val % 2 = 0)
    (hk : k j = 1) : walsh (derivative (fun z => Q (compress z)) a) k = 0 := by
  apply walsh_zero_of_affine_shift _ k (unitBit n j.val) 0
  · intro z
    simpa using derivative_Q_flip_even z a j hj hjn he
  · simp only [dot_unitBit, hk, zero_add]

theorem walsh_Q_first {n : ℕ} (hn : 5 ≤ n) :
    walsh (fun z : Bits n => Q (compress z)) (unitBit n 0) = 0 := by
  apply walsh_Q_zero_of_even_coordinate _ (⟨2, by omega⟩ : Fin n)
    (by simp) (by simp; omega) (by simp)
  simp [unitBit]

theorem walsh_Q_penultimate {n : ℕ} (hn : 5 ≤ n) :
    walsh (fun z : Bits n => Q (compress z)) (unitBit n (n - 2)) = 0 := by
  apply walsh_Q_zero_of_even_coordinate _ (⟨2, by omega⟩ : Fin n)
    (by simp) (by simp; omega) (by simp)
  simp [unitBit, show ¬ 2 = n - 2 by omega]

theorem tailMask_zero_eq_lift {n : ℕ} (hn : 5 ≤ n) :
    tailMask n 0 = liftMask n (decode5 31) := by
  ext i
  have hi := i.isLt
  have hp : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  by_cases h0 : i.val = 0
  · simp [tailMask, liftMask, unitBit, blockMask, decode5, h0,
      show ¬ 0 = n - 2 by omega, show ¬ 0 = n - 1 by omega]
  by_cases h2 : i.val = n - 2
  · have h21 : ¬ n - 2 = n - 1 := by omega
    simp [tailMask, liftMask, unitBit, blockMask, decode5, h2, h21,
      show ¬ n - 2 = 0 by omega] <;> decide
  by_cases h1 : i.val = n - 1
  · have h12 : ¬ n - 1 = n - 2 := by omega
    simp [tailMask, liftMask, unitBit, blockMask, decode5, h1, h12,
      show ¬ n - 1 = 0 by omega, show ¬ n - 1 < n - 2 by omega] <;> decide
  have hil : 1 ≤ i.val := by omega
  have hir : i.val < n - 2 := by omega
  rcases hp with hp | hp <;>
    simp [tailMask, liftMask, unitBit, blockMask, decode5, h0, h1, h2, hil, hir, hp] <;> decide

theorem tailMask_one_eq_lift {n : ℕ} (hn : 5 ≤ n) :
    tailMask n 1 = liftMask n (decode5 15) := by
  ext i
  have hi := i.isLt
  have hp : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  by_cases h0 : i.val = 0
  · simp [tailMask, liftMask, unitBit, blockMask, decode5, h0,
      show ¬ 0 = n - 2 by omega, show ¬ 0 = n - 1 by omega]
  by_cases h2 : i.val = n - 2
  · have h21 : ¬ n - 2 = n - 1 := by omega
    simp [tailMask, liftMask, unitBit, blockMask, decode5, h2, h21,
      show 1 ≤ n - 2 by omega] <;> decide
  by_cases h1 : i.val = n - 1
  · have h12 : ¬ n - 1 = n - 2 := by omega
    simp [tailMask, liftMask, unitBit, blockMask, decode5, h1, h12,
      show 1 ≤ n - 1 by omega, show ¬ n - 1 < n - 2 by omega] <;> decide
  have hil : 1 ≤ i.val := by omega
  have hir : i.val < n - 2 := by omega
  rcases hp with hp | hp <;>
    simp [tailMask, liftMask, unitBit, blockMask, decode5, h0, h1, h2, hil, hir, hp] <;> decide

theorem walsh_Q_tail {n : ℕ} (hn : 5 ≤ n) (j : ℕ) :
    walsh (fun z : Bits n => Q (compress z)) (tailMask n j) = 0 := by
  rcases Nat.lt_or_ge j 3 with hj | hj
  · interval_cases j
    · rw [tailMask_zero_eq_lift hn]
      exact walsh_lift_zero hn Q _ (q_walsh_zero (by simp))
    · rw [tailMask_one_eq_lift hn]
      exact walsh_lift_zero hn Q _ (q_walsh_zero (by simp))
    · by_cases hn5 : n = 5
      · subst n
        have hm : tailMask 5 2 = liftMask 5 (decode5 7) := by
          decide
        rw [hm]
        exact walsh_lift_zero (by omega) Q _ (q_walsh_zero (by simp))
      · have hn6 : 6 ≤ n := by omega
        let w := unitBit n 1 + unitBit n 3
        have hc : compress w = 0 := by
          dsimp [w]
          rw [compress_add, compress_second hn,
            compress_internal_odd (⟨3, by omega⟩ : Fin n) (by simp) (by simp; omega) (by simp)]
          exact bits_add_self _
        apply walsh_zero_of_affine_shift _ (tailMask n 2) w 0
        · intro z
          simp only [compress_add, hc, add_zero]
        · dsimp [w]
          rw [dot_add, dot_unitBit _ (⟨1, by omega⟩ : Fin n),
            dot_unitBit _ (⟨3, by omega⟩ : Fin n)]
          simp [tailMask]
  · apply walsh_Q_zero_of_even_coordinate _ (⟨2, by omega⟩ : Fin n)
      (by simp) (by simp; omega) (by simp)
    simp [tailMask, show ¬ j ≤ 2 by omega]

def adjacentMask (n j : ℕ) : Bits n := unitBit n (j - 1) + unitBit n j

def internalYMask (n j : ℕ) : Bits n := adjacentMask n j + unitBit n (n - 1)

def internalYCharacter (n j : ℕ) : Bits n := unitBit n (j - 1) + tailMask n (j + 1)

theorem derivative_Q_Xfirst_y : ∀ v : Bits 5,
    derivative Q (unitBit 5 0 + unitBit 5 1) (v + unitBit 5 3) =
      derivative Q (unitBit 5 0 + unitBit 5 1) v + 1 := by
  decide

theorem derivative_Q_Ylast_y : ∀ v : Bits 5,
    derivative Q (unitBit 5 1 + unitBit 5 2 + unitBit 5 4) (v + unitBit 5 3) =
      derivative Q (unitBit 5 1 + unitBit 5 2 + unitBit 5 4) v := by
  decide

theorem derivative_compress {n : ℕ} (a z : Bits n) :
    derivative (fun v => Q (compress v)) a z =
      derivative Q (compress a) (compress z) := by
  simp [derivative, compress_add]

theorem walsh_DQ_Xfirst {n : ℕ} (hn : 5 ≤ n) :
    walsh (derivative (fun z => Q (compress z)) (adjacentMask n 1))
      (adjacentMask n 1) = 0 := by
  have ha : compress (adjacentMask n 1) = unitBit 5 0 + unitBit 5 1 := by
    simp only [adjacentMask, Nat.sub_self, compress_add, compress_first hn, compress_second hn]
  apply walsh_zero_of_affine_shift _ _ (unitBit n (n - 2)) 1
  · intro z
    simp only [derivative_compress, compress_add, compress_penultimate hn, ha]
    exact derivative_Q_Xfirst_y _
  · rw [dot_unitBit _ (⟨n - 2, by omega⟩ : Fin n)]
    simp [adjacentMask, unitBit, show ¬ n - 2 = 0 by omega,
      show ¬ n - 2 = 1 by omega]

theorem walsh_DQ_X {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) :
    walsh (derivative (fun z => Q (compress z)) (adjacentMask n j))
      (adjacentMask n j) = 0 := by
  have hnp : n % 2 = 1 := Nat.odd_iff.mp ho
  by_cases hj1 : j = 1
  · subst j
    exact walsh_DQ_Xfirst hn
  by_cases he : j % 2 = 0
  · have hji : j < n - 2 := by omega
    apply walsh_DQ_zero_of_even_coordinate _ _ (⟨j, by omega⟩ : Fin n) hj hji he
    simp [adjacentMask, unitBit, show ¬ j = j - 1 by omega]
  · have hji : j - 1 < n - 2 := by omega
    have hep : (j - 1) % 2 = 0 := by omega
    apply walsh_DQ_zero_of_even_coordinate _ _ (⟨j - 1, by omega⟩ : Fin n)
      (by simp; omega) hji hep
    simp [adjacentMask, unitBit, show ¬ j - 1 = j by omega]

theorem walsh_DQ_Ylast {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) :
    walsh (derivative (fun z => Q (compress z)) (internalYMask n (n - 3)))
      (internalYCharacter n (n - 3)) = 0 := by
  have hnp : n % 2 = 1 := Nat.odd_iff.mp ho
  have hsub : n - 3 - 1 = n - 4 := by omega
  have ha : compress (internalYMask n (n - 3)) =
      unitBit 5 1 + unitBit 5 2 + unitBit 5 4 := by
    simp only [internalYMask, adjacentMask, compress_add, hsub]
    rw [compress_internal_odd (⟨n - 4, by omega⟩ : Fin n) (by simp; omega)
      (by simp; omega) (by simp; omega),
      compress_internal_even (⟨n - 3, by omega⟩ : Fin n) (by simp; omega)
      (by simp; omega) (by simp; omega), compress_last hn]
  apply walsh_zero_of_affine_shift _ _ (unitBit n (n - 2)) 0
  · intro z
    simp only [derivative_compress, compress_add, compress_penultimate hn, ha, add_zero]
    exact derivative_Q_Ylast_y _
  · rw [dot_unitBit _ (⟨n - 2, by omega⟩ : Fin n)]
    simp [internalYCharacter, unitBit, tailMask, hsub,
      show ¬ n - 2 = n - 4 by omega, show n - 3 + 1 ≤ n - 2 by omega]

theorem walsh_DQ_Y {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) :
    walsh (derivative (fun z => Q (compress z)) (internalYMask n j))
      (internalYCharacter n j) = 0 := by
  have hnp : n % 2 = 1 := Nat.odd_iff.mp ho
  by_cases hj1 : j = 1
  · subst j
    apply walsh_DQ_zero_of_even_coordinate _ _ (⟨2, by omega⟩ : Fin n)
      (by simp) (by simp; omega) (by simp)
    simp [internalYCharacter, unitBit, tailMask]
  by_cases hex : j = n - 3
  · subst j
    exact walsh_DQ_Ylast hn ho
  by_cases he : j % 2 = 0
  · have hji : j + 2 < n - 2 := by omega
    have hep : (j + 2) % 2 = 0 := by omega
    apply walsh_DQ_zero_of_even_coordinate _ _ (⟨j + 2, by omega⟩ : Fin n)
      (by simp) hji hep
    simp [internalYCharacter, unitBit, tailMask, show ¬ j + 2 = j - 1 by omega]
  · have hji : j - 1 < n - 2 := by omega
    have hep : (j - 1) % 2 = 0 := by omega
    apply walsh_DQ_zero_of_even_coordinate _ _ (⟨j - 1, by omega⟩ : Fin n)
      (by simp; omega) hji hep
    simp [internalYCharacter, unitBit, tailMask, show ¬ j + 1 ≤ j - 1 by omega]

end OddEJM
