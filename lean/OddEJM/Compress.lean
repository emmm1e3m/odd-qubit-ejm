import OddEJM.Character
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace OddEJM
open scoped BigOperators

theorem at_add {n : ℕ} (x y : Bits n) (j : ℕ) :
    coord (x + y) j = coord x j + coord y j := by
  simp only [coord]
  split_ifs <;> simp

theorem blockParity_add {n : ℕ} (x y : Bits n) (p : ℕ) :
    blockParity (x + y) p = blockParity x p + blockParity y p := by
  unfold blockParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem compress_add {n : ℕ} (x y : Bits n) :
    compress (x + y) = compress x + compress y := by
  ext i
  fin_cases i <;> simp [compress, at_add, blockParity_add]

theorem dot_unitBit {n : ℕ} (z : Bits n) (j : Fin n) :
    dot z (unitBit n j.val) = z j := by
  unfold dot unitBit
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    have h : b.val ≠ j.val := fun e => hbj (Fin.ext e)
    simp [h]
  · simp

theorem unitBit_dot {n : ℕ} (z : Bits n) (j : Fin n) :
    dot (unitBit n j.val) z = z j := by
  simpa [dot, mul_comm] using dot_unitBit z j

theorem at_unitBit {n : ℕ} (j : Fin n) (k : ℕ) :
    coord (unitBit n j.val) k = if k = j.val then 1 else 0 := by
  unfold coord unitBit
  split_ifs with hk he he
  · rfl
  · rfl
  · subst k
    exact (hk j.isLt).elim
  · rfl

theorem blockParity_unitBit {n : ℕ} (j : Fin n) (p : ℕ) :
    blockParity (unitBit n j.val) p =
      if 1 ≤ j.val ∧ j.val < n - 2 ∧ j.val % 2 = p then 1 else 0 := by
  unfold blockParity unitBit
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    have h : b.val ≠ j.val := fun e => hbj (Fin.ext e)
    simp [h]
  · simp

theorem compress_unitBit {n : ℕ} (j : Fin n) :
    compress (unitBit n j.val) =
      ![if 0 = j.val then 1 else 0,
        if 1 ≤ j.val ∧ j.val < n - 2 ∧ j.val % 2 = 1 then 1 else 0,
        if 1 ≤ j.val ∧ j.val < n - 2 ∧ j.val % 2 = 0 then 1 else 0,
        if n - 2 = j.val then 1 else 0,
        if n - 1 = j.val then 1 else 0] := by
  simp only [compress, at_unitBit, blockParity_unitBit]

theorem compress_internal_even {n : ℕ} (j : Fin n)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2) (he : j.val % 2 = 0) :
    compress (unitBit n j.val) = unitBit 5 2 := by
  have h0 : ¬ 0 = j.val := by omega
  have h2 : ¬ n - 2 = j.val := by omega
  have h1 : ¬ n - 1 = j.val := by omega
  rw [compress_unitBit]
  ext i
  fin_cases i <;> simp [unitBit, hj, hjn, he, h0, h2, h1]

theorem compress_internal_odd {n : ℕ} (j : Fin n)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2) (he : j.val % 2 = 1) :
    compress (unitBit n j.val) = unitBit 5 1 := by
  have h0 : ¬ 0 = j.val := by omega
  have h2 : ¬ n - 2 = j.val := by omega
  have h1 : ¬ n - 1 = j.val := by omega
  rw [compress_unitBit]
  ext i
  fin_cases i <;> simp [unitBit, hj, hjn, he, h0, h2, h1]

theorem Q_add_A (v : Bits 5) : Q (v + unitBit 5 2) = Q v + 1 := by
  simp [Q, unitBit]
  ring

theorem Q_compress_flip_even {n : ℕ} (z : Bits n) (j : Fin n)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2) (he : j.val % 2 = 0) :
    Q (compress (z + unitBit n j.val)) = Q (compress z) + 1 := by
  rw [compress_add, compress_internal_even j hj hjn he, Q_add_A]

theorem derivative_Q_flip_even {n : ℕ} (z a : Bits n) (j : Fin n)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2) (he : j.val % 2 = 0) :
    derivative (fun v => Q (compress v)) a (z + unitBit n j.val) =
      derivative (fun v => Q (compress v)) a z := by
  dsimp only [derivative]
  have h : z + unitBit n j.val + a = z + a + unitBit n j.val := by abel
  rw [h, Q_compress_flip_even z j hj hjn he,
    Q_compress_flip_even (z + a) j hj hjn he]
  have h11 : (1 : Bit) + 1 = 0 := by decide
  linear_combination h11

theorem compress_smul {n : ℕ} (r : Bit) (z : Bits n) :
    compress (r • z) = r • compress z := by
  have hc (j : ℕ) : coord (r • z) j = r * coord z j := by
    unfold coord
    split_ifs <;> simp
  have hb (p : ℕ) : blockParity (r • z) p = r * blockParity z p := by
    simp only [blockParity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  ext i
  fin_cases i <;> simp [compress, hc, hb]

theorem compress_first {n : ℕ} (hn : 5 ≤ n) :
    compress (unitBit n 0) = unitBit 5 0 := by
  have h0 : (0 : ℕ) < n := by omega
  have h2 : ¬ n - 2 = 0 := by omega
  have h1 : ¬ n - 1 = 0 := by omega
  rw [compress_unitBit (⟨0, h0⟩ : Fin n)]
  ext i
  fin_cases i <;> simp [unitBit, h2, h1]

theorem compress_second {n : ℕ} (hn : 5 ≤ n) :
    compress (unitBit n 1) = unitBit 5 1 := by
  exact compress_internal_odd (⟨1, by omega⟩ : Fin n) (by simp) (by simp; omega) (by simp)

theorem compress_third {n : ℕ} (hn : 5 ≤ n) :
    compress (unitBit n 2) = unitBit 5 2 := by
  exact compress_internal_even (⟨2, by omega⟩ : Fin n) (by simp) (by simp; omega) (by simp)

theorem compress_penultimate {n : ℕ} (hn : 5 ≤ n) :
    compress (unitBit n (n - 2)) = unitBit 5 3 := by
  have hlt : n - 2 < n := by omega
  have h0 : ¬ 0 = n - 2 := by omega
  have h1 : ¬ n - 1 = n - 2 := by omega
  rw [compress_unitBit (⟨n - 2, hlt⟩ : Fin n)]
  ext i
  fin_cases i <;> simp [unitBit, h0, h1]

theorem compress_last {n : ℕ} (hn : 5 ≤ n) :
    compress (unitBit n (n - 1)) = unitBit 5 4 := by
  have hlt : n - 1 < n := by omega
  have h0 : ¬ 0 = n - 1 := by omega
  have h1 : ¬ n - 2 = n - 1 := by omega
  have h2 : ¬ n - 1 < n - 2 := by omega
  rw [compress_unitBit (⟨n - 1, hlt⟩ : Fin n)]
  ext i
  fin_cases i <;> simp [unitBit, h0, h1, h2]

/-- 只用五个确定坐标构造压缩的右逆。 -/
def expand5 (n : ℕ) (v : Bits 5) : Bits n :=
  v 0 • unitBit n 0 + v 1 • unitBit n 1 + v 2 • unitBit n 2 +
    v 3 • unitBit n (n - 2) + v 4 • unitBit n (n - 1)

theorem compress_expand5 {n : ℕ} (hn : 5 ≤ n) (v : Bits 5) :
    compress (expand5 n v) = v := by
  simp only [expand5, compress_add, compress_smul, compress_first hn,
    compress_second hn, compress_third hn, compress_penultimate hn, compress_last hn]
  ext i
  fin_cases i <;> simp [unitBit]

theorem compress_surjective {n : ℕ} (hn : 5 ≤ n) :
    Function.Surjective (compress (n := n)) :=
  fun v => ⟨expand5 n v, compress_expand5 hn v⟩

/-- 双重平移平均给出全维度提升；不需要枚举任何 n 位串。 -/
theorem sum_compress_zero {n : ℕ} (hn : 5 ≤ n) (F : Bits 5 → ℂ)
    (hF : ∑ v, F v = 0) : ∑ z : Bits n, F (compress z) = 0 := by
  have hshift (v : Bits 5) :
      (∑ z : Bits n, F (compress z + v)) = ∑ z : Bits n, F (compress z) := by
    calc
      _ = ∑ z : Bits n, F (compress (z + expand5 n v)) := by
        simp only [compress_add, compress_expand5 hn]
      _ = _ := Equiv.sum_comp (Equiv.addRight (expand5 n v)) (fun z => F (compress z))
  have hz (z : Bits n) : ∑ v : Bits 5, F (compress z + v) = 0 := by
    calc
      _ = ∑ v : Bits 5, F v :=
        Fintype.sum_equiv (Equiv.addLeft (compress z)) _ _ (fun _ => rfl)
      _ = 0 := hF
  have havg : (32 : ℂ) * (∑ z : Bits n, F (compress z)) = 0 := by
    calc
      _ = ∑ v : Bits 5, ∑ z : Bits n, F (compress z) := by
        simp [Fintype.card_fun]
      _ = ∑ v : Bits 5, ∑ z : Bits n, F (compress z + v) := by
        simp only [hshift]
      _ = ∑ z : Bits n, ∑ v : Bits 5, F (compress z + v) := Finset.sum_comm
      _ = 0 := by simp only [hz, Finset.sum_const_zero]
  exact (mul_eq_zero.mp havg).resolve_left (by norm_num)

end OddEJM


