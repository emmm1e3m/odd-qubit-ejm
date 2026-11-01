import OddEJM.Core
import OddEJM.Chain
import Mathlib.Tactic
namespace OddEJM
open scoped BigOperators

/-- 相邻CNOT：j+1为控制位，j为目标位；下标从零开始。 -/
def adjacentCNOT {n : ℕ} (j : ℕ) (z : Bits n) : Bits n :=
  setBit z j (coord z j + coord z (j+1))

/-- 从最右门先执行的CNOT链；m个门的目标位依次为m-1,...,0。 -/
def rightCNOTChain {n : ℕ} : ℕ → Bits n → Bits n
  | 0, z => z
  | m+1, z => rightCNOTChain m (adjacentCNOT m z)

private def suffixSweep {n : ℕ} (m : ℕ) (z : Bits n) : Bits n :=
  fun j => if m ≤ j.val then suffix z j else z j

private theorem suffix_recurrence {n : ℕ} (z : Bits n) (j : Fin n) :
    suffix z j = z j + coord (suffix z) (j.val+1) := by
  have h := congrFun (difference_suffix z) j
  change suffix z j + coord (suffix z) (j.val+1) = z j at h
  rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem adjacent_sweep {n : ℕ} (m : ℕ) (hm : m < n) (z : Bits n) :
    adjacentCNOT m (suffixSweep (m+1) z) = suffixSweep m z := by
  funext j
  by_cases hj : j.val = m
  · have he : j = ⟨m,hm⟩ := Fin.ext hj
    subst j
    simp only [adjacentCNOT, setBit, suffixSweep, if_pos rfl, le_refl, if_true]
    have hc : coord (suffixSweep (m+1) z) m = z ⟨m,hm⟩ := by
      simp [coord, suffixSweep, hm]
    rw [hc]
    have hn : coord (suffixSweep (m+1) z) (m+1) =
        coord (suffix z) (m+1) := by
      unfold coord
      split_ifs <;> simp [suffixSweep]
    rw [hn]
    exact (suffix_recurrence z ⟨m,hm⟩).symm
  · simp only [adjacentCNOT, setBit, hj, if_false, suffixSweep]
    by_cases hlt : m < j.val
    · simp [show m+1 ≤ j.val by omega, le_of_lt hlt]
    · simp [show ¬m+1 ≤ j.val by omega, show ¬m ≤ j.val by omega]

private theorem chain_sweep {n : ℕ} (m : ℕ) (hm : m ≤ n) (z : Bits n) :
    rightCNOTChain m (suffixSweep m z) = suffix z := by
  induction m with
  | zero =>
      funext j
      simp [rightCNOTChain, suffixSweep]
  | succ m ih =>
      rw [rightCNOTChain, adjacent_sweep m (by omega)]
      exact ih (by omega)

private theorem sweep_last {n : ℕ} (hn : 0 < n) (z : Bits n) :
    suffixSweep (n-1) z = z := by
  funext j
  unfold suffixSweep
  split_ifs with h
  · have hj : j.val + 1 = n := by omega
    rw [suffix_recurrence, hj]
    simp [coord]
  · rfl

/-- 指定门序的逐CNOT位串变换恰等于后缀XOR。 -/
theorem rightCNOTChain_eq_suffix {n : ℕ} (hn : 0 < n) (z : Bits n) :
    rightCNOTChain (n-1) z = suffix z := by
  calc
    _ = rightCNOTChain (n-1) (suffixSweep (n-1) z) := by rw [sweep_last hn z]
    _ = _ := chain_sweep (n-1) (by omega) z

/-- 单个CNOT在计算基振幅上的实际作用。 -/
def adjacentCNOTAction {n : ℕ} (j : ℕ) (ψ : Vec n) : Vec n :=
  fun z => ψ (adjacentCNOT j z)

/-- 算符乘积CNOT_0 ... CNOT_(m-1)，最右算符先作用。 -/
def rightCNOTCircuit {n : ℕ} : ℕ → Vec n → Vec n
  | 0, ψ => ψ
  | m+1, ψ => rightCNOTCircuit m (adjacentCNOTAction m ψ)

private theorem adjacentCNOT_involutive {n : ℕ} (j : ℕ) (z : Bits n) :
    adjacentCNOT j (adjacentCNOT j z) = z := by
  funext k
  by_cases hk : k.val = j
  · have hj : j < n := by omega
    have he : k = ⟨j,hj⟩ := Fin.ext hk
    subst k
    by_cases hnext : j+1 < n
    · simp [adjacentCNOT, setBit, coord, hj, hnext,
        show j+1 ≠ j by omega, add_assoc, CharTwo.add_self_eq_zero]
    · simp [adjacentCNOT, setBit, coord, hj, hnext]
  · simp [adjacentCNOT, setBit, hk]

private theorem circuit_chain_cancel {n : ℕ} (m : ℕ) (ψ : Vec n) (z : Bits n) :
    rightCNOTCircuit m ψ (rightCNOTChain m z) = ψ z := by
  induction m generalizing ψ z with
  | zero => rfl
  | succ m ih =>
      simp only [rightCNOTCircuit, rightCNOTChain]
      rw [ih]
      exact congrArg ψ (adjacentCNOT_involutive m z)

/-- 实际逐门算符与公共定义中的后缀置换算符相等。 -/
theorem rightCNOTCircuit_eq_chain {n : ℕ} (hn : 0 < n) (ψ : Vec n) :
    rightCNOTCircuit (n-1) ψ = chain ψ := by
  funext z
  have h := circuit_chain_cancel (n-1) ψ (difference z)
  rw [rightCNOTChain_eq_suffix hn, suffix_difference] at h
  exact h

/-- 公共circuit严格等于题设门序S(n) H_n。 -/
theorem circuit_gate_order {n : ℕ} (hn : 0 < n) (ψ : Vec n) :
    circuit ψ = rightCNOTCircuit (n-1) (hadamardAt (n-1) ψ) := by
  rw [rightCNOTCircuit_eq_chain hn]
  rfl
end OddEJM



