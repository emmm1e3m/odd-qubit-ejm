import OddEJM.Core

namespace OddEJM
open scoped BigOperators

/-- 相邻后缀的模二差分还原原始位。 -/
theorem difference_suffix {n : ℕ} (z : Bits n) : difference (suffix z) = z := by
  funext j
  have hnext : coord (suffix z) (j.val + 1) =
      ∑ k : Fin n, if j < k then z k else 0 := by
    unfold coord
    split_ifs with h
    · unfold suffix
      apply Finset.sum_congr rfl
      intro k hk
      congr 1

    · symm
      apply Finset.sum_eq_zero
      intro k hk
      simp only [ite_eq_right_iff]
      intro hlt
      omega
  change suffix z j + coord (suffix z) (j.val + 1) = z j
  rw [hnext]
  unfold suffix
  rw [← Finset.sum_add_distrib]
  calc
    (∑ k : Fin n, ((if j ≤ k then z k else 0) + (if j < k then z k else 0))) =
        ∑ k : Fin n, if k = j then z j else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases heq : k = j
      · subst k
        simp
      · by_cases hlt : j < k
        · simp [heq, hlt, le_of_lt hlt, CharTwo.add_self_eq_zero]
        · have hle : ¬ j ≤ k := by omega
          simp [heq, hlt, hle]
    _ = z j := by simp

/-- 后缀XOR是置换，因此计算基振幅重排保内积。 -/
noncomputable def suffixEquiv (n : ℕ) : Bits n ≃ Bits n :=
  Equiv.ofBijective suffix ⟨Function.LeftInverse.injective difference_suffix,
    Finite.surjective_of_injective (Function.LeftInverse.injective difference_suffix)⟩

theorem suffix_difference {n : ℕ} (z : Bits n) : suffix (difference z) = z := by
  obtain ⟨w, rfl⟩ := (suffixEquiv n).surjective z
  change suffix (difference (suffix w)) = suffix w
  rw [difference_suffix]

def differenceEquiv (n : ℕ) : Bits n ≃ Bits n where
  toFun := difference
  invFun := suffix
  left_inv := suffix_difference
  right_inv := difference_suffix

theorem chain_inner {n : ℕ} (ψ φ : Vec n) :
    inner (chain ψ) (chain φ) = inner ψ φ := by
  exact Equiv.sum_comp (differenceEquiv n) (fun z => star (ψ z) * φ z)

end OddEJM


