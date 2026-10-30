import OddEJM.Core
import OddEJM.Split
import OddEJM.Chain
import OddEJM.Character
import Mathlib.Tactic

namespace OddEJM
open scoped BigOperators

private theorem sqrt2_norm : star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = (1 : ℂ) / 2 := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, hs]
  norm_num

/-- 单比特实际Hadamard振幅变换保内积。 -/
theorem hadamardAt_inner_fin {n : ℕ} (j : Fin n) (ψ φ : Vec n) :
    inner (hadamardAt j.val ψ) (hadamardAt j.val φ) = inner ψ φ := by
  unfold inner
  rw [sum_split_bit j, sum_split_bit j]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [hadamardAt, setBit_joinBit, coord_joinBit, bitSign_zero,
    bitSign_one, one_mul, neg_one_mul]
  simp only [star_mul, star_add, star_neg]
  have hm (a b : ℂ) :
      (a * star ((Real.sqrt 2 : ℂ)⁻¹)) * ((Real.sqrt 2 : ℂ)⁻¹ * b) = (a*b)/2 := by
    calc
      _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) * (a*b) := by ring
      _ = _ := by rw [sqrt2_norm]; ring
  rw [hm, hm]
  ring

theorem hadamardAt_inner {n : ℕ} (j : ℕ) (hj : j < n) (ψ φ : Vec n) :
    inner (hadamardAt j ψ) (hadamardAt j φ) = inner ψ φ :=
  hadamardAt_inner_fin ⟨j,hj⟩ ψ φ

/-- C_n = 后缀XOR接末位Hadamard的实际算符保内积。 -/
theorem circuit_inner {n : ℕ} (hn : 0 < n) (ψ φ : Vec n) :
    inner (circuit ψ) (circuit φ) = inner ψ φ := by
  unfold circuit
  rw [chain_inner]
  exact hadamardAt_inner (n-1) (by omega) ψ φ

end OddEJM


