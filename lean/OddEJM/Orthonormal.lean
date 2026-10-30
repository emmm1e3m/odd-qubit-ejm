import OddEJM.Core
import OddEJM.Character
import OddEJM.Phase
import OddEJM.Quantum
import Mathlib.Tactic
namespace OddEJM
open scoped BigOperators

theorem normFactor_card (n : ℕ) :
    star (normFactor n) * normFactor n * (2 : ℂ)^n = 1 := by
  have hs : (Real.sqrt ((2:ℝ)^n) : ℂ)^2 = (2:ℂ)^n := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have hn : (2 : ℂ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  unfold normFactor
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← pow_two, inv_pow, hs]
  exact inv_mul_cancel₀ hn

/-- 任意单位模相位函数所给出的全部归一化字符列正交。 -/
theorem phaseColumn_orthonormal {n : ℕ} (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (k l : Bits n) :
    inner (fun z => normFactor n * u z * character k z)
      (fun z => normFactor n * u z * character l z) = if k=l then 1 else 0 := by
  unfold inner
  calc
    _ = (star (normFactor n) * normFactor n) *
        ∑ z, star (character k z) * character l z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [star_mul]
      calc
        _ = (star (normFactor n) * normFactor n) * (star (u z) * u z) *
            (star (character k z) * character l z) := by ring
        _ = _ := by rw [hu]; ring
    _ = _ := by
      rw [character_orthogonality]
      split_ifs
      · exact normFactor_card n
      · simp

/-- 共同实际量子电路保持任意相位字符基的正交归一性。 -/
theorem phaseBasis_orthonormal {n : ℕ} (hn : 0<n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (k l : Bits n) :
    inner (circuit (fun z => normFactor n * u z * character k z))
      (circuit (fun z => normFactor n * u z * character l z)) =
      if k=l then 1 else 0 := by
  rw [circuit_inner hn]
  exact phaseColumn_orthonormal u hu k l

/-- 显式测量态的正交性只假设正比特数，适用于全部实参数。 -/
theorem measurement_orthonormal {n : ℕ} (hn : 0<n) (t : ℝ) (k l : Bits n) :
    inner (measurement n t k) (measurement n t l) = if k=l then 1 else 0 := by
  unfold measurement
  apply phaseBasis_orthonormal hn
  intro z
  rw [Complex.star_def, Complex.conj_mul',
    rawPhase_angle_norm]
  norm_num

end OddEJM

