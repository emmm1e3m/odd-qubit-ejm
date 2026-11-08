import UnifiedEJM.Core
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open OddEJM Complex
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer

/-- 归一复向量与任意置换、单位相位像的重叠模方至多为一。 -/
theorem twistedCorrelation_normSq_le_one {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (hc : (∑ i, Complex.normSq (c i)) = 1)
    (e : ι ≃ ι) (phase : ι → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) :
    Complex.normSq (∑ i, c i * star (c (e i)) * phase i) ≤ 1 := by
  classical
  have hsum : (∑ i, ‖c i‖ ^ 2) = 1 := by
    simpa only [← Complex.normSq_eq_norm_sq] using hc
  have hperm : (∑ i, ‖c (e i)‖ ^ 2) = 1 := by
    rw [Equiv.sum_comp e (fun i => ‖c i‖ ^ 2), hsum]
  have hnorm : ‖∑ i, c i * star (c (e i)) * phase i‖ ≤ 1 := by
    calc
      ‖∑ i, c i * star (c (e i)) * phase i‖ ≤
          ∑ i, ‖c i * star (c (e i)) * phase i‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖c (e i)‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [norm_mul, hphase]
      _ ≤ Real.sqrt (∑ i, ‖c i‖ ^ 2) * Real.sqrt (∑ i, ‖c (e i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
      _ = 1 := by rw [hsum, hperm]; norm_num
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (∑ i, c i * star (c (e i)) * phase i)]

/-- 178.8的S函数；仅使用四逻辑字归一性，不需要物理跨割矩阵的谱。 -/
theorem codeCorrelation_normSq_le_one (c : Bits 4 → ℂ)
    (hc : (∑ l, Complex.normSq (c l)) = 1) (d k : Bits 4) :
    Complex.normSq (∑ l, c l * star (c (l + d)) * character (l + d) k) ≤ 1 := by
  apply twistedCorrelation_normSq_le_one c hc (Equiv.addRight d)
    (fun l => character (l + d) k)
  intro l
  by_cases h : OddEJM.dot (l + d) k = 0 <;> simp [character, bitSign, h]

end UnifiedEJM.WeightedTransfer
