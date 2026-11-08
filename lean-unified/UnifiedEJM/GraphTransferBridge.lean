import UnifiedEJM.GraphPurity
import UnifiedEJM.GraphScoreBounds
import UnifiedEJM.GraphTransferWeight

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

/-- 原门实际背景纯度与211的有理加权转移签名完全一致。
    中央位数m任意且m≥1；不需要有限见证长度、秩零空间或路径谱假设。 -/
theorem physicalBackground_purity_transfer {m : ℕ} (hm : 1≤m)
    (S : Finset (Fin (m+4))) (u : ℂ) :
    Multipartite.cutPurity S (physicalBackground (m+4) u) =
      ∑ d : Bits 4, ∑ k : Bits 4,
        (WeightedTransfer.backgroundWeight
          (decide ((⟨0, by omega⟩ : Fin (m+4))∈S))
          (decide ((⟨1, by omega⟩ : Fin (m+4))∈S))
          (WeightedTransfer.middleColors S)
          (decide ((⟨m+2, by omega⟩ : Fin (m+4))∈S))
          (decide ((⟨m+3, by omega⟩ : Fin (m+4))∈S)) d k : ℂ) *
          (Complex.normSq (codeCorrelation (physicalCoefficients (m+4) u) d k) : ℂ) := by
  rw [physicalBackground_purity_weighted (by omega)]
  simp_rw [WeightedTransfer.physicalWeight_eq_backgroundWeight hm]

/-- 最终加权转移中使用的真实分数是非负且不超过一的实数。 -/
theorem transfer_score_bounds (n : ℕ) (t : ℝ) :
    ∀ d k, 0 ≤ Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k) ∧
      Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k) ≤ 1 :=
  physical_angle_score_bounds n t

end UnifiedEJM.GraphBackground
