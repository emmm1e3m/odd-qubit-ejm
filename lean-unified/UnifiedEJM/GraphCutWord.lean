import UnifiedEJM.GraphTransferBridge
import UnifiedEJM.PathCutScore

noncomputable section
open OddEJM Complex
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer

/-- 实际物理颜色串按转移证书使用的两个首位和两个尾位拆分。 -/
theorem cutWord_split {m : ℕ} (S : Finset (Fin (m + 4))) :
    PathCutScore.cutWord S =
      [decide ((⟨0, by omega⟩ : Fin (m + 4)) ∈ S),
       decide ((⟨1, by omega⟩ : Fin (m + 4)) ∈ S)] ++ middleColors S ++
      [decide ((⟨m + 2, by omega⟩ : Fin (m + 4)) ∈ S),
       decide ((⟨m + 3, by omega⟩ : Fin (m + 4)) ∈ S)] := by
  exact ofFn_split_four (fun j => decide (j ∈ S))

/-- 中央至少一位时，首个中央颜色与其余颜色保持原物理顺序。 -/
theorem middleColors_cons {m : ℕ} (S : Finset (Fin ((m + 1) + 4))) :
    middleColors S = decide ((⟨2, by omega⟩ : Fin ((m + 1) + 4)) ∈ S) ::
      List.ofFn (fun j : Fin m =>
        decide ((⟨j.val + 3, by omega⟩ : Fin ((m + 1) + 4)) ∈ S)) := by
  unfold middleColors
  rw [List.ofFn_succ]
  rfl

end UnifiedEJM.WeightedTransfer

namespace UnifiedEJM.GraphBackground

/-- 有理转移权重的实值表达，与末端证书中的平方模分数一致。 -/
theorem physicalBackground_purity_transfer_re {m : ℕ} (hm : 1 ≤ m)
    (S : Finset (Fin (m + 4))) (u : ℂ) :
    (Multipartite.cutPurity S (physicalBackground (m + 4) u)).re =
      ∑ d : Bits 4, ∑ k : Bits 4,
        (WeightedTransfer.backgroundWeight
          (decide ((⟨0, by omega⟩ : Fin (m + 4)) ∈ S))
          (decide ((⟨1, by omega⟩ : Fin (m + 4)) ∈ S))
          (WeightedTransfer.middleColors S)
          (decide ((⟨m + 2, by omega⟩ : Fin (m + 4)) ∈ S))
          (decide ((⟨m + 3, by omega⟩ : Fin (m + 4)) ∈ S)) d k : ℝ) *
          normSq (codeCorrelation (physicalCoefficients (m + 4) u) d k) := by
  rw [physicalBackground_purity_transfer hm]
  simp

end UnifiedEJM.GraphBackground
