import UnifiedEJM.PhysicsClosureAllLengths
import UnifiedEJM.GraphCutWord
import UnifiedEJM.GraphTailBridge
import UnifiedEJM.PhysicsPurityNine

noncomputable section
open OddEJM Complex
open scoped BigOperators

namespace UnifiedEJM.GraphBackground
open WeightedTransfer PathCutScore
open WeightedTransfer.SparseCertificate.Generated

/-- 闭包证书作用于实际颜色串，长度取真实物理系统的长度。 -/
theorem physicalBackground_score_two_bound {m : ℕ}
    (S : Finset (Fin ((m + 1) + 4))) (t : ℝ)
    (hscore : cutScore (cutWord S) = 2) :
    (Multipartite.cutPurity S
      (physicalBackground ((m + 1) + 4) (anglePhase t))).re ≤ 3/8 := by
  let first := decide ((⟨0, by omega⟩ : Fin ((m + 1) + 4)) ∈ S)
  let second := decide ((⟨1, by omega⟩ : Fin ((m + 1) + 4)) ∈ S)
  let third := decide ((⟨2, by omega⟩ : Fin ((m + 1) + 4)) ∈ S)
  let pen := decide ((⟨m + 3, by omega⟩ : Fin ((m + 1) + 4)) ∈ S)
  let last := decide ((⟨m + 4, by omega⟩ : Fin ((m + 1) + 4)) ∈ S)
  let middle := List.ofFn (fun j : Fin m =>
    decide ((⟨j.val + 3, by omega⟩ : Fin ((m + 1) + 4)) ∈ S))
  have hmiddle : middleColors S = third :: middle := middleColors_cons S
  have hlen : middle.length = m := List.length_ofFn
  have hword : cutWord S = first :: second :: third :: (middle ++ [pen, last]) := by
    rw [cutWord_split, hmiddle]
    rfl
  have h := background_weighted_score_le_three_eighths
    first second third middle pen last t (by simpa only [← hword] using hscore)
  rw [physicalBackground_purity_transfer_re (by omega), hmiddle]
  simpa only [hlen] using h

/-- 全态扰动估计闭合所有分数二的实际非前缀割。 -/
theorem seed_score_two_lt_half {n : ℕ} (hn : 9 ≤ n)
    (S : Finset (Fin n)) (t : ℝ) (hscore : cutScore (cutWord S) = 2) :
    (Multipartite.cutPurity S (UnifiedEJM.seed n t)).re < 1/2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = (m + 1) + 4 := ⟨n - 5, by omega⟩
  apply PurityTail.actual_cutPurity_lt_half_nine hn t S
  simpa only [backgroundSeed_eq_physicalBackground] using
    physicalBackground_score_two_bound S t hscore

end UnifiedEJM.GraphBackground
