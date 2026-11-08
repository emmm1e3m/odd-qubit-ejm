import UnifiedEJM.PhysicsClosureInitialFacts
import UnifiedEJM.PhysicsClosureTerminalFacts
import UnifiedEJM.PhysicsCorrelationBound
import UnifiedEJM.GraphNormalization

open OddEJM Complex
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
open UnifiedEJM.GraphBackground
open UnifiedEJM.WeightedTransfer.FiniteClosure

private theorem toggle_fold (cs : List Bool) (p : Bool) :
    cs.foldl (fun p _ => !p) p = if cs.length % 2 = 0 then p else !p := by
  induction cs generalizing p with
  | nil => simp
  | cons c cs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_cons]
      have hm : cs.length % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases h : cs.length % 2 = 0
      · have h' : (cs.length + 1) % 2 ≠ 0 := by omega
        simp [h, h']
      · have h' : (cs.length + 1) % 2 = 0 := by omega
        simp [h, h']

private theorem toggle_true_length (cs : List Bool) :
    cs.foldl (fun p _ => !p) true = decide ((cs.length + 5) % 2 ≠ 0) := by
  rw [toggle_fold]
  have hm : cs.length % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : cs.length % 2 = 0
  · have h' : (cs.length + 5) % 2 ≠ 0 := by omega
    simp [h, h']
  · have h' : (cs.length + 5) % 2 = 0 := by omega
    simp [h, h']

/-- 元数据保持的是实际颜色词的计分递推，非见证词长度。 -/
theorem run_scan (first second third : Bool) (middle : List Bool)
    (j : Fin 1756) (hrun : run nextNode (initialNode first second third) middle = some j) :
    nodeScan j = middle.foldl scanStep (scanFirstThree first second third) := by
  have h := run_some_metadata nextNode nodeScan scanStep
    (by
      intro i c k hk
      have hm := next_metadata i c
      rw [hk] at hm
      exact hm.1)
    (initialNode first second third) middle j hrun
  simpa only [initialNode_scan] using h

/-- 中央每增加一站翻转一次长度奇偶；固定两尾站不改变该奇偶。 -/
theorem run_parity (first second third : Bool) (middle : List Bool)
    (j : Fin 1756) (hrun : run nextNode (initialNode first second third) middle = some j) :
    (nodeData j).parity = decide ((middle.length + 5) % 2 ≠ 0) := by
  have h := run_some_metadata nextNode (fun i => (nodeData i).parity)
    (fun p _ => !p)
    (by
      intro i c k hk
      have hm := next_metadata i c
      rw [hk] at hm
      exact hm.2)
    (initialNode first second third) middle j hrun
  simpa only [initialNode_parity, toggle_true_length] using h

/-- 全部长度、全部分数二颜色词的背景S函数加权和至多3/8。
有限项只负责表内转移、吸收质量和真实三角系数；任意长后缀由列表归纳处理。 -/
theorem background_weighted_score_le_three_eighths
    (first second third : Bool) (middle : List Bool) (pen last : Bool) (t : ℝ)
    (hscore : cutScore (first :: second :: third :: (middle ++ [pen, last])) = 2) :
    (∑ d, ∑ k, (backgroundWeight first second (third :: middle) pen last d k : ℝ) *
      Complex.normSq (codeCorrelation
        (physicalCoefficients (middle.length + 5) (anglePhase t)) d k)) ≤ 3 / 8 := by
  let n := middle.length + 5
  have hn : 5 ≤ n := by dsimp [n]; omega
  let score : Logical → Logical → ℝ := fun d k =>
    Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k)
  have hnorm : ∀ d k, score d k ≤ 1 := by
    intro d k
    exact codeCorrelation_normSq_le_one (physicalCoefficients n (anglePhase t))
      (physicalCoefficients_normalized n (anglePhase t) (anglePhase_norm t)) d k
  have h := observationScore_le_three_eighths nodeDecode nodeCurrent centralSite nextNode
    [⟨pen, penultimateWord⟩, ⟨last, firstWord⟩] ⟨last, firstWord⟩ score
    (fun i => (nodeData i).parity = decide (n % 2 ≠ 0) ∧ terminalScore i pen last = 2)
    node_nonneg
    (by
      intro i c j hij
      have hi := allNodeFacts i c
      simpa only [hij] using hi)
    (by
      intro i c hic
      have hi := allNodeFacts i c
      simpa only [hic] using hi)
    hnorm
    (by
      intro i hi
      exact node_observation_bound hn i pen last t hi.1 hi.2)
    (initialNode first second third) middle
    (by
      intro j hj
      refine ⟨run_parity first second third middle j hj, ?_⟩
      exact terminal_score_two first second third middle pen last (nodeScan j)
        (run_scan first second third middle j hj) hscore)
  simpa only [observationScore, backgroundWeight_initialNode] using h

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
