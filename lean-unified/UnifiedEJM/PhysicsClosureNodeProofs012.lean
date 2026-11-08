import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureEdges

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeFacts0768 : NodeFacts 768 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0303 support0301 1 transition2134 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0303 support0302 1 transition2135 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0768 : NodeTailFacts 768 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0303 support0301 1 transition2136 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0301 support1377 1 transition1547 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1377 support1378 1 finish0498 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0303 support0301 1 transition2136 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0301 support1379 1 transition1548 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1379 support0613 1 finish0499 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0303 support1380 1 transition2137 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1380 support0737 1 transition1550 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0303 support1380 1 transition2137 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1380 support0739 1 transition1551 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0769 : NodeFacts 769 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0076 support0016 1 transition0590 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0076 support0134 1 transition0591 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0769 : NodeTailFacts 769 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0076 support0016 1 transition0592 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0510 1 transition0035 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0510 support0511 1 finish0016 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0076 support0016 1 transition0592 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0512 1 transition0036 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0512 support0513 1 finish0017 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0076 support0914 1 transition0593 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0914 support0915 1 transition0594 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0915 support0916 1 finish0240 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0076 support0914 1 transition0593 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0914 support0917 1 transition0595 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0917 support0744 1 finish0241 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0770 : NodeFacts 770 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0381 support0437 1 transition2618 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0381 support0438 1 transition2619 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0770 : NodeTailFacts 770 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0381 support0437 1 transition2620 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0437 support0076 1 transition2621 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0076 support0730 1 finish0136 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0381 support0437 1 transition2620 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0437 support0731 1 transition2622 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0731 support0088 1 finish0137 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0381 support1689 1 transition2623 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1689 support0601 2 transition2624 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0601 support0602 1 finish0064 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0381 support1689 1 transition2623 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1689 support0603 2 transition2625 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0603 support0604 1 finish0065 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0771 : NodeFacts 771 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0137 support0215 1 transition1026 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0137 support0216 1 transition1027 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0771 : NodeTailFacts 771 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0137 support0215 1 transition1028 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0215 support1159 1 transition1029 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1159 support1160 1 finish0378 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0137 support0215 1 transition1028 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0215 support1161 1 transition1030 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1161 support0522 1 finish0379 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0137 support1162 1 transition1031 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1162 support0737 1 transition1032 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0137 support1162 1 transition1031 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1162 support0739 1 transition1033 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0772 : NodeFacts 772 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0138 support0137 2 transition1034 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0138 support0138 2 transition1035 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0772 : NodeTailFacts 772 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0138 support0137 2 transition1036 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0137 support0215 1 transition0613 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0215 support0928 1 finish0246 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0138 support0137 2 transition1036 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0137 support0929 1 transition0614 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0929 support0148 1 finish0247 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0138 support0930 2 transition1037 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0930 support0737 2 transition0616 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0138 support0930 2 transition1037 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0930 support0739 2 transition0617 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0773 : NodeFacts 773 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0004 support0004 1 transition2120 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0004 support0303 1 transition2121 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0773 : NodeTailFacts 773 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0004 support0004 1 transition2122 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0004 support0919 1 transition0605 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0919 support0920 1 finish0242 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0004 support0004 1 transition2122 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0004 support0921 1 transition0606 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0921 support0922 1 finish0243 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0004 support1381 1 transition2123 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1381 support1153 1 transition1556 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1153 support1154 1 finish0374 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0004 support1381 1 transition2123 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1381 support1155 1 transition1557 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1155 support0938 1 finish0375 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0774 : NodeFacts 774 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0301 support0076 1 transition2124 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0301 support0381 1 transition2125 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0774 : NodeTailFacts 774 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0301 support0076 1 transition2126 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0076 support0726 1 transition0307 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0726 support0727 1 finish0134 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0301 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0301 support0076 1 transition2126 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0076 support0728 1 transition0308 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0728 support0729 1 finish0135 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0301 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0301 support1558 1 transition2127 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1558 support1559 1 transition2128 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1559 support1560 1 finish0592 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0301 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0301 support1558 1 transition2127 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1558 support1561 1 transition2129 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1561 support0612 1 finish0593 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0301 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0775 : NodeFacts 775 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0302 support0137 1 transition2130 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0302 support0138 1 transition2131 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0775 : NodeTailFacts 775 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0302 support0137 1 transition2132 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0137 support0215 1 transition0613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0215 support0928 1 finish0246 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0302 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0302 support0137 1 transition2132 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0137 support0929 1 transition0614 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0929 support0148 1 finish0247 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0302 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0302 support0930 1 transition2133 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0930 support0737 2 transition0616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0302 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0302 support0930 1 transition2133 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0930 support0739 2 transition0617 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0302 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0776 : NodeFacts 776 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0017 support0038 1 transition0132 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0017 support0039 1 transition0133 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0776 : NodeTailFacts 776 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0017 support0038 1 transition0134 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0038 support0596 1 transition0135 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0596 support0597 1 finish0062 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0017 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0017 support0038 1 transition0134 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0038 support0598 1 transition0136 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0598 support0599 1 finish0063 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0017 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0017 support0600 1 transition0137 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0600 support0601 1 transition0138 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0601 support0602 1 finish0064 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0017 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0017 support0600 1 transition0137 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0600 support0603 1 transition0139 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0603 support0604 1 finish0065 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0017 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0777 : NodeFacts 777 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0213 support0004 1 transition1552 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0213 support0303 1 transition1553 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0777 : NodeTailFacts 777 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0213 support0004 1 transition1554 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0004 support0919 1 transition0605 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0919 support0920 1 finish0242 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0213 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0213 support0004 1 transition1554 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0004 support0921 1 transition0606 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0921 support0922 1 finish0243 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0213 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0213 support1381 1 transition1555 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1381 support1153 1 transition1556 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1153 support1154 1 finish0374 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0213 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0213 support1381 1 transition1555 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1381 support1155 1 transition1557 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1155 support0938 1 finish0375 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0213 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0778 : NodeFacts 778 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0214 support0301 2 transition1558 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0214 support0302 2 transition1559 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0778 : NodeTailFacts 778 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0214 support0301 2 transition1560 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0301 support1377 1 transition1547 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1377 support1378 1 finish0498 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0214 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0214 support0301 2 transition1560 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0301 support1379 1 transition1548 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1379 support0613 1 finish0499 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0214 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0214 support1380 2 transition1561 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1380 support0737 1 transition1550 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0214 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0214 support1380 2 transition1561 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1380 support0739 1 transition1551 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0214 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0779 : NodeFacts 779 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0215 support0299 1 transition1562 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0215 support0304 1 transition1563 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0779 : NodeTailFacts 779 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0215 support0299 1 transition1564 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0299 support1372 1 transition1529 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1372 support1373 1 finish0496 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0215 support0299 1 transition1564 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0299 support1374 1 transition1530 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1374 support1375 1 finish0497 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0215 support1382 1 transition1565 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1382 support1383 1 transition1566 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1383 support1384 1 finish0500 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0215 support1382 1 transition1565 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1382 support1385 1 transition1567 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1385 support0954 1 finish0501 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0780 : NodeFacts 780 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0216 support0137 1 transition1568 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0216 support0138 1 transition1569 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0780 : NodeTailFacts 780 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0216 support0137 1 transition1570 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0137 support0215 1 transition0613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0215 support0928 1 finish0246 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0216 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0216 support0137 1 transition1570 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0137 support0929 1 transition0614 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0929 support0148 1 finish0247 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0216 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0216 support0930 1 transition1571 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0930 support0737 2 transition0616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0216 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0216 support0930 1 transition1571 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0930 support0739 2 transition0617 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0216 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0781 : NodeFacts 781 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0076 support0076 1 transition0596 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0076 support0135 1 transition0597 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0781 : NodeTailFacts 781 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0076 support0076 1 transition0598 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0076 support0726 1 transition0307 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0726 support0727 1 finish0134 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0076 support0076 1 transition0598 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0076 support0728 1 transition0308 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0728 support0729 1 finish0135 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0076 support0918 1 transition0599 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0918 support0601 1 transition0600 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0601 support0602 1 finish0064 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0076 support0918 1 transition0599 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0918 support0603 1 transition0601 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0603 support0604 1 finish0065 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0782 : NodeFacts 782 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0077 support0004 1 transition0602 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0077 support0136 1 transition0603 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0782 : NodeTailFacts 782 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0077 support0004 1 transition0604 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0004 support0919 1 transition0605 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0919 support0920 1 finish0242 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0077 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0077 support0004 1 transition0604 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0004 support0921 1 transition0606 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0921 support0922 1 finish0243 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0077 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0077 support0923 1 transition0607 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0923 support0924 1 transition0608 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0924 support0925 1 finish0244 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0077 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0077 support0923 1 transition0607 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0923 support0926 1 transition0609 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0926 support0927 1 finish0245 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0077 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0783 : NodeFacts 783 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0078 support0137 1 transition0610 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0078 support0138 1 transition0611 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0783 : NodeTailFacts 783 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0078 support0137 1 transition0612 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0137 support0215 1 transition0613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0215 support0928 1 finish0246 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0078 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0078 support0137 1 transition0612 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0137 support0929 1 transition0614 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0929 support0148 1 finish0247 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0078 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0078 support0930 1 transition0615 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0930 support0737 2 transition0616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0078 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0078 support0930 1 transition0615 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0930 support0739 2 transition0617 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0078 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0784 : NodeFacts 784 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0382 support0215 1 transition2626 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0382 support0215 1 transition2627 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0784 : NodeTailFacts 784 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0382 support0215 1 transition2628 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0215 support1159 1 transition1029 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1159 support1160 1 finish0378 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0382 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0382 support0215 1 transition2628 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0215 support1161 1 transition1030 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1161 support0522 1 finish0379 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0382 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0382 support0215 1 transition2629 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0215 support0215 1 transition2630 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0215 support0928 1 finish0246 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0382 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0382 support0215 1 transition2629 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0215 support0929 1 transition2631 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0929 support0148 1 finish0247 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0382 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0785 : NodeFacts 785 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0383 support0137 1 transition2632 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0383 support0138 1 transition2633 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0785 : NodeTailFacts 785 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0383 support0137 1 transition2634 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0137 support0215 1 transition0613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0215 support0928 1 finish0246 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0383 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0383 support0137 1 transition2634 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0137 support0929 1 transition0614 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0929 support0148 1 finish0247 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0383 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0383 support0930 1 transition2635 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0930 support0737 2 transition0616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0383 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0383 support0930 1 transition2635 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0930 support0739 2 transition0617 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0383 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0786 : NodeFacts 786 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0304 support0382 1 transition2138 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0304 support0383 1 transition2139 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0786 : NodeTailFacts 786 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0304 support0382 1 transition2140 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0382 support1562 1 transition2141 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1562 support1563 1 finish0594 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0304 support0382 1 transition2140 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0382 support1564 1 transition2142 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1564 support1565 1 finish0595 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0304 support1566 1 transition2143 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1566 support0737 1 transition2144 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0304 support1566 1 transition2143 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1566 support0739 1 transition2145 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0787 : NodeFacts 787 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0384 support0040 1 transition2636 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0384 support0040 1 transition2637 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0787 : NodeTailFacts 787 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0384 support0040 1 transition2638 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0040 support0605 1 transition0143 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0605 support0606 1 finish0066 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0384 support0040 1 transition2638 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0040 support0607 1 transition0144 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0607 support0599 1 finish0067 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0384 support0040 1 transition2639 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0040 support0040 1 transition2640 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0040 support1574 1 finish0600 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0384 support0040 1 transition2639 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0040 support0041 1 transition2641 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0041 support0088 1 finish0601 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0788 : NodeFacts 788 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0385 support0439 1 transition2642 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0385 support0440 1 transition2643 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0788 : NodeTailFacts 788 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0385 support0439 1 transition2644 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0439 support1690 1 transition2645 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1690 support1691 1 finish0654 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0385 support0439 1 transition2644 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0439 support1692 1 transition2646 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1692 support0613 1 finish0655 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0385 support1693 1 transition2647 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1693 support1171 1 transition2648 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0385 support1693 1 transition2647 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1693 support1173 1 transition2649 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0789 : NodeFacts 789 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0305 support0384 1 transition2146 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0305 support0385 1 transition2147 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0789 : NodeTailFacts 789 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0305 support0384 1 transition2148 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0384 support1567 1 transition2149 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1567 support1568 1 finish0596 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0305 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0305 support0384 1 transition2148 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0384 support1569 1 transition2150 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1569 support0729 1 finish0597 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0305 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0305 support1570 1 transition2151 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1570 support1571 1 transition2152 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1571 support1572 1 finish0598 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0305 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0305 support1570 1 transition2151 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1570 support1573 1 transition2153 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1573 support0604 1 finish0599 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0305 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0790 : NodeFacts 790 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0218 support0040 1 transition1584 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0218 support0307 1 transition1585 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0790 : NodeTailFacts 790 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0218 support0040 1 transition1586 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0040 support0605 1 transition0143 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0605 support0606 1 finish0066 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0218 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0218 support0040 1 transition1586 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0040 support0607 1 transition0144 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0607 support0599 1 finish0067 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0218 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0218 support1391 1 transition1587 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1391 support1392 1 transition1588 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1392 support1393 1 finish0504 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0218 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0218 support1391 1 transition1587 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1391 support1394 1 transition1589 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1394 support0612 1 finish0505 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0218 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0791 : NodeFacts 791 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0219 support0308 1 transition1590 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0219 support0309 1 transition1591 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0791 : NodeTailFacts 791 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0219 support0308 1 transition1592 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0308 support0388 1 transition1593 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0388 support1395 1 finish0506 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0219 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0219 support0308 1 transition1592 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0308 support1396 1 transition1594 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1396 support0148 1 finish0507 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0219 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0219 support1397 1 transition1595 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1397 support1171 2 transition1596 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0219 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0219 support1397 1 transition1595 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1397 support1173 2 transition1597 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0219 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0792 : NodeFacts 792 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0079 support0139 1 transition0618 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0079 support0140 1 transition0619 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0792 : NodeTailFacts 792 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0079 support0139 1 transition0620 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0139 support0931 1 transition0621 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0931 support0932 1 finish0248 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0079 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0079 support0139 1 transition0620 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0139 support0933 1 transition0622 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0933 support0922 1 finish0249 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0079 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0079 support0934 1 transition0623 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0934 support0935 1 transition0624 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0935 support0936 1 finish0250 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0079 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0079 support0934 1 transition0623 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0934 support0937 1 transition0625 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0937 support0938 1 finish0251 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0079 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0793 : NodeFacts 793 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0386 support0040 1 transition2650 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0386 support0441 1 transition2651 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0793 : NodeTailFacts 793 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0386 support0040 1 transition2652 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0040 support0605 1 transition0143 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0605 support0606 1 finish0066 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0386 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0386 support0040 1 transition2652 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0040 support0607 1 transition0144 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0607 support0599 1 finish0067 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0386 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0386 support1694 1 transition2653 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1694 support1571 1 transition2654 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1571 support1572 1 finish0598 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0386 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0386 support1694 1 transition2653 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1694 support1573 1 transition2655 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1573 support0604 1 finish0599 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0386 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0794 : NodeFacts 794 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0387 support0439 2 transition2656 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0387 support0440 2 transition2657 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0794 : NodeTailFacts 794 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0387 support0439 2 transition2658 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0439 support1690 1 transition2645 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1690 support1691 1 finish0654 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0387 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0387 support0439 2 transition2658 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0439 support1692 1 transition2646 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1692 support0613 1 finish0655 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0387 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0387 support1693 2 transition2659 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1693 support1171 1 transition2648 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0387 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0387 support1693 2 transition2659 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1693 support1173 1 transition2649 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0387 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0795 : NodeFacts 795 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0388 support0299 1 transition2660 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0388 support0442 1 transition2661 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0795 : NodeTailFacts 795 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0388 support0299 1 transition2662 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0299 support1372 1 transition1529 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1372 support1373 1 finish0496 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0388 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0388 support0299 1 transition2662 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0299 support1374 1 transition1530 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1374 support1375 1 finish0497 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0388 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0388 support1695 1 transition2663 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1695 support1696 1 transition2664 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1696 support1697 1 finish0656 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0388 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0388 support1695 1 transition2663 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1695 support1698 1 transition2665 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1698 support0954 1 finish0657 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0388 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0796 : NodeFacts 796 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0389 support0308 1 transition2666 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0389 support0309 1 transition2667 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0796 : NodeTailFacts 796 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0389 support0308 1 transition2668 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0308 support0388 1 transition1593 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0388 support1395 1 finish0506 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0389 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0389 support0308 1 transition2668 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0308 support1396 1 transition1594 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1396 support0148 1 finish0507 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0389 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0389 support1397 1 transition2669 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1397 support1171 2 transition1596 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0389 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0389 support1397 1 transition2669 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1397 support1173 2 transition1597 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0389 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0797 : NodeFacts 797 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0308 support0388 1 transition2166 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0308 support0389 1 transition2167 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0797 : NodeTailFacts 797 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0308 support0388 1 transition2168 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0388 support1576 1 transition2169 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1576 support1577 1 finish0602 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0308 support0388 1 transition2168 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0388 support1578 1 transition2170 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1578 support1565 1 finish0603 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0308 support1579 1 transition2171 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1579 support1171 1 transition2172 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0308 support1579 1 transition2171 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1579 support1173 1 transition2173 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0798 : NodeFacts 798 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0309 support0308 2 transition2174 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0309 support0309 2 transition2175 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0798 : NodeTailFacts 798 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0309 support0308 2 transition2176 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0308 support0388 1 transition1593 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0388 support1395 1 finish0506 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0309 support0308 2 transition2176 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0308 support1396 1 transition1594 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1396 support0148 1 finish0507 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0309 support1397 2 transition2177 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1397 support1171 2 transition1596 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0309 support1397 2 transition2177 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1397 support1173 2 transition1597 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0799 : NodeFacts 799 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0390 support0004 1 transition2670 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0390 support0005 1 transition2671 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0799 : NodeTailFacts 799 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0390 support0004 1 transition2672 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0004 support0919 1 transition0605 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0919 support0920 1 finish0242 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0390 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0390 support0004 1 transition2672 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0004 support0921 1 transition0606 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0921 support0922 1 finish0243 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0390 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0390 support1699 1 transition2673 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1699 support1700 1 transition2674 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1700 support1701 1 finish0658 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0390 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0390 support1699 1 transition2673 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1699 support1702 1 transition2675 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1702 support0938 1 finish0659 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0390 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0800 : NodeFacts 800 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0391 support0328 1 transition2676 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0391 support0329 1 transition2677 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0800 : NodeTailFacts 800 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0391 support0328 1 transition2678 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0328 support1442 1 transition1723 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1442 support1443 1 finish0536 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0391 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0391 support0328 1 transition2678 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0328 support1444 1 transition1724 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1444 support0148 1 finish0537 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0391 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0391 support1445 1 transition2679 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1445 support0616 1 transition1726 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0391 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0391 support1445 1 transition2679 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1445 support0618 1 transition1727 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0391 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0801 : NodeFacts 801 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0315 support0144 1 transition2212 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0315 support0397 1 transition2213 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0801 : NodeTailFacts 801 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0315 support0144 1 transition2214 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0315 support0144 1 transition2214 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0315 support1589 1 transition2215 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1589 support1590 1 transition2216 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1590 support1591 1 finish0610 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0315 support1589 1 transition2215 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1589 support1592 1 transition2217 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1592 support0954 1 finish0611 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0802 : NodeFacts 802 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0316 support0399 1 transition2224 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0316 support0400 1 transition2225 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0802 : NodeTailFacts 802 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0316 support0399 1 transition2226 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0399 support0315 1 transition2227 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0315 support1414 1 finish0518 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0316 support0399 1 transition2226 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0399 support0398 1 transition2228 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0398 support0148 1 finish0519 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0316 support1594 1 transition2229 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1594 support0524 2 transition2230 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0524 support0525 1 finish0022 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0316 support1594 1 transition2229 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1594 support0526 2 transition2231 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0526 support0527 1 finish0023 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0803 : NodeFacts 803 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0084 support0148 1 transition0656 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0084 support0149 1 transition0657 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0803 : NodeTailFacts 803 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0084 support0148 1 transition0658 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0148 support0960 1 transition0659 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0960 support0961 1 finish0264 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0084 support0148 1 transition0658 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0148 support0962 1 transition0660 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0962 support0148 1 finish0265 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0084 support0963 1 transition0661 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0963 support0616 1 transition0662 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0084 support0963 1 transition0661 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0963 support0618 1 transition0663 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0804 : NodeFacts 804 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0085 support0084 2 transition0664 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0085 support0085 2 transition0665 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0804 : NodeTailFacts 804 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0085 support0084 2 transition0666 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 support0148 1 transition0345 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0148 support0679 1 finish0152 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0085 support0084 2 transition0666 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 support0149 1 transition0346 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0149 support0148 2 finish0153 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0085 support0757 2 transition0667 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0757 support0616 2 transition0348 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0085 support0757 2 transition0667 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0757 support0618 2 transition0349 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0805 : NodeFacts 805 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0044 support0044 1 transition0350 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0044 support0044 1 transition0351 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0805 : NodeTailFacts 805 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0044 support0044 1 transition0352 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0044 support0619 1 transition0159 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0619 support0620 1 finish0074 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0044 support0044 1 transition0352 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0044 support0621 1 transition0160 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0621 support0044 1 finish0075 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0044 support0044 1 transition0353 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0044 support0044 1 transition0354 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0044 support0682 1 finish0154 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0044 support0044 1 transition0353 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0044 support0319 1 transition0355 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0319 support0044 2 finish0155 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0806 : NodeFacts 806 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0044 support0044 1 transition0668 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0044 support0150 1 transition0669 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0806 : NodeTailFacts 806 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0044 support0044 1 transition0670 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0044 support0619 1 transition0159 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0619 support0620 1 finish0074 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0044 support0044 1 transition0670 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0044 support0621 1 transition0160 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0621 support0044 1 finish0075 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0044 support0964 1 transition0671 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0964 support0965 1 transition0672 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0965 support0966 1 finish0266 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0044 support0964 1 transition0671 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0964 support0967 1 transition0673 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0967 support0725 2 finish0267 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0044 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0807 : NodeFacts 807 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0392 support0088 1 transition2680 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0392 support0088 1 transition2681 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0807 : NodeTailFacts 807 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0392 support0088 1 transition2682 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0088 support0766 1 transition0367 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0766 support0767 1 finish0160 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0392 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0392 support0088 1 transition2682 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0088 support0768 1 transition0368 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0768 support0088 1 finish0161 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0392 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0392 support0088 1 transition2683 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0088 support0088 1 transition2684 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0088 support1655 1 finish0660 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0392 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0392 support0088 1 transition2683 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0088 support0408 1 transition2685 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0408 support0088 2 finish0661 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0392 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0808 : NodeFacts 808 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0393 support0142 1 transition2686 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0393 support0143 1 transition2687 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0808 : NodeTailFacts 808 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0393 support0142 1 transition2688 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0142 support0943 1 transition0635 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0943 support0944 1 finish0254 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0393 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0393 support0142 1 transition2688 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0142 support0945 1 transition0636 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0945 support0148 1 finish0255 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0393 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0393 support0946 1 transition2689 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0946 support0616 1 transition0638 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0393 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0393 support0946 1 transition2689 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0946 support0618 1 transition0639 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0393 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0809 : NodeFacts 809 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0222 support0044 1 transition1608 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0222 support0311 1 transition1609 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0809 : NodeTailFacts 809 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0222 support0044 1 transition1610 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0044 support0619 1 transition0159 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0619 support0620 1 finish0074 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0222 support0044 1 transition1610 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0044 support0621 1 transition0160 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0621 support0044 1 finish0075 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0222 support1402 1 transition1611 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1402 support1403 1 transition1612 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1403 support1404 1 finish0510 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0222 support1402 1 transition1611 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1402 support1405 1 transition1613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1405 support0518 2 finish0511 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0810 : NodeFacts 810 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0394 support0328 1 transition2690 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0394 support0329 1 transition2691 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0810 : NodeTailFacts 810 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0394 support0328 1 transition2692 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0328 support1442 1 transition1723 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1442 support1443 1 finish0536 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0394 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0394 support0328 1 transition2692 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0328 support1444 1 transition1724 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1444 support0148 1 finish0537 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0394 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0394 support1445 1 transition2693 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1445 support0616 1 transition1726 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0394 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0394 support1445 1 transition2693 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1445 support0618 1 transition1727 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0394 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0811 : NodeFacts 811 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0328 support0088 1 transition2302 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0328 support0408 1 transition2303 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0811 : NodeTailFacts 811 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0328 support0088 1 transition2304 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0088 support0766 1 transition0367 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0766 support0767 1 finish0160 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0328 support0088 1 transition2304 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0088 support0768 1 transition0368 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0768 support0088 1 finish0161 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0328 support1606 1 transition2305 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1606 support1607 1 transition2306 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1607 support1608 1 finish0616 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0328 support1606 1 transition2305 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1606 support1609 1 transition2307 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1609 support0612 2 finish0617 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0812 : NodeFacts 812 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0329 support0084 1 transition2308 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0329 support0085 1 transition2309 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0812 : NodeTailFacts 812 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0329 support0084 1 transition2310 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 support0148 1 transition0345 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0148 support0679 1 finish0152 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0329 support0084 1 transition2310 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 support0149 1 transition0346 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0149 support0148 2 finish0153 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0329 support0757 1 transition2311 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0757 support0616 2 transition0348 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0329 support0757 1 transition2311 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0757 support0618 2 transition0349 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0813 : NodeFacts 813 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0229 support0229 1 transition1654 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0229 support0229 1 transition1655 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0813 : NodeTailFacts 813 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0229 support0229 1 transition1656 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0229 support1193 1 transition1105 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1193 support1194 1 finish0400 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0229 support0229 1 transition1656 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0229 support1195 1 transition1106 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1195 support0229 1 finish0401 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0229 support0229 1 transition1657 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0229 support0229 1 transition1658 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0229 support1315 1 finish0522 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0229 support0229 1 transition1657 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0229 support0401 1 transition1659 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0401 support0229 2 finish0523 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0814 : NodeFacts 814 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0230 support0317 1 transition1660 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0230 support0318 1 transition1661 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0814 : NodeTailFacts 814 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0230 support0317 1 transition1662 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0317 support1419 1 transition1663 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1419 support1420 1 finish0524 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0230 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0230 support0317 1 transition1662 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0317 support1421 1 transition1664 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1421 support0148 1 finish0525 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0230 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0230 support1422 1 transition1665 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1422 support0616 1 transition1666 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0230 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0230 support1422 1 transition1665 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1422 support0618 1 transition1667 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0230 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0815 : NodeFacts 815 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0148 support0229 1 transition1102 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0148 support0230 1 transition1103 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0815 : NodeTailFacts 815 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0148 support0229 1 transition1104 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0229 support1193 1 transition1105 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1193 support1194 1 finish0400 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0148 support0229 1 transition1104 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0229 support1195 1 transition1106 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1195 support0229 1 finish0401 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0148 support1196 1 transition1107 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1196 support1197 1 transition1108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1197 support1198 1 finish0402 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0148 support1196 1 transition1107 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1196 support1199 1 transition1109 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1199 support0954 2 finish0403 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0816 : NodeFacts 816 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0149 support0084 1 transition1110 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0149 support0085 1 transition1111 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0816 : NodeTailFacts 816 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0149 support0084 1 transition1112 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 support0148 1 transition0345 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0148 support0679 1 finish0152 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0149 support0084 1 transition1112 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 support0149 1 transition0346 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0149 support0148 2 finish0153 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0149 support0757 1 transition1113 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0757 support0616 2 transition0348 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0149 support0757 1 transition1113 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0757 support0618 2 transition0349 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0817 : NodeFacts 817 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0144 support0144 1 transition1074 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0144 support0144 1 transition1075 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0817 : NodeTailFacts 817 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0144 support0144 1 transition1076 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0144 support0144 1 transition1076 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0144 support0144 1 transition1077 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0144 1 transition1078 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0144 support1185 1 finish0394 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0144 support0144 1 transition1077 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0314 1 transition1079 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0314 support0229 1 finish0395 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0818 : NodeFacts 818 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0314 support0395 1 transition2204 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0314 support0396 1 transition2205 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0818 : NodeTailFacts 818 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0314 support0395 1 transition2206 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0395 support0908 1 transition2207 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0908 support1508 1 finish0608 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0314 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0314 support0395 1 transition2206 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0395 support1587 1 transition2208 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1587 support0908 2 finish0609 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0314 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0314 support1588 1 transition2209 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1588 support1204 1 transition2210 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0314 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0314 support1588 1 transition2209 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1588 support1206 1 transition2211 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0314 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0819 : NodeFacts 819 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0144 support0144 1 transition1622 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0144 support0314 1 transition1623 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0819 : NodeTailFacts 819 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0144 support0144 1 transition1624 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0144 support0144 1 transition1624 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0144 support1407 1 transition1625 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1407 support1408 1 transition1626 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1408 support1409 1 finish0514 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0144 support1407 1 transition1625 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1407 support1410 1 transition1627 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1410 support0913 1 finish0515 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0820 : NodeFacts 820 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0395 support0144 1 transition2694 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0395 support0443 1 transition2695 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0820 : NodeTailFacts 820 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0395 support0144 1 transition2696 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0395 support0144 1 transition2696 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0395 support1703 1 transition2697 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1703 support1704 1 transition2698 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1704 support1705 1 finish0662 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0395 support1703 1 transition2697 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1703 support1706 1 transition2699 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1706 support0913 1 finish0663 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0821 : NodeFacts 821 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0396 support0320 1 transition2700 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0396 support0321 1 transition2701 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0821 : NodeTailFacts 821 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0396 support0320 1 transition2702 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0320 support0229 1 transition1677 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0229 support1315 1 finish0522 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0396 support0320 1 transition2702 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0320 support0401 1 transition1678 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0401 support0229 2 finish0523 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0396 support1427 1 transition2703 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1427 support1204 2 transition1680 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0396 support1427 1 transition2703 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1427 support1206 2 transition1681 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0822 : NodeFacts 822 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0397 support0444 1 transition2704 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0397 support0445 1 transition2705 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0822 : NodeTailFacts 822 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0397 support0444 1 transition2706 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0444 support1707 1 transition2707 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1707 support1708 1 finish0664 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0397 support0444 1 transition2706 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0444 support1709 1 transition2708 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1709 support0613 1 finish0665 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0397 support1710 1 transition2709 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1710 support0957 1 transition2710 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0957 support0958 1 finish0262 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0397 support1710 1 transition2709 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1710 support0959 1 transition2711 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0959 support0527 1 finish0263 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0823 : NodeFacts 823 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0398 support0042 1 transition2712 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0398 support0043 1 transition2713 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0823 : NodeTailFacts 823 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0398 support0042 1 transition2714 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0042 support0613 1 transition0151 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0613 support0562 1 finish0070 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0398 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0398 support0042 1 transition2714 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0042 support0614 1 transition0152 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0614 support0613 2 finish0071 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0398 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0398 support0615 1 transition2715 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0615 support0616 1 transition0154 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0398 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0398 support0615 1 transition2715 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0615 support0618 1 transition0155 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0398 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0824 : NodeFacts 824 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0082 support0144 1 transition0640 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0082 support0145 1 transition0641 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0824 : NodeTailFacts 824 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0082 support0144 1 transition0642 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0082 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0082 support0144 1 transition0642 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0082 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0082 support0950 1 transition0645 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0950 support0951 1 transition0646 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0951 support0952 1 finish0258 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0082 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0082 support0950 1 transition0645 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0950 support0953 1 transition0647 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0953 support0954 1 finish0259 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0082 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0825 : NodeFacts 825 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0083 support0146 1 transition0648 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0083 support0147 1 transition0649 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0825 : NodeTailFacts 825 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0083 support0146 1 transition0650 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0146 support0082 1 transition0651 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0082 support0955 1 finish0260 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0083 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0083 support0146 1 transition0650 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0146 support0226 1 transition0652 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0226 support0148 1 finish0261 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0083 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0083 support0956 1 transition0653 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0956 support0957 2 transition0654 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0957 support0958 1 finish0262 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0083 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0083 support0956 1 transition0653 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0956 support0959 2 transition0655 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0959 support0527 1 finish0263 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0083 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0826 : NodeFacts 826 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0224 support0315 1 transition1628 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0224 support0315 1 transition1629 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0826 : NodeTailFacts 826 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0224 support0315 1 transition1630 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0315 support1411 1 transition1631 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1411 support1412 1 finish0516 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0224 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0224 support0315 1 transition1630 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0315 support1413 1 transition1632 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1413 support0613 1 finish0517 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0224 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0224 support0315 1 transition1633 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0315 support0315 1 transition1634 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0315 support1414 1 finish0518 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0224 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0224 support0315 1 transition1633 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0315 support0398 1 transition1635 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0398 support0148 1 finish0519 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0224 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0827 : NodeFacts 827 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0225 support0042 1 transition1636 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0225 support0043 1 transition1637 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0827 : NodeTailFacts 827 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0225 support0042 1 transition1638 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0042 support0613 1 transition0151 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0613 support0562 1 finish0070 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0225 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0225 support0042 1 transition1638 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0042 support0614 1 transition0152 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0614 support0613 2 finish0071 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0225 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0225 support0615 1 transition1639 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0615 support0616 1 transition0154 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0225 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0225 support0615 1 transition1639 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0615 support0618 1 transition0155 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0225 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0828 : NodeFacts 828 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0399 support0315 1 transition2716 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0399 support0398 1 transition2717 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0828 : NodeTailFacts 828 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0399 support0315 1 transition2718 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0315 support1411 1 transition1631 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1411 support1412 1 finish0516 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0399 support0315 1 transition2718 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0315 support1413 1 transition1632 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1413 support0613 1 finish0517 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0399 support1593 1 transition2719 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1593 support0524 1 transition2222 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0524 support0525 1 finish0022 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0399 support1593 1 transition2719 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1593 support0526 1 transition2223 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0526 support0527 1 finish0023 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0829 : NodeFacts 829 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0400 support0042 2 transition2720 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0400 support0043 2 transition2721 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0829 : NodeTailFacts 829 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0400 support0042 2 transition2722 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0042 support0613 1 transition0151 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0613 support0562 1 finish0070 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0400 support0042 2 transition2722 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0042 support0614 1 transition0152 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0614 support0613 2 finish0071 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0400 support0615 2 transition2723 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0615 support0616 1 transition0154 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0400 support0615 2 transition2723 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0615 support0618 1 transition0155 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0830 : NodeFacts 830 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0229 support0229 1 transition2232 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0229 support0401 1 transition2233 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0830 : NodeTailFacts 830 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0229 support0229 1 transition2234 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0229 support1193 1 transition1105 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1193 support1194 1 finish0400 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0229 support0229 1 transition2234 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0229 support1195 1 transition1106 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1195 support0229 1 finish0401 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0229 support1595 1 transition2235 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1595 support1204 1 transition2236 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0229 support1595 1 transition2235 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1595 support1206 1 transition2237 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0229 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0831 : NodeFacts 831 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0401 support0320 1 transition2724 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0401 support0321 1 transition2725 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0831 : NodeTailFacts 831 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0401 support0320 1 transition2726 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0320 support0229 1 transition1677 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0229 support1315 1 finish0522 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0401 support0320 1 transition2726 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0320 support0401 1 transition1678 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0401 support0229 2 finish0523 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0401 support1427 1 transition2727 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1427 support1204 2 transition1680 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0401 support1427 1 transition2727 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1427 support1206 2 transition1681 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
