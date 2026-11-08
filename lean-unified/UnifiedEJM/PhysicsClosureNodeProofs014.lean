import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureEdges

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeFacts0896 : NodeFacts 896 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0023 support0050 1 transition0180 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0023 support0051 1 transition0181 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0896 : NodeTailFacts 896 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0023 support0050 1 transition0182 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0023 support0050 1 transition0182 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0023 support0643 1 transition0185 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0023 support0643 1 transition0185 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0897 : NodeFacts 897 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0093 support0159 1 transition0722 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0093 support0160 1 transition0723 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0897 : NodeTailFacts 897 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0093 support0159 1 transition0724 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0159 support0997 1 transition0725 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0997 support0998 1 finish0286 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0093 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0093 support0159 1 transition0724 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0159 support0999 1 transition0726 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0999 support0246 1 finish0287 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0093 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0093 support1000 1 transition0727 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1000 support1001 1 transition0728 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1001 support1002 1 finish0288 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0093 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0093 support1000 1 transition0727 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1000 support1003 1 transition0729 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1003 support1004 2 finish0289 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0093 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0898 : NodeFacts 898 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0094 support0048 1 transition0730 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0094 support0161 1 transition0731 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0898 : NodeTailFacts 898 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0094 support0048 1 transition0732 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0048 support0634 1 transition0175 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0634 support0635 1 finish0082 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0094 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0094 support0048 1 transition0732 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0048 support0636 1 transition0176 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0636 support0048 1 finish0083 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0094 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0094 support1005 1 transition0733 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1005 support0787 1 transition0734 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0787 support0788 1 finish0172 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0094 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0094 support1005 1 transition0733 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1005 support0789 1 transition0735 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0789 support0790 2 finish0173 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0094 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0899 : NodeFacts 899 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0095 support0162 2 transition0736 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0095 support0163 2 transition0737 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0899 : NodeTailFacts 899 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0095 support0162 2 transition0738 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0162 support1006 1 transition0739 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1006 support1007 1 finish0290 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0095 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0095 support0162 2 transition0738 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0162 support1008 1 transition0740 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1008 support0096 1 finish0291 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0095 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0095 support1009 2 transition0741 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1009 support0540 1 transition0742 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0095 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0095 support1009 2 transition0741 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1009 support0542 1 transition0743 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0095 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0900 : NodeFacts 900 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0246 support0092 1 transition1772 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0246 support0339 1 transition1773 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0900 : NodeTailFacts 900 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0246 support0092 1 transition1774 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0092 support0777 1 transition0383 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0777 support0778 1 finish0166 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0246 support0092 1 transition1774 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0092 support0779 1 transition0384 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0779 support0092 1 finish0167 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0246 support1468 1 transition1775 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1468 support1469 1 transition1776 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1469 support1470 1 finish0550 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0246 support1468 1 transition1775 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1468 support1471 1 transition1777 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1471 support1472 2 finish0551 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0901 : NodeFacts 901 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0246 support0246 1 transition1778 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0246 support0340 1 transition1779 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0901 : NodeTailFacts 901 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0246 support0246 1 transition1780 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0246 support1250 1 transition1191 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1250 support1251 1 finish0430 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0246 support0246 1 transition1780 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0246 support1252 1 transition1192 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1252 support0246 1 finish0431 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0246 support1473 1 transition1781 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1473 support1001 1 transition1782 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1001 support1002 1 finish0288 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0246 support1473 1 transition1781 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1473 support1003 1 transition1783 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1003 support1004 2 finish0289 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0246 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0902 : NodeFacts 902 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0340 support0022 1 transition2376 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0340 support0023 1 transition2377 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0902 : NodeTailFacts 902 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0340 support0022 1 transition2378 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0022 support0536 1 transition0059 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0536 support0537 1 finish0028 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0340 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0340 support0022 1 transition2378 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0022 support0538 1 transition0060 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0538 support0096 1 finish0029 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0340 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0340 support0539 1 transition2379 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0539 support0540 1 transition0062 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0340 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0340 support0539 1 transition2379 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0539 support0542 1 transition0063 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0340 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0903 : NodeFacts 903 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0343 support0414 1 transition2388 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0343 support0415 1 transition2389 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0903 : NodeTailFacts 903 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0343 support0414 1 transition2390 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0414 support0164 1 transition2363 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0164 support1259 1 finish0436 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0343 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0343 support0414 1 transition2390 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0414 support0343 1 transition2364 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0343 support0164 2 finish0437 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0343 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0343 support1633 1 transition2391 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1633 support1464 2 transition2366 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1464 support1465 1 finish0548 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0343 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0343 support1633 1 transition2391 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1633 support1466 2 transition2367 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1466 support1467 2 finish0549 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0343 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0904 : NodeFacts 904 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0096 support0096 1 transition2392 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0096 support0097 1 transition2393 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0904 : NodeTailFacts 904 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0096 support0096 1 transition2394 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0096 support0791 1 transition0399 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0791 support0792 1 finish0174 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0096 support0096 1 transition2394 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0096 support0793 1 transition0400 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0793 support0096 1 finish0175 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0096 support0794 1 transition2395 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0794 support0540 1 transition0402 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0096 support0794 1 transition2395 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0794 support0542 1 transition0403 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0905 : NodeFacts 905 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0167 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0167 support0252 1 transition1236 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0252, supportNumbers0252, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0167 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0167 support0253 1 transition1237 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0253, supportNumbers0253, fromList]

theorem nodeTailFacts0905 : NodeTailFacts 905 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0167 support0252 1 transition1238 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0252 support1265 1 transition1239 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1265 support1265 1 finish0440 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0167 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0167 support0252 1 transition1238 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0252 support1266 1 transition1240 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1266 support1267 1 finish0441 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0167 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0167 support1268 1 transition1241 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1268 support0799 1 transition1242 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0799 support0252 1 finish0178 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0167 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0167 support1268 1 transition1241 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1268 support0800 1 transition1243 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0800 support0801 1 finish0179 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0167 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0906 : NodeFacts 906 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0168 support0167 2 transition1244 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0168 support0168 2 transition1245 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0906 : NodeTailFacts 906 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0168 support0167 2 transition1246 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0167 support0252 1 transition0765 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0252 support0252 1 finish0298 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0168 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0168 support0167 2 transition1246 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0167 support1022 1 transition0766 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1022 support1023 1 finish0299 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0168 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0168 support1024 2 transition1247 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1024 support0799 2 transition0768 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0799 support0252 1 finish0178 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0168 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0168 support1024 2 transition1247 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1024 support0800 2 transition0769 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0800 support0801 1 finish0179 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0168 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0907 : NodeFacts 907 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0254 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0254 support0053 1 transition1830 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0053, supportNumbers0053, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0254 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0254 support0344 1 transition1831 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0344, supportNumbers0344, fromList]

theorem nodeTailFacts0907 : NodeTailFacts 907 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0254 support0053 1 transition1832 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0053 support0648 1 transition0197 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0648 support0648 1 finish0090 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0254 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0254 support0053 1 transition1832 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0053 support0649 1 transition0198 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0649 support0650 1 finish0091 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0254 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0254 support1476 1 transition1833 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1476 support1477 1 transition1834 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1477 support0053 1 finish0552 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0254 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0254 support1476 1 transition1833 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1476 support1478 1 transition1835 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1478 support1479 1 finish0553 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0254 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0908 : NodeFacts 908 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0255 support0103 1 transition1836 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0255 support0104 1 transition1837 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0908 : NodeTailFacts 908 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0255 support0103 1 transition1838 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0103 support0173 1 transition0439 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0173 support0173 1 finish0186 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0255 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0255 support0103 1 transition1838 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0103 support0814 1 transition0440 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0814 support0815 1 finish0187 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0255 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0255 support0816 1 transition1839 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0816 support0657 2 transition0442 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0657 support0173 1 finish0096 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0255 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0255 support0816 1 transition1839 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0816 support0658 2 transition0443 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0658 support0659 1 finish0097 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0255 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0909 : NodeFacts 909 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0418 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0418 support0053 1 transition2836 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0053, supportNumbers0053, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0418 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0418 support0101 1 transition2837 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0101, supportNumbers0101, fromList]

theorem nodeTailFacts0909 : NodeTailFacts 909 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0418 support0053 1 transition2838 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0053 support0648 1 transition0197 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0648 support0648 1 finish0090 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0418 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0418 support0053 1 transition2838 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0053 support0649 1 transition0198 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0649 support0650 1 finish0091 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0418 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0418 support0806 1 transition2839 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0806 support0550 1 transition0426 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0550 support0053 1 finish0036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0418 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0418 support0806 1 transition2839 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0806 support0551 1 transition0427 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0551 support0552 1 finish0037 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0418 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0910 : NodeFacts 910 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0419 support0054 2 transition2840 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0419 support0055 2 transition2841 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0910 : NodeTailFacts 910 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0419 support0054 2 transition2842 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0054 support0653 1 transition0205 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0653 support0653 1 finish0094 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0419 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0419 support0054 2 transition2842 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0054 support0654 1 transition0206 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0654 support0655 1 finish0095 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0419 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0419 support0656 2 transition2843 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0656 support0657 1 transition0208 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0657 support0173 1 finish0096 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0419 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0419 support0656 2 transition2843 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0656 support0658 1 transition0209 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0658 support0659 1 finish0097 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0419 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0911 : NodeFacts 911 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0173 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0173 support0252 1 transition1272 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0252, supportNumbers0252, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0173 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0173 support0257 1 transition1273 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0257, supportNumbers0257, fromList]

theorem nodeTailFacts0911 : NodeTailFacts 911 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0173 support0252 1 transition1274 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0252 support1265 1 transition1239 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1265 support1265 1 finish0440 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0173 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0173 support0252 1 transition1274 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0252 support1266 1 transition1240 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1266 support1267 1 finish0441 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0173 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0173 support1274 1 transition1275 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1274 support1275 1 transition1276 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1275 support0252 1 finish0444 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0173 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0173 support1274 1 transition1275 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1274 support1276 1 transition1277 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1276 support1277 1 finish0445 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0173 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0912 : NodeFacts 912 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0174 support0103 1 transition1278 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0174 support0104 1 transition1279 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0912 : NodeTailFacts 912 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0174 support0103 1 transition1280 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0103 support0173 1 transition0439 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0173 support0173 1 finish0186 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0174 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0174 support0103 1 transition1280 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0103 support0814 1 transition0440 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0814 support0815 1 finish0187 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0174 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0174 support0816 1 transition1281 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0816 support0657 2 transition0442 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0657 support0173 1 finish0096 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0174 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0174 support0816 1 transition1281 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0816 support0658 2 transition0443 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0658 support0659 1 finish0097 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0174 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0913 : NodeFacts 913 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0103 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0103 support0173 1 transition0790 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0173, supportNumbers0173, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0103 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0103 support0174 1 transition0791 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0174, supportNumbers0174, fromList]

theorem nodeTailFacts0913 : NodeTailFacts 913 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0103 support0173 1 transition0792 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0173 support1035 1 transition0793 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1035 support1035 1 finish0306 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0103 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0103 support0173 1 transition0792 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0173 support1036 1 transition0794 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1036 support1037 1 finish0307 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0103 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0103 support1038 1 transition0795 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1038 support0657 1 transition0796 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0657 support0173 1 finish0096 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0103 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0103 support1038 1 transition0795 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1038 support0658 1 transition0797 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0658 support0659 1 finish0097 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0103 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0914 : NodeFacts 914 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0104 support0103 2 transition0798 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0104 support0104 2 transition0799 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0914 : NodeTailFacts 914 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0104 support0103 2 transition0800 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0103 support0173 1 transition0439 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0173 support0173 1 finish0186 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0104 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0104 support0103 2 transition0800 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0103 support0814 1 transition0440 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0814 support0815 1 finish0187 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0104 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0104 support0816 2 transition0801 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0816 support0657 2 transition0442 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0657 support0173 1 finish0096 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0104 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0104 support0816 2 transition0801 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0816 support0658 2 transition0443 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0658 support0659 1 finish0097 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0104 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0915 : NodeFacts 915 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0345 support0173 1 transition2404 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0345 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0345 support0173 1 transition2405 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0173, supportNumbers0173, fromList]

theorem nodeTailFacts0915 : NodeTailFacts 915 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0345 support0173 1 transition2406 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0173 support1035 1 transition0793 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1035 support1035 1 finish0306 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0345 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0345 support0173 1 transition2406 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0173 support1036 1 transition0794 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1036 support1037 1 finish0307 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0345 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0345 support0173 1 transition2407 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0173 support0173 1 transition2408 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0173 support0173 1 finish0186 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0345 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0345 support0173 1 transition2407 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0173 support0814 1 transition2409 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0814 support0815 1 finish0187 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0345 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0916 : NodeFacts 916 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0346 support0103 1 transition2410 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0346 support0104 1 transition2411 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0916 : NodeTailFacts 916 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0346 support0103 1 transition2412 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0103 support0173 1 transition0439 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0173 support0173 1 finish0186 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0346 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0346 support0103 1 transition2412 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0103 support0814 1 transition0440 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0814 support0815 1 finish0187 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0346 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0346 support0816 1 transition2413 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0816 support0657 2 transition0442 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0657 support0173 1 finish0096 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0346 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0346 support0816 1 transition2413 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0816 support0658 2 transition0443 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0658 support0659 1 finish0097 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0346 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0917 : NodeFacts 917 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0420 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0420 support0175 1 transition2844 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0175, supportNumbers0175, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0420 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0420 support1737 1 transition2845 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support1737, supportNumbers1737, fromList]

theorem nodeTailFacts0917 : NodeTailFacts 917 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0420 support0175 1 transition2846 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0175 support1039 1 transition0805 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1039 support1039 1 finish0308 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0420 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0420 support0175 1 transition2846 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0175 support1040 1 transition0806 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1040 support1041 1 finish0309 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0420 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0420 support1738 1 transition2847 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1738 support1739 1 transition2848 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1739 support0175 1 finish0676 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0420 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0420 support1738 1 transition2847 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1738 support1740 1 transition2849 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1740 support1741 1 finish0677 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0420 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0918 : NodeFacts 918 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0421 support0261 1 transition2850 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0421 support0262 1 transition2851 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0918 : NodeTailFacts 918 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0421 support0261 1 transition2852 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0261 support0351 1 transition1303 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0351 support0351 1 finish0450 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0421 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0421 support0261 1 transition2852 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0261 support1287 1 transition1304 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1287 support1288 1 finish0451 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0421 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0421 support1289 1 transition2853 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1289 support1048 2 transition1306 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1048 support0351 1 finish0314 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0421 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0421 support1289 1 transition2853 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1289 support1049 2 transition1307 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1049 support1050 1 finish0315 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0421 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0919 : NodeFacts 919 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0261 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0261 support0351 1 transition1872 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0351, supportNumbers0351, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0261 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0261 support0352 1 transition1873 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0352, supportNumbers0352, fromList]

theorem nodeTailFacts0919 : NodeTailFacts 919 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0261 support0351 1 transition1874 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0351 support1494 1 transition1875 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1494 support1494 1 finish0562 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0261 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0261 support0351 1 transition1874 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0351 support1495 1 transition1876 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1495 support1496 1 finish0563 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0261 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0261 support1497 1 transition1877 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1497 support1048 1 transition1878 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1048 support0351 1 finish0314 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0261 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0261 support1497 1 transition1877 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1497 support1049 1 transition1879 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1049 support1050 1 finish0315 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0261 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0920 : NodeFacts 920 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0262 support0261 2 transition1880 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0262 support0262 2 transition1881 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0920 : NodeTailFacts 920 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0262 support0261 2 transition1882 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0261 support0351 1 transition1303 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0351 support0351 1 finish0450 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0262 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0262 support0261 2 transition1882 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0261 support1287 1 transition1304 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1287 support1288 1 finish0451 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0262 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0262 support1289 2 transition1883 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1289 support1048 2 transition1306 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1048 support0351 1 finish0314 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0262 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0262 support1289 2 transition1883 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1289 support1049 2 transition1307 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1049 support1050 1 finish0315 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0262 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0921 : NodeFacts 921 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0351 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0351 support0252 1 transition2438 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0252, supportNumbers0252, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0351 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0351 support1645 1 transition2439 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support1645, supportNumbers1645, fromList]

theorem nodeTailFacts0921 : NodeTailFacts 921 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0351 support0252 1 transition2440 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0252 support1265 1 transition1239 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1265 support1265 1 finish0440 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0351 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0351 support0252 1 transition2440 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0252 support1266 1 transition1240 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1266 support1267 1 finish0441 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0351 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0351 support1646 1 transition2441 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1646 support1647 1 transition2442 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1647 support0252 1 finish0634 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0351 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0351 support1646 1 transition2441 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1646 support1648 1 transition2443 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1648 support1649 1 finish0635 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0351 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0922 : NodeFacts 922 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0352 support0261 1 transition2444 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0352 support0262 1 transition2445 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0922 : NodeTailFacts 922 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0352 support0261 1 transition2446 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0261 support0351 1 transition1303 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0351 support0351 1 finish0450 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0352 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0352 support0261 1 transition2446 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0261 support1287 1 transition1304 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1287 support1288 1 finish0451 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0352 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0352 support1289 1 transition2447 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1289 support1048 2 transition1306 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1048 support0351 1 finish0314 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0352 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0352 support1289 1 transition2447 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1289 support1049 2 transition1307 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1049 support1050 1 finish0315 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0352 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0923 : NodeFacts 923 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0281 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0281 support0065 1 transition2008 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0065, supportNumbers0065, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0281 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0281 support0371 1 transition2009 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0371, supportNumbers0371, fromList]

theorem nodeTailFacts0923 : NodeTailFacts 923 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0281 support0065 1 transition2010 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0065 support0584 1 transition0257 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0584 support0584 1 finish0116 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0281 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0281 support0065 1 transition2010 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0065 support0691 1 transition0258 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0691 support0692 1 finish0117 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0281 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0281 support1527 1 transition2011 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1527 support1528 1 transition2012 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1528 support0065 1 finish0576 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0281 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0281 support1527 1 transition2011 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1527 support1529 1 transition2013 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1529 support1530 1 finish0577 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0281 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0924 : NodeFacts 924 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0282 support0061 1 transition2014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0282 support0062 1 transition2015 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0924 : NodeTailFacts 924 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0282 support0061 1 transition2016 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0061 support0114 1 transition0235 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0114 support0114 1 finish0108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0282 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0282 support0061 1 transition2016 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0061 support0678 1 transition0236 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0678 support0679 1 finish0109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0282 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0282 support0680 1 transition2017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0680 support0564 2 transition0238 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0282 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0282 support0680 1 transition2017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0680 support0565 2 transition0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0282 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0925 : NodeFacts 925 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0362 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0362 support0268 1 transition2494 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0268, supportNumbers0268, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0362 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0362 support0361 1 transition2495 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0361, supportNumbers0361, fromList]

theorem nodeTailFacts0925 : NodeTailFacts 925 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0362 support0268 1 transition2496 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0268 support1305 1 transition1341 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1305 support1305 1 finish0460 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0362 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0362 support0268 1 transition2496 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0268 support1306 1 transition1342 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1306 support1307 1 finish0461 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0362 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0362 support1514 1 transition2497 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1514 support0489 1 transition1928 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0489 support0268 1 finish0006 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0362 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0362 support1514 1 transition2497 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1514 support0490 1 transition1929 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0490 support0491 1 finish0007 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0362 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0926 : NodeFacts 926 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0363 support0028 2 transition2498 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0363 support0029 2 transition2499 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0926 : NodeTailFacts 926 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0363 support0028 2 transition2500 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0028 support0560 1 transition0089 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0560 support0560 1 finish0042 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0363 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0363 support0028 2 transition2500 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0028 support0561 1 transition0090 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0561 support0562 1 finish0043 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0363 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0363 support0563 2 transition2501 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0563 support0564 1 transition0092 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0363 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0363 support0563 2 transition2501 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0563 support0565 1 transition0093 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0363 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0927 : NodeFacts 927 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0114 support0187 1 transition0866 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0187, supportNumbers0187, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0114 support0188 1 transition0867 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0188, supportNumbers0188, fromList]

theorem nodeTailFacts0927 : NodeTailFacts 927 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0114 support0187 1 transition0868 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0187 support0898 1 transition0869 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0898 support0898 1 finish0328 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0114 support0187 1 transition0868 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0187 support1072 1 transition0870 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1072 support1073 1 finish0329 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0114 support1074 1 transition0871 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1074 support1075 1 transition0872 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1075 support0187 1 finish0330 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0114 support1074 1 transition0871 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1074 support1076 1 transition0873 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1076 support1077 1 finish0331 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0928 : NodeFacts 928 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0115 support0061 1 transition0874 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0115 support0062 1 transition0875 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0928 : NodeTailFacts 928 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0115 support0061 1 transition0876 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0061 support0114 1 transition0235 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0114 support0114 1 finish0108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0115 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0115 support0061 1 transition0876 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0061 support0678 1 transition0236 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0678 support0679 1 finish0109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0115 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0115 support0680 1 transition0877 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0680 support0564 2 transition0238 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0115 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0115 support0680 1 transition0877 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0680 support0565 2 transition0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0115 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0929 : NodeFacts 929 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0061 support0114 1 transition0482 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0061 support0115 1 transition0483 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0929 : NodeTailFacts 929 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0061 support0114 1 transition0484 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0114 support0717 1 transition0485 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0717 support0717 1 finish0204 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0061 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0061 support0114 1 transition0484 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0114 support0844 1 transition0486 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0844 support0845 1 finish0205 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0061 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0061 support0846 1 transition0487 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0846 support0564 1 transition0488 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0061 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0061 support0846 1 transition0487 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0846 support0565 1 transition0489 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0061 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0930 : NodeFacts 930 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0062 support0061 2 transition0490 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0062 support0062 2 transition0491 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0930 : NodeTailFacts 930 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0062 support0061 2 transition0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0061 support0114 1 transition0235 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0114 support0114 1 finish0108 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0062 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0062 support0061 2 transition0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0061 support0678 1 transition0236 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0678 support0679 1 finish0109 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0062 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0062 support0680 2 transition0493 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0680 support0564 2 transition0238 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0062 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0062 support0680 2 transition0493 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0680 support0565 2 transition0239 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0062 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0931 : NodeFacts 931 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0065 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0065 support0030 1 transition0516 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0030, supportNumbers0030, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0065 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0065 support0120 1 transition0517 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0120, supportNumbers0120, fromList]

theorem nodeTailFacts0931 : NodeTailFacts 931 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0065 support0030 1 transition0518 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0030 support0493 1 transition0097 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0493 support0493 1 finish0046 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0065 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0065 support0030 1 transition0518 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0030 support0567 1 transition0098 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0567 support0568 1 finish0047 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0065 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0065 support0865 1 transition0519 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0865 support0866 1 transition0520 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0866 support0030 1 finish0216 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0065 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0065 support0865 1 transition0519 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0865 support0867 1 transition0521 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0867 support0868 1 finish0217 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0065 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0932 : NodeFacts 932 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0108 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0108 support0180 1 transition0826 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0180, supportNumbers0180, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0108 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0108 support0181 1 transition0827 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0181, supportNumbers0181, fromList]

theorem nodeTailFacts0932 : NodeTailFacts 932 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0108 support0180 1 transition0828 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0180 support0874 1 transition0829 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0874 support0874 1 finish0318 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0108 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0108 support0180 1 transition0828 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0180 support1055 1 transition0830 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1055 support1056 1 finish0319 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0108 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0108 support1057 1 transition0831 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1057 support1058 1 transition0832 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1058 support0180 1 finish0320 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0108 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0108 support1057 1 transition0831 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1057 support1059 1 transition0833 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1059 support1060 1 finish0321 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0108 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0933 : NodeFacts 933 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0109 support0061 1 transition0834 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0109 support0062 1 transition0835 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0933 : NodeTailFacts 933 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0109 support0061 1 transition0836 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0061 support0114 1 transition0235 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0114 support0114 1 finish0108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0109 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0109 support0061 1 transition0836 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0061 support0678 1 transition0236 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0678 support0679 1 finish0109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0109 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0109 support0680 1 transition0837 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0680 support0564 2 transition0238 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0109 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0109 support0680 1 transition0837 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0680 support0565 2 transition0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0109 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0934 : NodeFacts 934 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0371 support0427 1 transition2544 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0371 support0428 1 transition2545 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0934 : NodeTailFacts 934 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0371 support0427 1 transition2546 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0427 support0065 1 transition2547 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0065 support0065 1 finish0638 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0371 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0371 support0427 1 transition2546 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0427 support1654 1 transition2548 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1654 support1655 1 finish0639 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0371 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0371 support1673 1 transition2549 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1673 support0668 2 transition2550 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0668 support0065 1 finish0102 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0371 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0371 support1673 1 transition2549 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1673 support0669 2 transition2551 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0669 support0670 1 finish0103 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0371 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0935 : NodeFacts 935 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0187 support0187 1 transition1364 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0187 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0187 support0187 1 transition1365 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0187, supportNumbers0187, fromList]

theorem nodeTailFacts0935 : NodeTailFacts 935 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0187 support0187 1 transition1366 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0187 support0898 1 transition0869 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0898 support0898 1 finish0328 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0187 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0187 support0187 1 transition1366 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0187 support1072 1 transition0870 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1072 support1073 1 finish0329 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0187 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0187 support0187 1 transition1367 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0187 support0187 1 transition1368 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0187 support0187 1 finish0466 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0187 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0187 support0187 1 transition1367 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0187 support1314 1 transition1369 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1314 support1315 1 finish0467 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0187 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0936 : NodeFacts 936 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0270 support0114 1 transition1944 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0270 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0270 support0114 1 transition1945 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0114, supportNumbers0114, fromList]

theorem nodeTailFacts0936 : NodeTailFacts 936 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0270 support0114 1 transition1946 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0114 support0717 1 transition0485 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0717 support0717 1 finish0204 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0270 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0270 support0114 1 transition1946 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0114 support0844 1 transition0486 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0844 support0845 1 finish0205 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0270 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0270 support0114 1 transition1947 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0114 support0114 1 transition1948 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0114 support0114 1 finish0108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0270 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0270 support0114 1 transition1947 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0114 support0678 1 transition1949 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0678 support0679 1 finish0109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0270 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0937 : NodeFacts 937 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0271 support0061 1 transition1950 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0271 support0062 1 transition1951 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0937 : NodeTailFacts 937 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0271 support0061 1 transition1952 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0061 support0114 1 transition0235 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0114 support0114 1 finish0108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0271 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0271 support0061 1 transition1952 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0061 support0678 1 transition0236 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0678 support0679 1 finish0109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0271 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0271 support0680 1 transition1953 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0680 support0564 2 transition0238 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0271 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0271 support0680 1 transition1953 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0680 support0565 2 transition0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0271 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0938 : NodeFacts 938 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0188 support0270 1 transition1370 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0188 support0271 1 transition1371 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0938 : NodeTailFacts 938 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0188 support0270 1 transition1372 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0270 support1136 1 transition1373 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1136 support1136 1 finish0468 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0188 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0188 support0270 1 transition1372 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0270 support1316 1 transition1374 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1316 support1317 1 finish0469 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0188 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0188 support1318 1 transition1375 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1318 support0564 1 transition1376 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0188 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0188 support1318 1 transition1375 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1318 support0565 1 transition1377 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0188 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0939 : NodeFacts 939 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0358 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0358 support0110 1 transition2472 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0110, supportNumbers0110, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0358 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0358 support1656 1 transition2473 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support1656, supportNumbers1656, fromList]

theorem nodeTailFacts0939 : NodeTailFacts 939 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0358 support0110 1 transition2474 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0110 support0831 1 transition0469 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0831 support0831 1 finish0196 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0358 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0358 support0110 1 transition2474 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0110 support0832 1 transition0470 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0832 support0833 1 finish0197 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0358 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0358 support1657 1 transition2475 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1657 support1658 1 transition2476 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1658 support0110 1 finish0640 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0358 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0358 support1657 1 transition2475 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1657 support1659 1 transition2477 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1659 support1660 1 finish0641 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0358 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0940 : NodeFacts 940 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0359 support0273 1 transition2478 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0359 support0274 1 transition2479 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0940 : NodeTailFacts 940 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0359 support0273 1 transition2480 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0273 support0187 1 transition1387 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0187 support0187 1 finish0466 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0359 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0359 support0273 1 transition2480 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0273 support1314 1 transition1388 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1314 support1315 1 finish0467 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0359 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0359 support1323 1 transition2481 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1323 support1081 2 transition1390 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1081 support0187 1 finish0334 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0359 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0359 support1323 1 transition2481 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1323 support1082 2 transition1391 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1082 support1083 1 finish0335 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0359 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0941 : NodeFacts 941 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0273 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0273 support0187 1 transition1962 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0187, supportNumbers0187, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0273 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0273 support0364 1 transition1963 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0364, supportNumbers0364, fromList]

theorem nodeTailFacts0941 : NodeTailFacts 941 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0273 support0187 1 transition1964 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0187 support0898 1 transition0869 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0898 support0898 1 finish0328 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0273 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0273 support0187 1 transition1964 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0187 support1072 1 transition0870 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1072 support1073 1 finish0329 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0273 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0273 support1516 1 transition1965 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1516 support1081 1 transition1942 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1081 support0187 1 finish0334 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0273 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0273 support1516 1 transition1965 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1516 support1082 1 transition1943 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1082 support1083 1 finish0335 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0273 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0942 : NodeFacts 942 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0274 support0273 2 transition1966 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0274 support0274 2 transition1967 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0942 : NodeTailFacts 942 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0274 support0273 2 transition1968 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0273 support0187 1 transition1387 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0187 support0187 1 finish0466 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0274 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0274 support0273 2 transition1968 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0273 support1314 1 transition1388 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1314 support1315 1 finish0467 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0274 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0274 support1323 2 transition1969 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1323 support1081 2 transition1390 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1081 support0187 1 finish0334 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0274 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0274 support1323 2 transition1969 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1323 support1082 2 transition1391 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1082 support1083 1 finish0335 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0274 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0943 : NodeFacts 943 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0422 support0059 1 transition2854 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0422 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0422 support0059 1 transition2855 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0059, supportNumbers0059, fromList]

theorem nodeTailFacts0943 : NodeTailFacts 943 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0422 support0059 1 transition2856 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0059 support0671 1 transition0227 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0671 support0671 1 finish0104 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0422 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0422 support0059 1 transition2856 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0059 support0672 1 transition0228 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0672 support0673 1 finish0105 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0422 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0422 support0059 1 transition2857 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0059 support0059 1 transition2858 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0059 support0059 1 finish0200 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0422 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0422 support0059 1 transition2857 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0059 support0838 1 transition2859 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0838 support0839 1 finish0201 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0422 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0944 : NodeFacts 944 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0423 support0185 1 transition2860 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0423 support0186 1 transition2861 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0944 : NodeTailFacts 944 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0423 support0185 1 transition2862 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0185 support1068 1 transition0861 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1068 support1068 1 finish0326 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0423 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0423 support0185 1 transition2862 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0185 support1069 1 transition0862 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1069 support1070 1 finish0327 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0423 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0423 support1071 1 transition2863 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1071 support0564 1 transition0864 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0423 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0423 support1071 1 transition2863 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1071 support0565 1 transition0865 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0423 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0945 : NodeFacts 945 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0028 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0028 support0059 1 transition0224 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0059, supportNumbers0059, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0028 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0028 support0060 1 transition0225 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0060, supportNumbers0060, fromList]

theorem nodeTailFacts0945 : NodeTailFacts 945 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0028 support0059 1 transition0226 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0059 support0671 1 transition0227 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0671 support0671 1 finish0104 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0028 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0028 support0059 1 transition0226 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0059 support0672 1 transition0228 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0672 support0673 1 finish0105 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0028 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0028 support0674 1 transition0229 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0674 support0675 1 transition0230 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0675 support0059 1 finish0106 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0028 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0028 support0674 1 transition0229 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0674 support0676 1 transition0231 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0676 support0677 1 finish0107 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0028 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0946 : NodeFacts 946 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0029 support0061 1 transition0232 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0029 support0062 1 transition0233 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0946 : NodeTailFacts 946 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0029 support0061 1 transition0234 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0061 support0114 1 transition0235 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0114 support0114 1 finish0108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0029 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0029 support0061 1 transition0234 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0061 support0678 1 transition0236 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0678 support0679 1 finish0109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0029 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0029 support0680 1 transition0237 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0680 support0564 2 transition0238 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0029 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0029 support0680 1 transition0237 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0680 support0565 2 transition0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0029 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0947 : NodeFacts 947 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0112 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0112 support0059 1 transition0852 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0059, supportNumbers0059, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0112 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0112 support0184 1 transition0853 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0184, supportNumbers0184, fromList]

theorem nodeTailFacts0947 : NodeTailFacts 947 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0112 support0059 1 transition0854 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0059 support0671 1 transition0227 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0671 support0671 1 finish0104 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0112 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0112 support0059 1 transition0854 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0059 support0672 1 transition0228 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0672 support0673 1 finish0105 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0112 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0112 support1067 1 transition0855 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1067 support0841 1 transition0856 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0841 support0059 1 finish0202 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0112 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0112 support1067 1 transition0855 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1067 support0842 1 transition0857 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0842 support0843 1 finish0203 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0112 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0948 : NodeFacts 948 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0113 support0185 2 transition0858 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0113 support0186 2 transition0859 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0948 : NodeTailFacts 948 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0113 support0185 2 transition0860 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0185 support1068 1 transition0861 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1068 support1068 1 finish0326 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0113 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0113 support0185 2 transition0860 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0185 support1069 1 transition0862 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1069 support1070 1 finish0327 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0113 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0113 support1071 2 transition0863 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1071 support0564 1 transition0864 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0113 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0113 support1071 2 transition0863 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1071 support0565 1 transition0865 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0113 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0949 : NodeFacts 949 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0268 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0268 support0110 1 transition1918 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0110, supportNumbers0110, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0268 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0268 support0360 1 transition1919 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0360, supportNumbers0360, fromList]

theorem nodeTailFacts0949 : NodeTailFacts 949 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0268 support0110 1 transition1920 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0110 support0831 1 transition0469 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0831 support0831 1 finish0196 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0268 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0268 support0110 1 transition1920 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0110 support0832 1 transition0470 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0832 support0833 1 finish0197 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0268 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0268 support1510 1 transition1921 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1510 support1511 1 transition1922 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1511 support0110 1 finish0570 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0268 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0268 support1510 1 transition1921 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1510 support1512 1 transition1923 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1512 support1513 1 finish0571 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0268 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0950 : NodeFacts 950 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0361 support0028 1 transition2490 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0361 support0029 1 transition2491 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0950 : NodeTailFacts 950 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0361 support0028 1 transition2492 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0028 support0560 1 transition0089 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0560 support0560 1 finish0042 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0361 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0361 support0028 1 transition2492 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0028 support0561 1 transition0090 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0561 support0562 1 finish0043 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0361 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0361 support0563 1 transition2493 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0563 support0564 1 transition0092 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0361 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0361 support0563 1 transition2493 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0563 support0565 1 transition0093 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0361 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0951 : NodeFacts 951 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0364 support0273 1 transition2502 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0364 support0274 1 transition2503 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0951 : NodeTailFacts 951 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0364 support0273 1 transition2504 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0273 support0187 1 transition1387 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0187 support0187 1 finish0466 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0364 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0364 support0273 1 transition2504 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0273 support1314 1 transition1388 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1314 support1315 1 finish0467 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0364 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0364 support1323 1 transition2505 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1323 support1081 2 transition1390 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1081 support0187 1 finish0334 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0364 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0364 support1323 1 transition2505 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1323 support1082 2 transition1391 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1082 support1083 1 finish0335 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0364 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0952 : NodeFacts 952 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0114 support0114 1 transition2506 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0114 support0115 1 transition2507 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0952 : NodeTailFacts 952 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0114 support0114 1 transition2508 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0114 support0717 1 transition0485 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0717 support0717 1 finish0204 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0114 support0114 1 transition2508 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0114 support0844 1 transition0486 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0844 support0845 1 finish0205 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0114 support0846 1 transition2509 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0846 support0564 1 transition0488 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0114 support0846 1 transition2509 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0846 support0565 1 transition0489 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0114 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0953 : NodeFacts 953 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0189 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0189 support0030 1 transition1378 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0030, supportNumbers0030, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0189 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0189 support0272 1 transition1379 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0272, supportNumbers0272, fromList]

theorem nodeTailFacts0953 : NodeTailFacts 953 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0189 support0030 1 transition1380 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0030 support0493 1 transition0097 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0493 support0493 1 finish0046 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0189 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0189 support0030 1 transition1380 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0030 support0567 1 transition0098 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0567 support0568 1 finish0047 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0189 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0189 support1319 1 transition1381 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1319 support1320 1 transition1382 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1320 support0030 1 finish0470 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0189 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0189 support1319 1 transition1381 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1319 support1321 1 transition1383 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1321 support1322 1 finish0471 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0189 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0954 : NodeFacts 954 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0190 support0273 1 transition1384 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0190 support0274 1 transition1385 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0954 : NodeTailFacts 954 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0190 support0273 1 transition1386 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0273 support0187 1 transition1387 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0187 support0187 1 finish0466 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0190 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0190 support0273 1 transition1386 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0273 support1314 1 transition1388 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1314 support1315 1 finish0467 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0190 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0190 support1323 1 transition1389 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1323 support1081 2 transition1390 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1081 support0187 1 finish0334 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0190 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0190 support1323 1 transition1389 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1323 support1082 2 transition1391 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1082 support1083 1 finish0335 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0190 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0955 : NodeFacts 955 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0365 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0365 support0030 1 transition2510 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0030, supportNumbers0030, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0365 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0365 support0116 1 transition2511 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0116, supportNumbers0116, fromList]

theorem nodeTailFacts0955 : NodeTailFacts 955 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0365 support0030 1 transition2512 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0030 support0493 1 transition0097 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0493 support0493 1 finish0046 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0365 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0365 support0030 1 transition2512 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0030 support0567 1 transition0098 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0567 support0568 1 finish0047 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0365 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0365 support0847 1 transition2513 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0847 support0848 1 transition0498 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0848 support0030 1 finish0206 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0365 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0365 support0847 1 transition2513 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0847 support0849 1 transition0499 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0849 support0850 1 finish0207 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0365 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0956 : NodeFacts 956 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0366 support0189 2 transition2514 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0366 support0190 2 transition2515 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0956 : NodeTailFacts 956 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0366 support0189 2 transition2516 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0189 support0857 1 transition0881 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0857 support0857 1 finish0332 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0366 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0366 support0189 2 transition2516 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0189 support1078 1 transition0882 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1078 support1079 1 finish0333 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0366 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0366 support1080 2 transition2517 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1080 support1081 1 transition0884 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1081 support0187 1 finish0334 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0366 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0366 support1080 2 transition2517 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1080 support1082 1 transition0885 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1082 support1083 1 finish0335 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0366 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0957 : NodeFacts 957 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0012 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0012 support0030 1 transition0094 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0030, supportNumbers0030, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0012 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0012 support0031 1 transition0095 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0031, supportNumbers0031, fromList]

theorem nodeTailFacts0957 : NodeTailFacts 957 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0012 support0030 1 transition0096 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0030 support0493 1 transition0097 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0493 support0493 1 finish0046 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0012 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0012 support0030 1 transition0096 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0030 support0567 1 transition0098 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0567 support0568 1 finish0047 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0012 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0012 support0569 1 transition0099 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0569 support0570 1 transition0100 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0570 support0571 1 finish0048 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0012 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0012 support0569 1 transition0099 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0569 support0572 1 transition0101 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0572 support0573 1 finish0049 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0012 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0958 : NodeFacts 958 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0369 support0367 1 transition2532 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0369 support0368 1 transition2533 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0958 : NodeTailFacts 958 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0369 support0367 1 transition2534 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0367 support1518 1 transition1979 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1518 support0857 1 finish0572 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0369 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0369 support0367 1 transition2534 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0367 support1519 1 transition1980 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1519 support1520 1 finish0573 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0369 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0369 support1521 1 transition2535 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1521 support0861 1 transition1982 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0369 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0369 support1521 1 transition2535 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1521 support0863 1 transition1983 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0369 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0959 : NodeFacts 959 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0117 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0117 support0030 1 transition0886 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0030, supportNumbers0030, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0117 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0117 support0191 1 transition0887 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0191, supportNumbers0191, fromList]

theorem nodeTailFacts0959 : NodeTailFacts 959 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0117 support0030 1 transition0888 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0030 support0493 1 transition0097 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0493 support0493 1 finish0046 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0117 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0117 support0030 1 transition0888 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0030 support0567 1 transition0098 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0567 support0568 1 finish0047 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0117 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0117 support1084 1 transition0889 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1084 support1085 1 transition0890 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1085 support0688 1 finish0336 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0117 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0117 support1084 1 transition0889 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1084 support1086 1 transition0891 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1086 support1087 1 finish0337 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0117 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
