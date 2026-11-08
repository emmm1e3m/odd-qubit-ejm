import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureEdges

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeFacts1728 : NodeFacts 1728 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0022 support0048 1 transition0172 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0048, supportNumbers0048, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0022 support0049 1 transition0173 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0049, supportNumbers0049, fromList]

theorem nodeTailFacts1728 : NodeTailFacts 1728 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0022 support0048 1 transition0174 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0048 support0634 1 transition0175 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0634 support0635 1 finish0082 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0022 support0048 1 transition0174 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0048 support0636 1 transition0176 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0636 support0048 1 finish0083 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0022 support0637 1 transition0177 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0637 support0638 1 transition0178 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0638 support0639 1 finish0084 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0022 support0637 1 transition0177 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0637 support0640 1 transition0179 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0640 support0641 2 finish0085 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1729 : NodeFacts 1729 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0023 support0050 1 transition0180 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0023 support0051 1 transition0181 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1729 : NodeTailFacts 1729 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0023 support0050 1 transition0182 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0023 support0050 1 transition0182 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0023 support0643 1 transition0185 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0023 support0643 1 transition0185 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1730 : NodeFacts 1730 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0084 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0084 support0148 1 transition0656 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0148, supportNumbers0148, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0084 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0084 support0149 1 transition0657 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0149, supportNumbers0149, fromList]

theorem nodeTailFacts1730 : NodeTailFacts 1730 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0084 support0148 1 transition0658 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0148 support0960 1 transition0659 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0960 support0961 1 finish0264 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0084 support0148 1 transition0658 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0148 support0962 1 transition0660 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0962 support0148 1 finish0265 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0084 support0963 1 transition0661 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0963 support0616 1 transition0662 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0084 support0963 1 transition0661 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0963 support0618 1 transition0663 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0084 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1731 : NodeFacts 1731 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0085 support0084 2 transition0664 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0085 support0085 2 transition0665 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1731 : NodeTailFacts 1731 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0085 support0084 2 transition0666 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 support0148 1 transition0345 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0148 support0679 1 finish0152 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0085 support0084 2 transition0666 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 support0149 1 transition0346 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0149 support0148 2 finish0153 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0085 support0757 2 transition0667 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0757 support0616 2 transition0348 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0085 support0757 2 transition0667 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0757 support0618 2 transition0349 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0085 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1732 : NodeFacts 1732 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0236 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0236 support0326 1 transition1702 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0326, supportNumbers0326, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0236 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0236 support0327 1 transition1703 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0327, supportNumbers0327, fromList]

theorem nodeTailFacts1732 : NodeTailFacts 1732 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0236 support0326 1 transition1704 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0326 support1438 1 transition1705 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1438 support1439 1 finish0534 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0236 support0326 1 transition1704 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0326 support1440 1 transition1706 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1440 support0326 1 finish0535 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0236 support1441 1 transition1707 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1441 support0976 1 transition1708 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0236 support1441 1 transition1707 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1441 support0978 1 transition1709 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1733 : NodeFacts 1733 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0237 support0236 2 transition1710 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0237 support0237 2 transition1711 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1733 : NodeTailFacts 1733 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0237 support0236 2 transition1712 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0236 support0326 1 transition1143 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0326 support1217 1 finish0412 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0237 support0236 2 transition1712 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0236 support0327 1 transition1144 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0327 support0326 2 finish0413 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0237 support1218 2 transition1713 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1218 support0976 2 transition1146 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0237 support1218 2 transition1713 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1218 support0978 2 transition1147 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1734 : NodeFacts 1734 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0050 support0096 1 transition0396 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0096, supportNumbers0096, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0050 support0097 1 transition0397 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0097, supportNumbers0097, fromList]

theorem nodeTailFacts1734 : NodeTailFacts 1734 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0050 support0096 1 transition0398 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0096 support0791 1 transition0399 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0791 support0792 1 finish0174 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0050 support0096 1 transition0398 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0096 support0793 1 transition0400 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0793 support0096 1 finish0175 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0050 support0794 1 transition0401 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0794 support0540 1 transition0402 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0050 support0794 1 transition0401 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0794 support0542 1 transition0403 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 11) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 11) (1 / (2 : ℚ) ^ 10) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1735 : NodeFacts 1735 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0051 support0050 2 transition0404 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0051 support0051 2 transition0405 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1735 : NodeTailFacts 1735 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0051 support0050 2 transition0406 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0051 support0050 2 transition0406 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0051 support0643 2 transition0407 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0051 support0643 2 transition0407 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1736 : NodeFacts 1736 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0162 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0162 support0246 1 transition1204 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0246, supportNumbers0246, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0162 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0162 support0247 1 transition1205 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0247, supportNumbers0247, fromList]

theorem nodeTailFacts1736 : NodeTailFacts 1736 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0162 support0246 1 transition1206 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0246 support1250 1 transition1191 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1250 support1251 1 finish0430 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0162 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0162 support0246 1 transition1206 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0246 support1252 1 transition1192 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1252 support0246 1 finish0431 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0162 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0162 support1254 1 transition1207 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1254 support1255 1 transition1208 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1255 support1256 1 finish0434 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0162 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0162 support1254 1 transition1207 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1254 support1257 1 transition1209 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1257 support1258 2 finish0435 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0162 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1737 : NodeFacts 1737 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0163 support0050 1 transition1210 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0163 support0051 1 transition1211 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1737 : NodeTailFacts 1737 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0163 support0050 1 transition1212 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0163 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0163 support0050 1 transition1212 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0163 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0163 support0643 1 transition1213 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0163 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0163 support0643 1 transition1213 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0163 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1738 : NodeFacts 1738 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0096 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0096 support0164 1 transition0744 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0164, supportNumbers0164, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0096 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0096 support0165 1 transition0745 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0165, supportNumbers0165, fromList]

theorem nodeTailFacts1738 : NodeTailFacts 1738 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0096 support0164 1 transition0746 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0164 support1010 1 transition0747 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1010 support1011 1 finish0292 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0096 support0164 1 transition0746 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0164 support1012 1 transition0748 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1012 support0164 1 finish0293 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0096 support1013 1 transition0749 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1013 support1014 1 transition0750 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1014 support1015 1 finish0294 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0096 support1013 1 transition0749 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1013 support1016 1 transition0751 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1016 support1017 2 finish0295 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1739 : NodeFacts 1739 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0097 support0050 1 transition0752 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0097 support0051 1 transition0753 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1739 : NodeTailFacts 1739 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0097 support0050 1 transition0754 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0097 support0050 1 transition0754 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0097 support0643 1 transition0755 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0097 support0643 1 transition0755 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1740 : NodeFacts 1740 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0243 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0243 support0157 1 transition1750 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0157, supportNumbers0157, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0243 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0243 support0334 1 transition1751 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0334, supportNumbers0334, fromList]

theorem nodeTailFacts1740 : NodeTailFacts 1740 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0243 support0157 1 transition1752 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0157 support0988 1 transition0707 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0988 support0989 1 finish0280 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0243 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0243 support0157 1 transition1752 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0157 support0990 1 transition0708 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0990 support0157 1 finish0281 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0243 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0243 support1455 1 transition1753 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1455 support1241 1 transition1754 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1241 support1242 1 finish0426 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0243 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0243 support1455 1 transition1753 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1455 support1243 1 transition1755 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1243 support1244 2 finish0427 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0243 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1741 : NodeFacts 1741 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0244 support0335 2 transition1756 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0244 support0336 2 transition1757 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1741 : NodeTailFacts 1741 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0244 support0335 2 transition1758 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0335 support1456 1 transition1759 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1456 support1457 1 finish0544 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0244 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0244 support0335 2 transition1758 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0335 support1458 1 transition1760 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1458 support0096 1 finish0545 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0244 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0244 support1459 2 transition1761 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1459 support0540 1 transition1762 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0244 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0244 support1459 2 transition1761 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1459 support0542 1 transition1763 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0244 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1742 : NodeFacts 1742 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0248 support0096 1 transition1798 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0248 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0248 support0096 1 transition1799 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0096, supportNumbers0096, fromList]

theorem nodeTailFacts1742 : NodeTailFacts 1742 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0248 support0096 1 transition1800 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0096 support0791 1 transition0399 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0791 support0792 1 finish0174 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0248 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0248 support0096 1 transition1800 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0096 support0793 1 transition0400 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0793 support0096 1 finish0175 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0248 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0248 support0096 1 transition1801 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0096 support0096 1 transition1802 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0248 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0248 support0096 1 transition1801 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0096 support0097 1 transition1803 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0248 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1743 : NodeFacts 1743 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0249 support0050 1 transition1804 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0249 support0051 1 transition1805 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1743 : NodeTailFacts 1743 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0249 support0050 1 transition1806 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0249 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0249 support0050 1 transition1806 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0249 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0249 support0643 1 transition1807 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0249 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0249 support0643 1 transition1807 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0249 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1744 : NodeFacts 1744 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0414 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0414 support0164 1 transition2818 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0164, supportNumbers0164, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0414 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0414 support0343 1 transition2819 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0343, supportNumbers0343, fromList]

theorem nodeTailFacts1744 : NodeTailFacts 1744 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0414 support0164 1 transition2820 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0164 support1010 1 transition0747 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1010 support1011 1 finish0292 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0414 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0414 support0164 1 transition2820 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0164 support1012 1 transition0748 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1012 support0164 1 finish0293 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0414 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0414 support1475 1 transition2821 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1475 support1464 1 transition1796 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1464 support1465 1 finish0548 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0414 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0414 support1475 1 transition2821 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1475 support1466 1 transition1797 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1466 support1467 2 finish0549 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0414 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1745 : NodeFacts 1745 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0415 support0414 2 transition2822 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0415 support0415 2 transition2823 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1745 : NodeTailFacts 1745 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0415 support0414 2 transition2824 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0414 support0164 1 transition2363 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0164 support1259 1 finish0436 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0415 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0415 support0414 2 transition2824 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0414 support0343 1 transition2364 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0343 support0164 2 finish0437 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0415 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0415 support1633 2 transition2825 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1633 support1464 2 transition2366 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1464 support1465 1 finish0548 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0415 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0415 support1633 2 transition2825 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1633 support1466 2 transition2367 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1466 support1467 2 finish0549 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0415 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1746 : NodeFacts 1746 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0022 support0048 1 transition0172 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0048, supportNumbers0048, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0022 support0049 1 transition0173 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0049, supportNumbers0049, fromList]

theorem nodeTailFacts1746 : NodeTailFacts 1746 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0022 support0048 1 transition0174 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0048 support0634 1 transition0175 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0634 support0635 1 finish0082 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0022 support0048 1 transition0174 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0048 support0636 1 transition0176 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0636 support0048 1 finish0083 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0022 support0637 1 transition0177 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0637 support0638 1 transition0178 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0638 support0639 1 finish0084 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0022 support0637 1 transition0177 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0637 support0640 1 transition0179 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0640 support0641 2 finish0085 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0022 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1747 : NodeFacts 1747 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0023 support0050 1 transition0180 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0023 support0051 1 transition0181 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1747 : NodeTailFacts 1747 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0023 support0050 1 transition0182 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0023 support0050 1 transition0182 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0023 support0643 1 transition0185 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0023 support0643 1 transition0185 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0023 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1748 : NodeFacts 1748 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0335 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0335 support0411 1 transition2344 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0411, supportNumbers0411, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0335 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0335 support0412 1 transition2345 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0412, supportNumbers0412, fromList]

theorem nodeTailFacts1748 : NodeTailFacts 1748 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0335 support0411 1 transition2346 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0411 support1619 1 transition2331 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1619 support1620 1 finish0622 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0335 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0335 support0411 1 transition2346 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0411 support1621 1 transition2332 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1621 support0411 1 finish0623 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0335 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0335 support1623 1 transition2347 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1623 support1624 1 transition2348 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1624 support1625 1 finish0626 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0335 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0335 support1623 1 transition2347 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1623 support1626 1 transition2349 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1626 support1627 2 finish0627 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0335 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1749 : NodeFacts 1749 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0336 support0050 1 transition2350 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0336 support0051 1 transition2351 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1749 : NodeTailFacts 1749 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0336 support0050 1 transition2352 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0336 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0336 support0050 1 transition2352 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0336 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0336 support0643 1 transition2353 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0336 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0336 support0643 1 transition2353 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0336 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1750 : NodeFacts 1750 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0455 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0455 support0411 1 transition3044 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0411, supportNumbers0411, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0455 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0455 support0454 1 transition3045 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0454, supportNumbers0454, fromList]

theorem nodeTailFacts1750 : NodeTailFacts 1750 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0455 support0411 1 transition3046 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0411 support1619 1 transition2331 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1619 support1620 1 finish0622 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0455 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0455 support0411 1 transition3046 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0411 support1621 1 transition2332 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1621 support0411 1 finish0623 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0455 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0455 support1734 1 transition3047 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1734 support0630 1 transition2800 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0630 support0631 1 finish0080 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0455 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0455 support1734 1 transition3047 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1734 support0632 1 transition2801 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0632 support0633 2 finish0081 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0455 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1751 : NodeFacts 1751 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0456 support0090 2 transition3048 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0456 support0091 2 transition3049 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1751 : NodeTailFacts 1751 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0456 support0090 2 transition3050 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0090 support0773 1 transition0375 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0773 support0774 1 finish0164 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0456 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0456 support0090 2 transition3050 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0090 support0775 1 transition0376 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0775 support0096 1 finish0165 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0456 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0456 support0776 2 transition3051 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0776 support0540 1 transition0378 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0456 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0456 support0776 2 transition3051 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0776 support0542 1 transition0379 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0456 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1752 : NodeFacts 1752 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0341 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0341 support0246 1 transition2380 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0246, supportNumbers0246, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0341 (1 / (2 : ℚ) ^ 8) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0341 support0340 1 transition2381 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0340, supportNumbers0340, fromList]

theorem nodeTailFacts1752 : NodeTailFacts 1752 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0341 support0246 1 transition2382 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0246 support1250 1 transition1191 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1250 support1251 1 finish0430 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0341 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0341 support0246 1 transition2382 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0246 support1252 1 transition1192 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1252 support0246 1 finish0431 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0341 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0341 support1473 1 transition2383 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1473 support1001 1 transition1782 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1001 support1002 1 finish0288 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0341 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0341 support1473 1 transition2383 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1473 support1003 1 transition1783 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1003 support1004 2 finish0289 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0341 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1753 : NodeFacts 1753 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0342 support0022 2 transition2384 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0342 support0023 2 transition2385 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1753 : NodeTailFacts 1753 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0342 support0022 2 transition2386 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0022 support0536 1 transition0059 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0536 support0537 1 finish0028 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0342 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0342 support0022 2 transition2386 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0022 support0538 1 transition0060 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0538 support0096 1 finish0029 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0342 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0342 support0539 2 transition2387 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0539 support0540 1 transition0062 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0342 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0342 support0539 2 transition2387 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0539 support0542 1 transition0063 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0342 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1754 : NodeFacts 1754 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0050 support0096 1 transition0396 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0096, supportNumbers0096, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0050 support0097 1 transition0397 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0097, supportNumbers0097, fromList]

theorem nodeTailFacts1754 : NodeTailFacts 1754 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0050 support0096 1 transition0398 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0096 support0791 1 transition0399 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0791 support0792 1 finish0174 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0050 support0096 1 transition0398 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0096 support0793 1 transition0400 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0793 support0096 1 finish0175 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0050 support0794 1 transition0401 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0794 support0540 1 transition0402 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0050 support0794 1 transition0401 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0794 support0542 1 transition0403 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 11) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 11) (1 / (2 : ℚ) ^ 10) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1755 : NodeFacts 1755 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0051 support0050 2 transition0404 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0051 support0051 2 transition0405 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1755 : NodeTailFacts 1755 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0051 support0050 2 transition0406 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0051 support0050 2 transition0406 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0051 support0643 2 transition0407 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0051 support0643 2 transition0407 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 10) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
