import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureEdges

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeFacts1536 : NodeFacts 1536 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0466 support0142 1 transition3100 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0466 support0143 1 transition3101 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1536 : NodeTailFacts 1536 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0466 support0142 1 transition3102 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0142 support0943 1 transition0635 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0943 support0944 1 finish0254 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0466 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0466 support0142 1 transition3102 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0142 support0945 1 transition0636 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0945 support0148 1 finish0255 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0466 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0466 support0946 1 transition3103 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0946 support0616 1 transition0638 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0466 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0466 support0946 1 transition3103 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0946 support0618 1 transition0639 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0466 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1537 : NodeFacts 1537 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0401 support0320 1 transition2724 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0401 support0321 1 transition2725 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1537 : NodeTailFacts 1537 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0401 support0320 1 transition2726 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0320 support0229 1 transition1677 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0229 support1315 1 finish0522 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0401 support0320 1 transition2726 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0320 support0401 1 transition1678 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0401 support0229 2 finish0523 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0401 support1427 1 transition2727 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1427 support1204 2 transition1680 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0401 support1427 1 transition2727 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1427 support1206 2 transition1681 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0401 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1538 : NodeFacts 1538 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0148 support0148 1 transition2728 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0148 support0149 1 transition2729 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1538 : NodeTailFacts 1538 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0148 support0148 1 transition2730 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0148 support0960 1 transition0659 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0960 support0961 1 finish0264 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0148 support0148 1 transition2730 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0148 support0962 1 transition0660 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0962 support0148 1 finish0265 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0148 support0963 1 transition2731 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0963 support0616 1 transition0662 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0148 support0963 1 transition2731 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0963 support0618 1 transition0663 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1539 : NodeFacts 1539 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0395 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0395 support0144 1 transition2694 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0144, supportNumbers0144, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0395 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0395 support0443 1 transition2695 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0443, supportNumbers0443, fromList]

theorem nodeTailFacts1539 : NodeTailFacts 1539 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0395 support0144 1 transition2696 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0395 support0144 1 transition2696 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0395 support1703 1 transition2697 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1703 support1704 1 transition2698 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1704 support1705 1 finish0662 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0395 support1703 1 transition2697 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1703 support1706 1 transition2699 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1706 support0913 1 finish0663 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0395 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1540 : NodeFacts 1540 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0396 support0320 1 transition2700 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0396 support0321 1 transition2701 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1540 : NodeTailFacts 1540 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0396 support0320 1 transition2702 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0320 support0229 1 transition1677 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0229 support1315 1 finish0522 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0396 support0320 1 transition2702 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0320 support0401 1 transition1678 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0401 support0229 2 finish0523 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0396 support1427 1 transition2703 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1427 support1204 2 transition1680 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0396 support1427 1 transition2703 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1427 support1206 2 transition1681 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0396 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1541 : NodeFacts 1541 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0467 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0467 support0144 1 transition3104 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0144, supportNumbers0144, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0467 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0467 support0314 1 transition3105 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0314, supportNumbers0314, fromList]

theorem nodeTailFacts1541 : NodeTailFacts 1541 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0467 support0144 1 transition3106 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0467 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0467 support0144 1 transition3106 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0467 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0467 support1407 1 transition3107 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1407 support1408 1 transition1626 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1408 support1409 1 finish0514 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0467 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0467 support1407 1 transition3107 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1407 support1410 1 transition1627 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1410 support0913 1 finish0515 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0467 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1542 : NodeFacts 1542 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0468 support0395 2 transition3108 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0468 support0396 2 transition3109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1542 : NodeTailFacts 1542 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0468 support0395 2 transition3110 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0395 support0908 1 transition2207 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0908 support1508 1 finish0608 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0468 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0468 support0395 2 transition3110 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0395 support1587 1 transition2208 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1587 support0908 2 finish0609 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0468 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0468 support1588 2 transition3111 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1588 support1204 1 transition2210 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0468 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0468 support1588 2 transition3111 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1588 support1206 1 transition2211 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0468 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1543 : NodeFacts 1543 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0226 support0227 1 transition1640 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0226 support0228 1 transition1641 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1543 : NodeTailFacts 1543 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0226 support0227 1 transition1642 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0227 support0735 1 transition1097 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0735 support1070 1 finish0398 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0226 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0226 support0227 1 transition1642 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0227 support1191 1 transition1098 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1191 support0735 2 finish0399 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0226 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0226 support1192 1 transition1643 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1192 support0616 1 transition1100 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0226 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0226 support1192 1 transition1643 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1192 support0618 1 transition1101 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0226 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1544 : NodeFacts 1544 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0315 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0315 support0144 1 transition2212 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0144, supportNumbers0144, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0315 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0315 support0397 1 transition2213 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0397, supportNumbers0397, fromList]

theorem nodeTailFacts1544 : NodeTailFacts 1544 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0315 support0144 1 transition2214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0315 support0144 1 transition2214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0315 support1589 1 transition2215 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1589 support1590 1 transition2216 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1590 support1591 1 finish0610 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0315 support1589 1 transition2215 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1589 support1592 1 transition2217 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1592 support0954 1 finish0611 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0315 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1545 : NodeFacts 1545 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0316 support0399 1 transition2224 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0316 support0400 1 transition2225 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1545 : NodeTailFacts 1545 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0316 support0399 1 transition2226 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0399 support0315 1 transition2227 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0315 support1414 1 finish0518 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0316 support0399 1 transition2226 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0399 support0398 1 transition2228 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0398 support0148 1 finish0519 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0316 support1594 1 transition2229 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1594 support0524 2 transition2230 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0524 support0525 1 finish0022 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0316 support1594 1 transition2229 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1594 support0526 2 transition2231 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0526 support0527 1 finish0023 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0316 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1546 : NodeFacts 1546 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0146 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0146 support0082 1 transition1088 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0082, supportNumbers0082, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0146 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0146 support0226 1 transition1089 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0226, supportNumbers0226, fromList]

theorem nodeTailFacts1546 : NodeTailFacts 1546 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0146 support0082 1 transition1090 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0082 support0750 1 transition0337 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0750 support0751 1 finish0148 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0146 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0146 support0082 1 transition1090 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0082 support0752 1 transition0338 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0752 support0735 1 finish0149 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0146 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0146 support1190 1 transition1091 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1190 support0957 1 transition1092 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0957 support0958 1 finish0262 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0146 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0146 support1190 1 transition1091 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1190 support0959 1 transition1093 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0959 support0527 1 finish0263 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0146 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1547 : NodeFacts 1547 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0147 support0227 2 transition1094 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0147 support0228 2 transition1095 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1547 : NodeTailFacts 1547 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0147 support0227 2 transition1096 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0227 support0735 1 transition1097 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0735 support1070 1 finish0398 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0147 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0147 support0227 2 transition1096 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0227 support1191 1 transition1098 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1191 support0735 2 finish0399 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0147 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0147 support1192 2 transition1099 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1192 support0616 1 transition1100 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0147 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0147 support1192 2 transition1099 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1192 support0618 1 transition1101 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0147 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1548 : NodeFacts 1548 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0444 support0082 1 transition2986 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0444 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0444 support0082 1 transition2987 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0082, supportNumbers0082, fromList]

theorem nodeTailFacts1548 : NodeTailFacts 1548 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0444 support0082 1 transition2988 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0082 support0750 1 transition0337 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0750 support0751 1 finish0148 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0444 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0444 support0082 1 transition2988 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0082 support0752 1 transition0338 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0752 support0735 1 finish0149 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0444 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0444 support0082 1 transition2989 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0082 support0082 1 transition2990 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0082 support0955 1 finish0260 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0444 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0444 support0082 1 transition2989 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0082 support0226 1 transition2991 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0226 support0148 1 finish0261 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0444 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1549 : NodeFacts 1549 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0445 support0227 1 transition2992 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0445 support0228 1 transition2993 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1549 : NodeTailFacts 1549 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0445 support0227 1 transition2994 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0227 support0735 1 transition1097 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0735 support1070 1 finish0398 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0445 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0445 support0227 1 transition2994 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0227 support1191 1 transition1098 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1191 support0735 2 finish0399 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0445 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0445 support1192 1 transition2995 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1192 support0616 1 transition1100 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0445 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0445 support1192 1 transition2995 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1192 support0618 1 transition1101 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0445 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1550 : NodeFacts 1550 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0402 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0402 support0044 1 transition2732 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0044, supportNumbers0044, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0402 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0402 support0150 1 transition2733 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0150, supportNumbers0150, fromList]

theorem nodeTailFacts1550 : NodeTailFacts 1550 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0402 support0044 1 transition2734 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0044 support0619 1 transition0159 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0619 support0620 1 finish0074 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0402 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0402 support0044 1 transition2734 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0044 support0621 1 transition0160 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0621 support0044 1 finish0075 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0402 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0402 support0964 1 transition2735 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0964 support0965 1 transition0672 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0965 support0966 1 finish0266 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0402 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0402 support0964 1 transition2735 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0964 support0967 1 transition0673 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0967 support0725 2 finish0267 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0402 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1551 : NodeFacts 1551 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0403 support0231 2 transition2736 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0403 support0232 2 transition2737 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1551 : NodeTailFacts 1551 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0403 support0231 2 transition2738 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0231 support1200 1 transition1117 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1200 support1201 1 finish0404 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0403 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0403 support0231 2 transition2738 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0231 support1202 1 transition1118 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1202 support0229 1 finish0405 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0403 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0403 support1203 2 transition2739 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1203 support1204 1 transition1120 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1204 support1205 1 finish0406 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0403 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0403 support1203 2 transition2739 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1203 support1206 1 transition1121 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1206 support0913 2 finish0407 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0403 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1552 : NodeFacts 1552 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0086 support0151 1 transition0674 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0086 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0086 support0151 1 transition0675 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0151, supportNumbers0151, fromList]

theorem nodeTailFacts1552 : NodeTailFacts 1552 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0086 support0151 1 transition0676 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0151 support0968 1 transition0677 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0968 support0969 1 finish0268 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0086 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0086 support0151 1 transition0676 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0151 support0970 1 transition0678 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0970 support0151 1 finish0269 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0086 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0086 support0151 1 transition0679 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0151 support0151 1 transition0680 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0151 support0971 1 finish0270 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0086 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0086 support0151 1 transition0679 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0151 support0446 1 transition0681 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0446 support0151 2 finish0271 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0086 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1553 : NodeFacts 1553 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0087 support0152 1 transition0682 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0087 support0153 1 transition0683 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1553 : NodeTailFacts 1553 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0087 support0152 1 transition0684 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0152 support0972 1 transition0685 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0972 support0973 1 finish0272 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0087 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0087 support0152 1 transition0684 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0152 support0974 1 transition0686 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0974 support0326 1 finish0273 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0087 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0087 support0975 1 transition0687 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0975 support0976 1 transition0688 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0087 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0087 support0975 1 transition0687 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0975 support0978 1 transition0689 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0087 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1554 : NodeFacts 1554 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0151 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0151 support0044 1 transition1122 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0044, supportNumbers0044, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0151 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0151 support0233 1 transition1123 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0233, supportNumbers0233, fromList]

theorem nodeTailFacts1554 : NodeTailFacts 1554 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0151 support0044 1 transition1124 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0044 support0619 1 transition0159 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0619 support0620 1 finish0074 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0151 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0151 support0044 1 transition1124 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0044 support0621 1 transition0160 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0621 support0044 1 finish0075 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0151 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0151 support1207 1 transition1125 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1207 support1208 1 transition1126 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1208 support1087 1 finish0408 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0151 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0151 support1207 1 transition1125 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1207 support1209 1 transition1127 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1209 support1210 2 finish0409 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0151 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1555 : NodeFacts 1555 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0446 support0469 1 transition2996 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0446 support0470 1 transition2997 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1555 : NodeTailFacts 1555 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0446 support0469 1 transition2998 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0469 support0151 1 transition2999 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0151 support0971 1 finish0270 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0446 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0446 support0469 1 transition2998 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0469 support0446 1 transition3000 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0446 support0151 2 finish0271 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0446 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0446 support1764 1 transition3001 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1764 support0762 2 transition3002 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0762 support0763 1 finish0158 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0446 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0446 support1764 1 transition3001 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1764 support0764 2 transition3003 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0764 support0765 2 finish0159 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0446 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1556 : NodeFacts 1556 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0236 support0326 1 transition1702 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0236 support0327 1 transition1703 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1556 : NodeTailFacts 1556 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0236 support0326 1 transition1704 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0326 support1438 1 transition1705 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1438 support1439 1 finish0534 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0236 support0326 1 transition1704 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0326 support1440 1 transition1706 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1440 support0326 1 finish0535 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0236 support1441 1 transition1707 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1441 support0976 1 transition1708 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0236 support1441 1 transition1707 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1441 support0978 1 transition1709 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0236 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1557 : NodeFacts 1557 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0237 support0236 2 transition1710 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0237 support0237 2 transition1711 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1557 : NodeTailFacts 1557 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0237 support0236 2 transition1712 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0236 support0326 1 transition1143 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0326 support1217 1 finish0412 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0237 support0236 2 transition1712 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0236 support0327 1 transition1144 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0327 support0326 2 finish0413 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0237 support1218 2 transition1713 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1218 support0976 2 transition1146 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0237 support1218 2 transition1713 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1218 support0978 2 transition1147 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0237 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1558 : NodeFacts 1558 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0322 support0020 1 transition2264 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0322 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0322 support0020 1 transition2265 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0020, supportNumbers0020, fromList]

theorem nodeTailFacts1558 : NodeTailFacts 1558 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0322 support0020 1 transition2266 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0020 support0528 1 transition0051 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0528 support0529 1 finish0024 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0322 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0322 support0020 1 transition2266 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0020 support0530 1 transition0052 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0530 support0020 1 finish0025 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0322 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0322 support0020 1 transition2267 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0020 support0020 1 transition2268 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0020 support1436 1 finish0532 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0322 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0322 support0020 1 transition2267 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0020 support0235 1 transition2269 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0235 support0020 2 finish0533 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0322 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1559 : NodeFacts 1559 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0323 support0404 1 transition2270 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0323 support0405 1 transition2271 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1559 : NodeTailFacts 1559 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0323 support0404 1 transition2272 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0404 support1597 1 transition2273 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1597 support1598 1 finish0612 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0323 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0323 support0404 1 transition2272 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0404 support1599 1 transition2274 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1599 support0326 1 finish0613 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0323 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0323 support1600 1 transition2275 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1600 support0976 1 transition2276 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0323 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0323 support1600 1 transition2275 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1600 support0978 1 transition2277 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0323 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1560 : NodeFacts 1560 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0234 support0152 1 transition1690 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0234 support0153 1 transition1691 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1560 : NodeTailFacts 1560 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0234 support0152 1 transition1692 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0152 support0972 1 transition0685 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0972 support0973 1 finish0272 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0234 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0234 support0152 1 transition1692 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0152 support0974 1 transition0686 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0974 support0326 1 finish0273 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0234 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0234 support0975 1 transition1693 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0975 support0976 1 transition0688 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0234 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0234 support0975 1 transition1693 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0975 support0978 1 transition0689 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0234 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1561 : NodeFacts 1561 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0407 support0447 1 transition2758 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0407 support0448 1 transition2759 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1561 : NodeTailFacts 1561 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0407 support0447 1 transition2760 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0447 support1716 1 transition2761 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1716 support1717 1 finish0668 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0407 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0407 support0447 1 transition2760 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0447 support1718 1 transition2762 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1718 support0326 1 finish0669 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0407 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0407 support1719 1 transition2763 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1719 support0976 1 transition2764 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0407 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0407 support1719 1 transition2763 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1719 support0978 1 transition2765 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0407 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1562 : NodeFacts 1562 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0404 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0404 support0151 1 transition2744 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0151, supportNumbers0151, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0404 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0404 support0446 1 transition2745 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0446, supportNumbers0446, fromList]

theorem nodeTailFacts1562 : NodeTailFacts 1562 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0404 support0151 1 transition2746 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0151 support0968 1 transition0677 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0968 support0969 1 finish0268 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0404 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0404 support0151 1 transition2746 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0151 support0970 1 transition0678 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0970 support0151 1 finish0269 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0404 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0404 support1711 1 transition2747 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1711 support1712 1 transition2748 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1712 support1713 1 finish0666 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0404 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0404 support1711 1 transition2747 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1711 support1714 1 transition2749 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1714 support1715 2 finish0667 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0404 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1563 : NodeFacts 1563 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0405 support0236 1 transition2750 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0405 support0237 1 transition2751 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1563 : NodeTailFacts 1563 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0405 support0236 1 transition2752 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0236 support0326 1 transition1143 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0326 support1217 1 finish0412 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0405 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0405 support0236 1 transition2752 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0236 support0327 1 transition1144 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0327 support0326 2 finish0413 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0405 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0405 support1218 1 transition2753 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1218 support0976 2 transition1146 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0405 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0405 support1218 1 transition2753 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1218 support0978 2 transition1147 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0405 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1564 : NodeFacts 1564 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0469 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0469 support0151 1 transition3116 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0151, supportNumbers0151, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0469 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0469 support0234 1 transition3117 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0234, supportNumbers0234, fromList]

theorem nodeTailFacts1564 : NodeTailFacts 1564 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0469 support0151 1 transition3118 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0151 support0968 1 transition0677 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0968 support0969 1 finish0268 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0469 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0469 support0151 1 transition3118 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0151 support0970 1 transition0678 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0970 support0151 1 finish0269 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0469 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0469 support1211 1 transition3119 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1211 support0762 1 transition1132 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0762 support0763 1 finish0158 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0469 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0469 support1211 1 transition3119 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1211 support0764 1 transition1133 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0764 support0765 2 finish0159 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0469 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1565 : NodeFacts 1565 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0470 support0152 2 transition3120 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0470 support0153 2 transition3121 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1565 : NodeTailFacts 1565 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0470 support0152 2 transition3122 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0152 support0972 1 transition0685 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0972 support0973 1 finish0272 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0470 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0470 support0152 2 transition3122 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0152 support0974 1 transition0686 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0974 support0326 1 finish0273 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0470 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0470 support0975 2 transition3123 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0975 support0976 1 transition0688 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0470 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0470 support0975 2 transition3123 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0975 support0978 1 transition0689 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0470 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1566 : NodeFacts 1566 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0326 support0229 1 transition2288 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0229, supportNumbers0229, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0326 support0407 1 transition2289 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0407, supportNumbers0407, fromList]

theorem nodeTailFacts1566 : NodeTailFacts 1566 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0326 support0229 1 transition2290 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0229 support1193 1 transition1105 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1193 support1194 1 finish0400 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0326 support0229 1 transition2290 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0229 support1195 1 transition1106 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1195 support0229 1 finish0401 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0326 support1602 1 transition2291 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1602 support1603 1 transition2292 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1603 support1526 1 finish0614 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0326 support1602 1 transition2291 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1602 support1604 1 transition2293 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1604 support1605 2 finish0615 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1567 : NodeFacts 1567 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0327 support0236 1 transition2294 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0327 support0237 1 transition2295 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1567 : NodeTailFacts 1567 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0327 support0236 1 transition2296 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0236 support0326 1 transition1143 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0326 support1217 1 finish0412 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0327 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0327 support0236 1 transition2296 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0236 support0327 1 transition1144 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0327 support0326 2 finish0413 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0327 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0327 support1218 1 transition2297 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1218 support0976 2 transition1146 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0327 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0327 support1218 1 transition2297 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1218 support0978 2 transition1147 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0327 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1568 : NodeFacts 1568 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0152 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0152 support0020 1 transition1134 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0020, supportNumbers0020, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0152 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0152 support0235 1 transition1135 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0235, supportNumbers0235, fromList]

theorem nodeTailFacts1568 : NodeTailFacts 1568 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0152 support0020 1 transition1136 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0020 support0528 1 transition0051 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0528 support0529 1 finish0024 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0152 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0152 support0020 1 transition1136 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0020 support0530 1 transition0052 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0530 support0020 1 finish0025 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0152 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0152 support1212 1 transition1137 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1212 support1213 1 transition1138 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1213 support1214 1 finish0410 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0152 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0152 support1212 1 transition1137 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1212 support1215 1 transition1139 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1215 support1216 2 finish0411 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0152 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1569 : NodeFacts 1569 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0153 support0236 1 transition1140 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0153 support0237 1 transition1141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1569 : NodeTailFacts 1569 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0153 support0236 1 transition1142 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0236 support0326 1 transition1143 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0326 support1217 1 finish0412 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0153 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0153 support0236 1 transition1142 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0236 support0327 1 transition1144 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0327 support0326 2 finish0413 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0153 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0153 support1218 1 transition1145 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1218 support0976 2 transition1146 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0153 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0153 support1218 1 transition1145 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1218 support0978 2 transition1147 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0153 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1570 : NodeFacts 1570 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0447 support0326 1 transition3004 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0447 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0447 support0326 1 transition3005 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0326, supportNumbers0326, fromList]

theorem nodeTailFacts1570 : NodeTailFacts 1570 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0447 support0326 1 transition3006 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0326 support1438 1 transition1705 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1438 support1439 1 finish0534 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0447 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0447 support0326 1 transition3006 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0326 support1440 1 transition1706 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1440 support0326 1 finish0535 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0447 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0447 support0326 1 transition3007 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0326 support0326 1 transition3008 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0326 support1217 1 finish0412 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0447 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0447 support0326 1 transition3007 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0326 support0327 1 transition3009 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0327 support0326 2 finish0413 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0447 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1571 : NodeFacts 1571 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0448 support0236 1 transition3010 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0448 support0237 1 transition3011 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1571 : NodeTailFacts 1571 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0448 support0236 1 transition3012 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0236 support0326 1 transition1143 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0326 support1217 1 finish0412 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0448 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0448 support0236 1 transition3012 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0236 support0327 1 transition1144 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0327 support0326 2 finish0413 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0448 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0448 support1218 1 transition3013 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1218 support0976 2 transition1146 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0448 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0448 support1218 1 transition3013 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1218 support0978 2 transition1147 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0448 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1572 : NodeFacts 1572 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0324 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0324 support0020 1 transition2278 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0020, supportNumbers0020, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0324 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0324 support0406 1 transition2279 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0406, supportNumbers0406, fromList]

theorem nodeTailFacts1572 : NodeTailFacts 1572 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0324 support0020 1 transition2280 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0020 support0528 1 transition0051 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0528 support0529 1 finish0024 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0324 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0324 support0020 1 transition2280 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0020 support0530 1 transition0052 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0530 support0020 1 finish0025 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0324 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0324 support1601 1 transition2281 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1601 support1432 1 transition2282 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1432 support1433 1 finish0530 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0324 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0324 support1601 1 transition2281 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1601 support1434 1 transition2283 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1434 support1435 2 finish0531 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0324 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1573 : NodeFacts 1573 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0325 support0404 2 transition2284 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0325 support0405 2 transition2285 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1573 : NodeTailFacts 1573 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0325 support0404 2 transition2286 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0404 support1597 1 transition2273 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1597 support1598 1 finish0612 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0325 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0325 support0404 2 transition2286 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0404 support1599 1 transition2274 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1599 support0326 1 finish0613 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0325 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0325 support1600 2 transition2287 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1600 support0976 1 transition2276 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0325 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0325 support1600 2 transition2287 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1600 support0978 1 transition2277 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0325 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1574 : NodeFacts 1574 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0326 support0326 1 transition3124 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0326 support0327 1 transition3125 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1574 : NodeTailFacts 1574 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0326 support0326 1 transition3126 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0326 support1438 1 transition1705 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1438 support1439 1 finish0534 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0326 support0326 1 transition3126 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0326 support1440 1 transition1706 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1440 support0326 1 finish0535 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0326 support1441 1 transition3127 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1441 support0976 1 transition1708 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0976 support0977 1 finish0274 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0326 support1441 1 transition3127 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1441 support0978 1 transition1709 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0978 support0979 2 finish0275 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0326 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1575 : NodeFacts 1575 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0222 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0222 support0044 1 transition1608 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0044, supportNumbers0044, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0222 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0222 support0311 1 transition1609 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0311, supportNumbers0311, fromList]

theorem nodeTailFacts1575 : NodeTailFacts 1575 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0222 support0044 1 transition1610 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0044 support0619 1 transition0159 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0619 support0620 1 finish0074 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0222 support0044 1 transition1610 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0044 support0621 1 transition0160 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0621 support0044 1 finish0075 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0222 support1402 1 transition1611 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1402 support1403 1 transition1612 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1403 support1404 1 finish0510 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0222 support1402 1 transition1611 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1402 support1405 1 transition1613 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1405 support0518 2 finish0511 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0222 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1576 : NodeFacts 1576 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0223 support0312 1 transition1614 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0223 support0313 1 transition1615 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1576 : NodeTailFacts 1576 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0223 support0312 1 transition1616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0312 support0222 1 transition1617 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0222 support1299 1 finish0512 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0223 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0223 support0312 1 transition1616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0312 support0223 1 transition1618 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0223 support0222 2 finish0513 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0223 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0223 support1406 1 transition1619 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1406 support1223 2 transition1620 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1223 support1224 1 finish0416 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0223 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0223 support1406 1 transition1619 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1406 support1225 2 transition1621 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1225 support0938 2 finish0417 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0223 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1577 : NodeFacts 1577 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0328 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0328 support0088 1 transition2302 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0088, supportNumbers0088, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0328 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0328 support0408 1 transition2303 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0408, supportNumbers0408, fromList]

theorem nodeTailFacts1577 : NodeTailFacts 1577 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0328 support0088 1 transition2304 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0088 support0766 1 transition0367 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0766 support0767 1 finish0160 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0328 support0088 1 transition2304 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0088 support0768 1 transition0368 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0768 support0088 1 finish0161 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0328 support1606 1 transition2305 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1606 support1607 1 transition2306 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1607 support1608 1 finish0616 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0328 support1606 1 transition2305 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1606 support1609 1 transition2307 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1609 support0612 2 finish0617 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1578 : NodeFacts 1578 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0329 support0084 1 transition2308 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0329 support0085 1 transition2309 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1578 : NodeTailFacts 1578 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0329 support0084 1 transition2310 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 support0148 1 transition0345 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0148 support0679 1 finish0152 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0329 support0084 1 transition2310 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 support0149 1 transition0346 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0149 support0148 2 finish0153 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0329 support0757 1 transition2311 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0757 support0616 2 transition0348 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0329 support0757 1 transition2311 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0757 support0618 2 transition0349 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1579 : NodeFacts 1579 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0046 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0046 support0088 1 transition0364 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0088, supportNumbers0088, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0046 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0046 support0089 1 transition0365 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0089, supportNumbers0089, fromList]

theorem nodeTailFacts1579 : NodeTailFacts 1579 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0046 support0088 1 transition0366 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0088 support0766 1 transition0367 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0766 support0767 1 finish0160 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0046 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0046 support0088 1 transition0366 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0088 support0768 1 transition0368 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0768 support0088 1 finish0161 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0046 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0046 support0769 1 transition0369 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0769 support0770 1 transition0370 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0770 support0696 1 finish0162 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0046 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0046 support0769 1 transition0369 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0769 support0771 1 transition0371 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0771 support0772 2 finish0163 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0046 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1580 : NodeFacts 1580 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0047 support0090 1 transition0372 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0047 support0091 1 transition0373 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1580 : NodeTailFacts 1580 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0047 support0090 1 transition0374 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0090 support0773 1 transition0375 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0773 support0774 1 finish0164 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0047 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0047 support0090 1 transition0374 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0090 support0775 1 transition0376 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0775 support0096 1 finish0165 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0047 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0047 support0776 1 transition0377 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0776 support0540 1 transition0378 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0047 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0047 support0776 1 transition0377 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0776 support0542 1 transition0379 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0047 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1581 : NodeFacts 1581 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0048 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0048 support0092 1 transition0380 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0092, supportNumbers0092, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0048 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0048 support0093 1 transition0381 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0093, supportNumbers0093, fromList]

theorem nodeTailFacts1581 : NodeTailFacts 1581 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0048 support0092 1 transition0382 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0092 support0777 1 transition0383 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0777 support0778 1 finish0166 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0048 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0048 support0092 1 transition0382 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0092 support0779 1 transition0384 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0779 support0092 1 finish0167 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0048 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0048 support0780 1 transition0385 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0780 support0781 1 transition0386 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0781 support0782 1 finish0168 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0048 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0048 support0780 1 transition0385 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0780 support0783 1 transition0387 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0783 support0784 2 finish0169 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0048 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1582 : NodeFacts 1582 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0049 support0094 1 transition0388 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0049 support0095 1 transition0389 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1582 : NodeTailFacts 1582 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0049 support0094 1 transition0390 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0094 support0048 1 transition0391 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0048 support0785 1 finish0170 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0049 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0049 support0094 1 transition0390 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0094 support0049 1 transition0392 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0049 support0048 2 finish0171 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0049 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0049 support0786 1 transition0393 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0786 support0787 2 transition0394 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0787 support0788 1 finish0172 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0049 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0049 support0786 1 transition0393 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0786 support0789 2 transition0395 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0789 support0790 2 finish0173 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0049 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1583 : NodeFacts 1583 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0050 support0096 1 transition0396 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0050 support0097 1 transition0397 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1583 : NodeTailFacts 1583 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0050 support0096 1 transition0398 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0096 support0791 1 transition0399 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0791 support0792 1 finish0174 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0050 support0096 1 transition0398 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0096 support0793 1 transition0400 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0793 support0096 1 finish0175 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0050 support0794 1 transition0401 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0794 support0540 1 transition0402 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0050 support0794 1 transition0401 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0794 support0542 1 transition0403 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0050 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1584 : NodeFacts 1584 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0051 support0050 2 transition0404 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0051 support0051 2 transition0405 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1584 : NodeTailFacts 1584 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0051 support0050 2 transition0406 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0051 support0050 2 transition0406 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0051 support0643 2 transition0407 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0051 support0643 2 transition0407 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0051 (1 / (2 : ℚ) ^ 9) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1585 : NodeFacts 1585 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0241 support0241 1 transition1736 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0241 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0241 support0241 1 transition1737 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0241, supportNumbers0241, fromList]

theorem nodeTailFacts1585 : NodeTailFacts 1585 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0241 support0241 1 transition1738 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0241 support1231 1 transition1169 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1231 support1232 1 finish0420 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0241 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0241 support0241 1 transition1738 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0241 support1233 1 transition1170 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1233 support0241 1 finish0421 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0241 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0241 support0241 1 transition1739 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0241 support0241 1 transition1740 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0241 support1450 1 finish0540 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0241 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0241 support0241 1 transition1739 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0241 support0471 1 transition1741 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0471 support0241 2 finish0541 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0241 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1586 : NodeFacts 1586 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0472 support0157 1 transition3136 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0472 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0472 support0157 1 transition3137 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0157, supportNumbers0157, fromList]

theorem nodeTailFacts1586 : NodeTailFacts 1586 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0472 support0157 1 transition3138 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0157 support0988 1 transition0707 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0988 support0989 1 finish0280 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0472 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0472 support0157 1 transition3138 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0157 support0990 1 transition0708 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0990 support0157 1 finish0281 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0472 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0472 support0157 1 transition3139 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0157 support0157 1 transition3140 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0157 support1239 1 finish0424 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0472 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0472 support0157 1 transition3139 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0157 support0158 1 transition3141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0158 support0157 2 finish0425 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0472 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1587 : NodeFacts 1587 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0473 support0335 1 transition3142 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0473 support0336 1 transition3143 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1587 : NodeTailFacts 1587 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0473 support0335 1 transition3144 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0335 support1456 1 transition1759 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1456 support1457 1 finish0544 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0473 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0473 support0335 1 transition3144 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0335 support1458 1 transition1760 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1458 support0096 1 finish0545 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0473 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0473 support1459 1 transition3145 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1459 support0540 1 transition1762 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0473 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0473 support1459 1 transition3145 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1459 support0542 1 transition1763 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0473 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1588 : NodeFacts 1588 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0411 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0411 support0241 1 transition2790 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0241, supportNumbers0241, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0411 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0411 support0453 1 transition2791 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0453, supportNumbers0453, fromList]

theorem nodeTailFacts1588 : NodeTailFacts 1588 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0411 support0241 1 transition2792 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0241 support1231 1 transition1169 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1231 support1232 1 finish0420 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0411 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0411 support0241 1 transition2792 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0241 support1233 1 transition1170 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1233 support0241 1 finish0421 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0411 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0411 support1729 1 transition2793 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1729 support1730 1 transition2794 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1730 support1731 1 finish0674 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0411 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0411 support1729 1 transition2793 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1729 support1732 1 transition2795 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1732 support1733 2 finish0675 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0411 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1589 : NodeFacts 1589 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0454 support0090 1 transition3040 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0454 support0091 1 transition3041 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1589 : NodeTailFacts 1589 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0454 support0090 1 transition3042 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0090 support0773 1 transition0375 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0773 support0774 1 finish0164 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0454 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0454 support0090 1 transition3042 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0090 support0775 1 transition0376 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0775 support0096 1 finish0165 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0454 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0454 support0776 1 transition3043 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0776 support0540 1 transition0378 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0454 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0454 support0776 1 transition3043 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0776 support0542 1 transition0379 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0454 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1590 : NodeFacts 1590 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0090 support0157 1 transition0704 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0090 support0158 1 transition0705 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1590 : NodeTailFacts 1590 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0090 support0157 1 transition0706 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0157 support0988 1 transition0707 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0988 support0989 1 finish0280 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0090 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0090 support0157 1 transition0706 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0157 support0990 1 transition0708 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0990 support0157 1 finish0281 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0090 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0090 support0991 1 transition0709 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0991 support0992 1 transition0710 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0992 support0993 1 finish0282 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0090 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0090 support0991 1 transition0709 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0991 support0994 1 transition0711 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0994 support0995 2 finish0283 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0090 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1591 : NodeFacts 1591 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0091 support0050 1 transition0712 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0091 support0051 1 transition0713 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1591 : NodeTailFacts 1591 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0091 support0050 1 transition0714 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0091 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0091 support0050 1 transition0714 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0091 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0091 support0643 1 transition0715 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0091 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0091 support0643 1 transition0715 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0091 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1592 : NodeFacts 1592 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0164 support0164 1 transition1214 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0164 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0164 support0164 1 transition1215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0164, supportNumbers0164, fromList]

theorem nodeTailFacts1592 : NodeTailFacts 1592 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0164 support0164 1 transition1216 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0164 support1010 1 transition0747 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1010 support1011 1 finish0292 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0164 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0164 support0164 1 transition1216 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0164 support1012 1 transition0748 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1012 support0164 1 finish0293 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0164 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0164 support0164 1 transition1217 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0164 support0164 1 transition1218 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0164 support1259 1 finish0436 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0164 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0164 support0164 1 transition1217 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0164 support0343 1 transition1219 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0343 support0164 2 finish0437 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0164 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1593 : NodeFacts 1593 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0165 support0248 1 transition1220 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0165 support0249 1 transition1221 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1593 : NodeTailFacts 1593 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0165 support0248 1 transition1222 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0248 support1260 1 transition1223 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1260 support1261 1 finish0438 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0165 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0165 support0248 1 transition1222 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0248 support1262 1 transition1224 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1262 support0096 1 finish0439 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0165 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0165 support1263 1 transition1225 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1263 support0540 1 transition1226 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0165 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0165 support1263 1 transition1225 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1263 support0542 1 transition1227 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 10) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 10) (1 / (2 : ℚ) ^ 9) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0165 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1594 : NodeFacts 1594 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0096 support0164 1 transition0744 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0096 support0165 1 transition0745 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1594 : NodeTailFacts 1594 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0096 support0164 1 transition0746 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0164 support1010 1 transition0747 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1010 support1011 1 finish0292 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0096 support0164 1 transition0746 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0164 support1012 1 transition0748 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1012 support0164 1 finish0293 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0096 support1013 1 transition0749 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1013 support1014 1 transition0750 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1014 support1015 1 finish0294 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0096 support1013 1 transition0749 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1013 support1016 1 transition0751 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1016 support1017 2 finish0295 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0096 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1595 : NodeFacts 1595 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0097 support0050 1 transition0752 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0097 support0051 1 transition0753 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1595 : NodeTailFacts 1595 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0097 support0050 1 transition0754 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0050 support0096 1 transition0183 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0096 support0642 1 finish0086 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0097 support0050 1 transition0754 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0050 support0097 1 transition0184 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0097 support0096 2 finish0087 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0097 support0643 1 transition0755 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0643 support0540 2 transition0186 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0540 support0541 1 finish0030 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0097 support0643 1 transition0755 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 support0542 2 transition0187 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0542 support0543 2 finish0031 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0097 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1596 : NodeFacts 1596 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0092 support0092 1 transition0716 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0092 (1 / (2 : ℚ) ^ 6) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0092 support0092 1 transition0717 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0092, supportNumbers0092, fromList]

theorem nodeTailFacts1596 : NodeTailFacts 1596 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0092 support0092 1 transition0718 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0092 support0777 1 transition0383 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0777 support0778 1 finish0166 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0092 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0092 support0092 1 transition0718 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0092 support0779 1 transition0384 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0779 support0092 1 finish0167 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0092 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0092 support0092 1 transition0719 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0092 support0092 1 transition0720 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0092 support0996 1 finish0284 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0092 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0092 support0092 1 transition0719 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0092 support0413 1 transition0721 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0413 support0092 2 finish0285 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0092 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1597 : NodeFacts 1597 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0245 support0337 1 transition1764 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0245 support0338 1 transition1765 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1597 : NodeTailFacts 1597 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0245 support0337 1 transition1766 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0337 support1460 1 transition1767 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1460 support1461 1 finish0546 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0245 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0245 support0337 1 transition1766 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0337 support1462 1 transition1768 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1462 support0164 1 finish0547 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0245 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0245 support1463 1 transition1769 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1463 support1464 1 transition1770 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1464 support1465 1 finish0548 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0245 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0245 support1463 1 transition1769 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1463 support1466 1 transition1771 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1466 support1467 2 finish0549 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0245 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1598 : NodeFacts 1598 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0337 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0337 support0092 1 transition2354 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0092, supportNumbers0092, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0337 (1 / (2 : ℚ) ^ 7) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0337 support0413 1 transition2355 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0413, supportNumbers0413, fromList]

theorem nodeTailFacts1598 : NodeTailFacts 1598 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0337 support0092 1 transition2356 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0092 support0777 1 transition0383 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0777 support0778 1 finish0166 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0337 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0337 support0092 1 transition2356 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0092 support0779 1 transition0384 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0779 support0092 1 finish0167 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0337 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0337 support1628 1 transition2357 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1628 support1629 1 transition2358 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1629 support1630 1 finish0628 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0337 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0337 support1628 1 transition2357 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1628 support1631 1 transition2359 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1631 support1632 2 finish0629 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0337 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1599 : NodeFacts 1599 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0338 support0414 1 transition2360 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0338 support0415 1 transition2361 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1599 : NodeTailFacts 1599 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0338 support0414 1 transition2362 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0414 support0164 1 transition2363 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0164 support1259 1 finish0436 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0338 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0338 support0414 1 transition2362 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0414 support0343 1 transition2364 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0343 support0164 2 finish0437 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0338 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0338 support1633 1 transition2365 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1633 support1464 2 transition2366 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1464 support1465 1 finish0548 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0338 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0338 support1633 1 transition2365 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1633 support1466 2 transition2367 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 9) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1466 support1467 2 finish0549 (1 / (2 : ℚ) ^ 9) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0338 (1 / (2 : ℚ) ^ 8) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
