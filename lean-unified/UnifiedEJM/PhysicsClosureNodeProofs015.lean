import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureEdges

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeFacts0960 : NodeFacts 960 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0424 support0459 1 transition2864 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0424 support0460 1 transition2865 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0960 : NodeTailFacts 960 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0424 support0459 1 transition2866 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0459 support0117 1 transition2867 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0117 support0030 1 finish0210 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0424 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0424 support0459 1 transition2866 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0459 support0854 1 transition2868 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0854 support0855 1 finish0211 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0424 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0424 support1742 1 transition2869 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1742 support0687 2 transition2870 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0687 support0688 1 finish0114 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0424 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0424 support1742 1 transition2869 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1742 support0689 2 transition2871 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0689 support0690 1 finish0115 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0424 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0961 : NodeFacts 961 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0194 support0279 1 transition1412 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0194 support0280 1 transition1413 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0961 : NodeTailFacts 961 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0194 support0279 1 transition1414 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0279 support1334 1 transition1415 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1334 support0898 1 finish0478 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0194 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0194 support0279 1 transition1414 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0279 support1335 1 transition1416 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1335 support1336 1 finish0479 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0194 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0194 support1337 1 transition1417 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1337 support0861 1 transition1418 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0194 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0194 support1337 1 transition1417 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1337 support0863 1 transition1419 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0194 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0962 : NodeFacts 962 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0195 support0194 2 transition1420 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0195 support0195 2 transition1421 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0962 : NodeTailFacts 962 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0195 support0194 2 transition1422 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0194 support0279 1 transition0907 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0279 support0187 1 finish0340 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0195 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0195 support0194 2 transition1422 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0194 support1093 1 transition0908 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1093 support1094 1 finish0341 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0195 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0195 support1095 2 transition1423 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1095 support0861 2 transition0910 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0195 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0195 support1095 2 transition1423 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1095 support0863 2 transition0911 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0195 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0963 : NodeFacts 963 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0367 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0367 support0117 1 transition2522 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0117, supportNumbers0117, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0367 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0367 support0424 1 transition2523 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0424, supportNumbers0424, fromList]

theorem nodeTailFacts0963 : NodeTailFacts 963 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0367 support0117 1 transition2524 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0117 support0851 1 transition0503 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0851 support0493 1 finish0208 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0367 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0367 support0117 1 transition2524 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0117 support0852 1 transition0504 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0852 support0853 1 finish0209 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0367 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0367 support1665 1 transition2525 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1665 support1666 1 transition2526 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1666 support0571 1 finish0644 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0367 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0367 support1665 1 transition2525 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1665 support1667 1 transition2527 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1667 support1668 1 finish0645 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0367 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0964 : NodeFacts 964 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0368 support0194 1 transition2528 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0368 support0195 1 transition2529 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0964 : NodeTailFacts 964 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0368 support0194 1 transition2530 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0194 support0279 1 transition0907 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0279 support0187 1 finish0340 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0368 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0368 support0194 1 transition2530 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0194 support1093 1 transition0908 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1093 support1094 1 finish0341 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0368 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0368 support1095 1 transition2531 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1095 support0861 2 transition0910 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0368 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0368 support1095 1 transition2531 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1095 support0863 2 transition0911 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0368 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0965 : NodeFacts 965 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0277 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0277 support0012 1 transition1984 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0012, supportNumbers0012, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0277 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0277 support0369 1 transition1985 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0369, supportNumbers0369, fromList]

theorem nodeTailFacts0965 : NodeTailFacts 965 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0277 support0012 1 transition1986 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0012 support0492 1 transition0019 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0492 support0493 1 finish0008 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0277 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0277 support0012 1 transition1986 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0012 support0494 1 transition0020 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0494 support0495 1 finish0009 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0277 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0277 support1522 1 transition1987 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1522 support1328 1 transition1988 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1328 support0571 1 finish0474 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0277 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0277 support1522 1 transition1987 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1522 support1329 1 transition1989 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1329 support1330 1 finish0475 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0277 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0966 : NodeFacts 966 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0278 support0367 2 transition1990 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0278 support0368 2 transition1991 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0966 : NodeTailFacts 966 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0278 support0367 2 transition1992 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0367 support1518 1 transition1979 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1518 support0857 1 finish0572 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0278 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0278 support0367 2 transition1992 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0367 support1519 1 transition1980 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1519 support1520 1 finish0573 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0278 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0278 support1521 2 transition1993 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1521 support0861 1 transition1982 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0278 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0278 support1521 2 transition1993 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1521 support0863 1 transition1983 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0278 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0967 : NodeFacts 967 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0279 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0279 support0187 1 transition1994 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0187, supportNumbers0187, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0279 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0279 support0370 1 transition1995 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0370, supportNumbers0370, fromList]

theorem nodeTailFacts0967 : NodeTailFacts 967 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0279 support0187 1 transition1996 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0187 support0898 1 transition0869 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0898 support0898 1 finish0328 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0279 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0279 support0187 1 transition1996 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0187 support1072 1 transition0870 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1072 support1073 1 finish0329 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0279 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0279 support1523 1 transition1997 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1523 support1524 1 transition1998 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1524 support0862 1 finish0574 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0279 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0279 support1523 1 transition1997 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1523 support1525 1 transition1999 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1525 support1526 1 finish0575 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0279 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0968 : NodeFacts 968 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0280 support0194 1 transition2000 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0280 support0195 1 transition2001 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0968 : NodeTailFacts 968 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0280 support0194 1 transition2002 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0194 support0279 1 transition0907 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0279 support0187 1 finish0340 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0280 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0280 support0194 1 transition2002 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0194 support1093 1 transition0908 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1093 support1094 1 finish0341 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0280 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0280 support1095 1 transition2003 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1095 support0861 2 transition0910 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0280 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0280 support1095 1 transition2003 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1095 support0863 2 transition0911 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0280 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0969 : NodeFacts 969 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0118 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0118 support0012 1 transition0898 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0012, supportNumbers0012, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0118 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0118 support0193 1 transition0899 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0193, supportNumbers0193, fromList]

theorem nodeTailFacts0969 : NodeTailFacts 969 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0118 support0012 1 transition0900 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0012 support0492 1 transition0019 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0492 support0493 1 finish0008 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0118 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0118 support0012 1 transition0900 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0012 support0494 1 transition0020 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0494 support0495 1 finish0009 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0118 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0118 support1089 1 transition0901 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1089 support1090 1 transition0902 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1090 support0688 1 finish0338 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0118 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0118 support1089 1 transition0901 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1089 support1091 1 transition0903 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1091 support1092 1 finish0339 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0118 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0970 : NodeFacts 970 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0119 support0194 1 transition0904 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0119 support0195 1 transition0905 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0970 : NodeTailFacts 970 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0119 support0194 1 transition0906 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0194 support0279 1 transition0907 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0279 support0187 1 finish0340 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0119 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0119 support0194 1 transition0906 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0194 support1093 1 transition0908 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1093 support1094 1 finish0341 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0119 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0119 support1095 1 transition0909 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1095 support0861 2 transition0910 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0119 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0119 support1095 1 transition0909 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1095 support0863 2 transition0911 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0119 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0971 : NodeFacts 971 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0425 support0279 1 transition2872 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0425 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0425 support0279 1 transition2873 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0279, supportNumbers0279, fromList]

theorem nodeTailFacts0971 : NodeTailFacts 971 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0425 support0279 1 transition2874 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0279 support1334 1 transition1415 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1334 support0898 1 finish0478 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0425 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0425 support0279 1 transition2874 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0279 support1335 1 transition1416 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1335 support1336 1 finish0479 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0425 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0425 support0279 1 transition2875 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0279 support0279 1 transition2876 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0279 support0187 1 finish0340 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0425 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0425 support0279 1 transition2875 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0279 support1093 1 transition2877 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1093 support1094 1 finish0341 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0425 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0972 : NodeFacts 972 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0426 support0194 1 transition2878 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0426 support0195 1 transition2879 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0972 : NodeTailFacts 972 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0426 support0194 1 transition2880 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0194 support0279 1 transition0907 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0279 support0187 1 finish0340 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0426 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0426 support0194 1 transition2880 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0194 support1093 1 transition0908 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1093 support1094 1 finish0341 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0426 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0426 support1095 1 transition2881 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1095 support0861 2 transition0910 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0426 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0426 support1095 1 transition2881 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1095 support0863 2 transition0911 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0426 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0973 : NodeFacts 973 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0370 support0425 1 transition2536 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0370 support0426 1 transition2537 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0973 : NodeTailFacts 973 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0370 support0425 1 transition2538 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0425 support1669 1 transition2539 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1669 support0898 1 finish0646 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0370 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0370 support0425 1 transition2538 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0425 support1670 1 transition2540 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1670 support1671 1 finish0647 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0370 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0370 support1672 1 transition2541 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1672 support0861 1 transition2542 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0861 support0862 1 finish0214 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0370 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0370 support1672 1 transition2541 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1672 support0863 1 transition2543 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0863 support0864 1 finish0215 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0370 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0974 : NodeFacts 974 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0355 support0065 1 transition2458 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0355 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0355 support0065 1 transition2459 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0065, supportNumbers0065, fromList]

theorem nodeTailFacts0974 : NodeTailFacts 974 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0355 support0065 1 transition2460 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0065 support0584 1 transition0257 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0584 support0584 1 finish0116 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0355 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0355 support0065 1 transition2460 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0065 support0691 1 transition0258 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0691 support0692 1 finish0117 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0355 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0355 support0065 1 transition2461 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0065 support0065 1 transition2462 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0065 support0065 1 finish0638 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0355 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0355 support0065 1 transition2461 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0065 support1654 1 transition2463 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1654 support1655 1 finish0639 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0355 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0975 : NodeFacts 975 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0356 support0108 1 transition2464 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0356 support0109 1 transition2465 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0975 : NodeTailFacts 975 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0356 support0108 1 transition2466 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0108 support0698 1 transition0461 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0698 support0698 1 finish0194 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0356 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0356 support0108 1 transition2466 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0108 support0828 1 transition0462 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0828 support0829 1 finish0195 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0356 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0356 support0830 1 transition2467 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0830 support0564 1 transition0464 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0356 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0356 support0830 1 transition2467 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0830 support0565 1 transition0465 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0356 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0976 : NodeFacts 976 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0427 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0427 support0065 1 transition2882 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0065, supportNumbers0065, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0427 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0427 support1743 1 transition2883 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support1743, supportNumbers1743, fromList]

theorem nodeTailFacts0976 : NodeTailFacts 976 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0427 support0065 1 transition2884 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0065 support0584 1 transition0257 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0584 support0584 1 finish0116 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0427 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0427 support0065 1 transition2884 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0065 support0691 1 transition0258 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0691 support0692 1 finish0117 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0427 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0427 support1744 1 transition2885 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1744 support0668 1 transition2886 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0668 support0065 1 finish0102 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0427 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0427 support1744 1 transition2885 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1744 support0669 1 transition2887 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0669 support0670 1 finish0103 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0427 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0977 : NodeFacts 977 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0428 support0108 2 transition2888 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0428 support0109 2 transition2889 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0977 : NodeTailFacts 977 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0428 support0108 2 transition2890 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0108 support0698 1 transition0461 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0698 support0698 1 finish0194 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0428 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0428 support0108 2 transition2890 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0108 support0828 1 transition0462 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0828 support0829 1 finish0195 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0428 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0428 support0830 2 transition2891 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0830 support0564 1 transition0464 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0564 support0114 1 finish0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0428 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0428 support0830 2 transition2891 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0830 support0565 1 transition0465 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0565 support0566 1 finish0045 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0428 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0978 : NodeFacts 978 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0002 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0002 support0012 1 transition0016 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0012, supportNumbers0012, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0002 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0002 support0013 1 transition0017 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0013, supportNumbers0013, fromList]

theorem nodeTailFacts0978 : NodeTailFacts 978 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0002 support0012 1 transition0018 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0012 support0492 1 transition0019 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0492 support0493 1 finish0008 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0002 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0002 support0012 1 transition0018 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0012 support0494 1 transition0020 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0494 support0495 1 finish0009 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0002 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0002 support0496 1 transition0021 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0496 support0497 1 transition0022 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0497 support0498 1 finish0010 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0002 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0002 support0496 1 transition0021 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0496 support0499 1 transition0023 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0499 support0500 1 finish0011 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0002 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0979 : NodeFacts 979 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0003 support0014 1 transition0024 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0003 support0015 1 transition0025 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0979 : NodeTailFacts 979 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0003 support0014 1 transition0026 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0014 support0501 1 transition0027 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0501 support0502 1 finish0012 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0003 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0003 support0014 1 transition0026 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0014 support0503 1 transition0028 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0503 support0504 1 finish0013 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0003 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0003 support0505 1 transition0029 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0505 support0506 1 transition0030 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0003 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0003 support0505 1 transition0029 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0505 support0508 1 transition0031 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0003 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0980 : NodeFacts 980 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0374 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0374 support0199 1 transition2568 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0199, supportNumbers0199, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0374 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0374 support0431 1 transition2569 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0431, supportNumbers0431, fromList]

theorem nodeTailFacts0980 : NodeTailFacts 980 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0374 support0199 1 transition2570 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0199 support1106 1 transition0933 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1106 support0493 1 finish0348 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0374 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0374 support0199 1 transition2570 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0199 support1107 1 transition0934 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1107 support1108 1 finish0349 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0374 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0374 support1682 1 transition2571 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1682 support1683 1 transition2572 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1683 support0571 1 finish0652 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0374 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0374 support1682 1 transition2571 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1682 support1684 1 transition2573 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1684 support1685 1 finish0653 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0374 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0981 : NodeFacts 981 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0375 support0433 1 transition2580 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0375 support0434 1 transition2581 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0981 : NodeTailFacts 981 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0375 support0433 1 transition2582 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0433 support0374 1 transition2583 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0374 support0065 1 finish0584 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0375 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0375 support0433 1 transition2582 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0433 support1543 1 transition2584 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1543 support1544 1 finish0585 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0375 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0375 support1687 1 transition2585 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1687 support0579 2 transition2586 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0579 support0580 1 finish0052 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0375 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0375 support1687 1 transition2585 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1687 support0581 2 transition2587 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0581 support0582 1 finish0053 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0375 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0982 : NodeFacts 982 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0036 support0073 1 transition0286 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0036 support0074 1 transition0287 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0982 : NodeTailFacts 982 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0036 support0073 1 transition0288 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0073 support0716 1 transition0289 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0716 support0717 1 finish0130 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0036 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0036 support0073 1 transition0288 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0073 support0718 1 transition0290 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0718 support0719 1 finish0131 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0036 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0036 support0720 1 transition0291 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0720 support0506 1 transition0292 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0036 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0036 support0720 1 transition0291 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0720 support0508 1 transition0293 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0036 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0983 : NodeFacts 983 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0037 support0036 2 transition0294 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0037 support0037 2 transition0295 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0983 : NodeTailFacts 983 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0037 support0036 2 transition0296 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0036 support0073 1 transition0121 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0073 support0114 1 finish0058 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0037 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0037 support0036 2 transition0296 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0036 support0591 1 transition0122 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0591 support0592 1 finish0059 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0037 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0037 support0593 2 transition0297 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0593 support0506 2 transition0124 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0037 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0037 support0593 2 transition0297 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0593 support0508 2 transition0125 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0037 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0984 : NodeFacts 984 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0069 support0069 1 transition0542 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0069 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0069 support0069 1 transition0543 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0069, supportNumbers0069, fromList]

theorem nodeTailFacts0984 : NodeTailFacts 984 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0069 support0069 1 transition0544 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0069 support0702 1 transition0273 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0702 support0493 1 finish0122 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0069 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0069 support0069 1 transition0544 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0069 support0703 1 transition0274 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0703 support0704 1 finish0123 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0069 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0069 support0069 1 transition0545 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0069 support0069 1 transition0546 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0069 support0030 1 finish0224 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0069 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0069 support0069 1 transition0545 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0069 support0882 1 transition0547 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0882 support0883 1 finish0225 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0069 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0985 : NodeFacts 985 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0379 support0034 1 transition2604 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0379 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0379 support0034 1 transition2605 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0034, supportNumbers0034, fromList]

theorem nodeTailFacts0985 : NodeTailFacts 985 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0379 support0034 1 transition2606 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0034 support0583 1 transition0113 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0583 support0584 1 finish0054 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0379 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0379 support0034 1 transition2606 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0034 support0585 1 transition0114 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0585 support0586 1 finish0055 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0379 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0379 support0034 1 transition2607 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0034 support0034 1 transition2608 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0034 support0065 1 finish0126 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0379 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0379 support0034 1 transition2607 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0034 support0709 1 transition2609 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0709 support0710 1 finish0127 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0379 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0986 : NodeFacts 986 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0380 support0128 1 transition2610 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0380 support0129 1 transition2611 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0986 : NodeTailFacts 986 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0380 support0128 1 transition2612 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0128 support0893 1 transition0565 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0893 support0698 1 finish0230 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0380 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0380 support0128 1 transition2612 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0128 support0894 1 transition0566 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0894 support0895 1 finish0231 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0380 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0380 support0896 1 transition2613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0896 support0506 1 transition0568 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0380 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0380 support0896 1 transition2613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0896 support0508 1 transition0569 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0380 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0987 : NodeFacts 987 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0204 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0204 support0069 1 transition1482 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0069, supportNumbers0069, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0204 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0204 support0292 1 transition1483 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0292, supportNumbers0292, fromList]

theorem nodeTailFacts0987 : NodeTailFacts 987 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0204 support0069 1 transition1484 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0069 support0702 1 transition0273 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0702 support0493 1 finish0122 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0204 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0204 support0069 1 transition1484 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0069 support0703 1 transition0274 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0703 support0704 1 finish0123 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0204 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0204 support1364 1 transition1485 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1364 support1365 1 transition1486 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1365 support0571 1 finish0494 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0204 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0204 support1364 1 transition1485 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1364 support1366 1 transition1487 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1366 support1367 1 finish0495 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0204 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0988 : NodeFacts 988 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0293 support0014 1 transition2082 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0293 support0015 1 transition2083 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0988 : NodeTailFacts 988 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0293 support0014 1 transition2084 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0014 support0501 1 transition0027 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0501 support0502 1 finish0012 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0293 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0293 support0014 1 transition2084 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0014 support0503 1 transition0028 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0503 support0504 1 finish0013 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0293 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0293 support0505 1 transition2085 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0505 support0506 1 transition0030 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0293 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0293 support0505 1 transition2085 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0505 support0508 1 transition0031 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0293 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0989 : NodeFacts 989 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0014 support0034 1 transition0110 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0014 support0035 1 transition0111 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0989 : NodeTailFacts 989 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0014 support0034 1 transition0112 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0034 support0583 1 transition0113 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0583 support0584 1 finish0054 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0014 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0014 support0034 1 transition0112 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0034 support0585 1 transition0114 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0585 support0586 1 finish0055 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0014 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0014 support0587 1 transition0115 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0587 support0588 1 transition0116 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0588 support0580 1 finish0056 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0014 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0014 support0587 1 transition0115 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0587 support0589 1 transition0117 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0589 support0590 1 finish0057 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0014 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0990 : NodeFacts 990 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0015 support0036 1 transition0118 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0015 support0037 1 transition0119 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0990 : NodeTailFacts 990 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0015 support0036 1 transition0120 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0036 support0073 1 transition0121 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0073 support0114 1 finish0058 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0015 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0015 support0036 1 transition0120 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0036 support0591 1 transition0122 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0591 support0592 1 finish0059 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0015 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0015 support0593 1 transition0123 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0593 support0506 2 transition0124 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0015 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0015 support0593 1 transition0123 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0593 support0508 2 transition0125 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0015 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0991 : NodeFacts 991 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0130 support0130 1 transition0978 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0130 support0130 1 transition0979 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0130, supportNumbers0130, fromList]

theorem nodeTailFacts0991 : NodeTailFacts 991 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0130 support0130 1 transition0980 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0130 support0897 1 transition0573 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0897 support0898 1 finish0232 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0130 support0130 1 transition0980 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0130 support0899 1 transition0574 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0899 support0900 1 finish0233 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0130 support0130 1 transition0981 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0130 support0130 1 transition0982 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0130 support0187 1 finish0364 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0130 support0130 1 transition0981 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0130 support1133 1 transition0983 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1133 support1134 1 finish0365 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0992 : NodeFacts 992 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0131 support0206 1 transition0984 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0131 support0207 1 transition0985 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0992 : NodeTailFacts 992 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0131 support0206 1 transition0986 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0206 support1135 1 transition0987 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1135 support1136 1 finish0366 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0131 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0131 support0206 1 transition0986 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0206 support1137 1 transition0988 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1137 support1138 1 finish0367 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0131 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0131 support1139 1 transition0989 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1139 support0506 1 transition0990 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0131 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0131 support1139 1 transition0989 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1139 support0508 1 transition0991 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0131 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0993 : NodeFacts 993 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0073 support0130 1 transition0570 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0073 support0131 1 transition0571 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0993 : NodeTailFacts 993 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0073 support0130 1 transition0572 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0130 support0897 1 transition0573 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0897 support0898 1 finish0232 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0073 support0130 1 transition0572 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0130 support0899 1 transition0574 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0899 support0900 1 finish0233 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0073 support0901 1 transition0575 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0901 support0902 1 transition0576 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0902 support0862 1 finish0234 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0073 support0901 1 transition0575 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0901 support0903 1 transition0577 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0903 support0904 1 finish0235 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0994 : NodeFacts 994 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0074 support0036 1 transition0578 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0074 support0037 1 transition0579 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0994 : NodeTailFacts 994 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0074 support0036 1 transition0580 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0036 support0073 1 transition0121 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0073 support0114 1 finish0058 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0074 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0074 support0036 1 transition0580 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0036 support0591 1 transition0122 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0591 support0592 1 finish0059 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0074 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0074 support0593 1 transition0581 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0593 support0506 2 transition0124 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0074 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0074 support0593 1 transition0581 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0593 support0508 2 transition0125 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0074 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0995 : NodeFacts 995 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0199 support0199 1 transition1446 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0199 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0199 support0199 1 transition1447 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0199, supportNumbers0199, fromList]

theorem nodeTailFacts0995 : NodeTailFacts 995 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0199 support0199 1 transition1448 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0199 support1106 1 transition0933 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1106 support0493 1 finish0348 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0199 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0199 support0199 1 transition1448 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0199 support1107 1 transition0934 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1107 support1108 1 finish0349 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0199 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0199 support0199 1 transition1449 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0199 support0199 1 transition1450 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0199 support0030 1 finish0484 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0199 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0199 support0199 1 transition1449 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0199 support1345 1 transition1451 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1345 support1346 1 finish0485 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0199 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0996 : NodeFacts 996 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0373 support0429 1 transition2560 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0373 support0430 1 transition2561 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0996 : NodeTailFacts 996 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0373 support0429 1 transition2562 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0429 support1678 1 transition2563 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1678 support0857 1 finish0650 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0373 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0373 support0429 1 transition2562 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0429 support1679 1 transition2564 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1679 support1680 1 finish0651 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0373 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0373 support1681 1 transition2565 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1681 support1360 1 transition2566 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0373 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0373 support1681 1 transition2565 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1681 support1362 1 transition2567 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0373 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0997 : NodeFacts 997 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0429 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0429 support0199 1 transition2892 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0199, supportNumbers0199, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0429 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0429 support1745 1 transition2893 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support1745, supportNumbers1745, fromList]

theorem nodeTailFacts0997 : NodeTailFacts 997 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0429 support0199 1 transition2894 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0199 support1106 1 transition0933 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1106 support0493 1 finish0348 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0429 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0429 support0199 1 transition2894 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0199 support1107 1 transition0934 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1107 support1108 1 finish0349 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0429 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0429 support1746 1 transition2895 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1746 support1747 1 transition2896 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1747 support0498 1 finish0678 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0429 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0429 support1746 1 transition2895 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1746 support1748 1 transition2897 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1748 support1749 1 finish0679 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0429 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0998 : NodeFacts 998 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0430 support0377 1 transition2898 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0430 support0378 1 transition2899 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0998 : NodeTailFacts 998 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0430 support0377 1 transition2900 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0377 support0130 1 transition2069 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0130 support0187 1 finish0364 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0430 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0430 support0377 1 transition2900 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0377 support1133 1 transition2070 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1133 support1134 1 finish0365 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0430 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0430 support1553 1 transition2901 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1553 support1360 2 transition2072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0430 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0430 support1553 1 transition2901 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1553 support1362 2 transition2073 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0430 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts0999 : NodeFacts 999 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0431 support0461 1 transition2902 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0431 support0462 1 transition2903 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts0999 : NodeTailFacts 999 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0431 support0461 1 transition2904 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0461 support1750 1 transition2905 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1750 support0885 1 finish0680 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0431 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0431 support0461 1 transition2904 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0461 support1751 1 transition2906 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1751 support1752 1 finish0681 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0431 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0431 support1753 1 transition2907 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1753 support1116 1 transition2908 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1116 support1117 1 finish0354 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0431 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0431 support1753 1 transition2907 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1753 support1118 1 transition2909 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1118 support1119 1 finish0355 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0431 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1000 : NodeFacts 1000 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0432 support0067 1 transition2910 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0432 support0068 1 transition2911 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1000 : NodeTailFacts 1000 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0432 support0067 1 transition2912 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0067 support0697 1 transition0265 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0697 support0698 1 finish0120 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0432 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0432 support0067 1 transition2912 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0067 support0699 1 transition0266 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0699 support0700 1 finish0121 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0432 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0432 support0701 1 transition2913 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0701 support0506 1 transition0268 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0432 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0432 support0701 1 transition2913 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0701 support0508 1 transition0269 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0432 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1001 : NodeFacts 1001 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0123 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0123 support0199 1 transition0930 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0199, supportNumbers0199, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0123 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0123 support0200 1 transition0931 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0200, supportNumbers0200, fromList]

theorem nodeTailFacts1001 : NodeTailFacts 1001 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0123 support0199 1 transition0932 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0199 support1106 1 transition0933 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1106 support0493 1 finish0348 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0123 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0123 support0199 1 transition0932 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0199 support1107 1 transition0934 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1107 support1108 1 finish0349 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0123 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0123 support1109 1 transition0935 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1109 support1110 1 transition0936 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1110 support0688 1 finish0350 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0123 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0123 support1109 1 transition0935 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1109 support1111 1 transition0937 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1111 support1112 1 finish0351 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0123 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1002 : NodeFacts 1002 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0124 support0201 1 transition0938 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0124 support0202 1 transition0939 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1002 : NodeTailFacts 1002 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0124 support0201 1 transition0940 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0201 support0123 1 transition0941 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0123 support0180 1 finish0352 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0124 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0124 support0201 1 transition0940 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0201 support1113 1 transition0942 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1113 support1114 1 finish0353 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0124 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0124 support1115 1 transition0943 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1115 support1116 2 transition0944 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1116 support1117 1 finish0354 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0124 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0124 support1115 1 transition0943 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1115 support1118 2 transition0945 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1118 support1119 1 finish0355 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0124 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1003 : NodeFacts 1003 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0285 support0374 1 transition2034 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0285 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0285 support0374 1 transition2035 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0374, supportNumbers0374, fromList]

theorem nodeTailFacts1003 : NodeTailFacts 1003 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0285 support0374 1 transition2036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0374 support1540 1 transition2037 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1540 support0584 1 finish0582 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0285 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0285 support0374 1 transition2036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0374 support1541 1 transition2038 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1541 support1542 1 finish0583 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0285 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0285 support0374 1 transition2039 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0374 support0374 1 transition2040 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0374 support0065 1 finish0584 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0285 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0285 support0374 1 transition2039 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0374 support1543 1 transition2041 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1543 support1544 1 finish0585 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0285 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1004 : NodeFacts 1004 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0286 support0067 1 transition2042 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0286 support0068 1 transition2043 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1004 : NodeTailFacts 1004 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0286 support0067 1 transition2044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0067 support0697 1 transition0265 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0697 support0698 1 finish0120 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0286 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0286 support0067 1 transition2044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0067 support0699 1 transition0266 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0699 support0700 1 finish0121 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0286 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0286 support0701 1 transition2045 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0701 support0506 1 transition0268 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0286 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0286 support0701 1 transition2045 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0701 support0508 1 transition0269 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0286 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1005 : NodeFacts 1005 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0433 support0374 1 transition2914 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0433 support0432 1 transition2915 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1005 : NodeTailFacts 1005 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0433 support0374 1 transition2916 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0374 support1540 1 transition2037 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1540 support0584 1 finish0582 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0433 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0433 support0374 1 transition2916 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0374 support1541 1 transition2038 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1541 support1542 1 finish0583 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0433 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0433 support1686 1 transition2917 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1686 support0579 1 transition2578 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0579 support0580 1 finish0052 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0433 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0433 support1686 1 transition2917 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1686 support0581 1 transition2579 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0581 support0582 1 finish0053 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0433 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1006 : NodeFacts 1006 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0434 support0067 2 transition2918 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0434 support0068 2 transition2919 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1006 : NodeTailFacts 1006 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0434 support0067 2 transition2920 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0067 support0697 1 transition0265 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0697 support0698 1 finish0120 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0434 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0434 support0067 2 transition2920 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0067 support0699 1 transition0266 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0699 support0700 1 finish0121 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0434 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0434 support0701 2 transition2921 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0701 support0506 1 transition0268 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0434 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0434 support0701 2 transition2921 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0701 support0508 1 transition0269 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0434 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1007 : NodeFacts 1007 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0130 support0130 1 transition1502 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0130 support0296 1 transition1503 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1007 : NodeTailFacts 1007 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0130 support0130 1 transition1504 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0130 support0897 1 transition0573 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0897 support0898 1 finish0232 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0130 support0130 1 transition1504 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0130 support0899 1 transition0574 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0899 support0900 1 finish0233 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0130 support1370 1 transition1505 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1370 support1360 1 transition1506 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0130 support1370 1 transition1505 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1370 support1362 1 transition1507 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0130 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1008 : NodeFacts 1008 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0296 support0377 1 transition2094 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0296 support0378 1 transition2095 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1008 : NodeTailFacts 1008 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0296 support0377 1 transition2096 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0377 support0130 1 transition2069 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0130 support0187 1 finish0364 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0296 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0296 support0377 1 transition2096 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0377 support1133 1 transition2070 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1133 support1134 1 finish0365 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0296 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0296 support1553 1 transition2097 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1553 support1360 2 transition2072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0296 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0296 support1553 1 transition2097 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1553 support1362 2 transition2073 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0296 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1009 : NodeFacts 1009 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0073 support0073 1 transition2098 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0073 support0074 1 transition2099 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1009 : NodeTailFacts 1009 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0073 support0073 1 transition2100 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0073 support0716 1 transition0289 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0716 support0717 1 finish0130 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0073 support0073 1 transition2100 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0073 support0718 1 transition0290 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0718 support0719 1 finish0131 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0073 support0720 1 transition2101 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0720 support0506 1 transition0292 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0073 support0720 1 transition2101 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0720 support0508 1 transition0293 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0073 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1010 : NodeFacts 1010 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0206 support0073 1 transition1508 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0206 support0073 1 transition1509 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1010 : NodeTailFacts 1010 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0206 support0073 1 transition1510 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0073 support0716 1 transition0289 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0716 support0717 1 finish0130 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0206 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0206 support0073 1 transition1510 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0073 support0718 1 transition0290 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0718 support0719 1 finish0131 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0206 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0206 support0073 1 transition1511 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0073 support0073 1 transition1512 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0073 support0114 1 finish0058 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0206 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0206 support0073 1 transition1511 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0073 support0591 1 transition1513 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0591 support0592 1 finish0059 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0206 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1011 : NodeFacts 1011 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0207 support0036 1 transition1514 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0207 support0037 1 transition1515 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1011 : NodeTailFacts 1011 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0207 support0036 1 transition1516 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0036 support0073 1 transition0121 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0073 support0114 1 finish0058 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0207 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0207 support0036 1 transition1516 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0036 support0591 1 transition0122 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0591 support0592 1 finish0059 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0207 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0207 support0593 1 transition1517 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0593 support0506 2 transition0124 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0207 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0207 support0593 1 transition1517 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0593 support0508 2 transition0125 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0207 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1012 : NodeFacts 1012 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0203 support0290 1 transition1474 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0203 support0291 1 transition1475 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1012 : NodeTailFacts 1012 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0203 support0290 1 transition1476 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0290 support1356 1 transition1477 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1356 support0857 1 finish0490 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0203 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0203 support0290 1 transition1476 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0290 support1357 1 transition1478 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1357 support1358 1 finish0491 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0203 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0203 support1359 1 transition1479 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1359 support1360 1 transition1480 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0203 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0203 support1359 1 transition1479 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1359 support1362 1 transition1481 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0203 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1013 : NodeFacts 1013 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0376 support0435 1 transition2588 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0376 support0436 1 transition2589 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1013 : NodeTailFacts 1013 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0376 support0435 1 transition2590 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0435 support0069 1 transition2591 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0069 support0030 1 finish0224 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0376 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0376 support0435 1 transition2590 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0435 support0882 1 transition2592 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0882 support0883 1 finish0225 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0376 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0376 support1688 1 transition2593 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1688 support1121 2 transition2594 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1121 support0498 1 finish0356 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0376 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0376 support1688 1 transition2593 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1688 support1122 2 transition2595 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1122 support1123 1 finish0357 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0376 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1014 : NodeFacts 1014 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0377 support0130 1 transition2596 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0377 support0296 1 transition2597 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1014 : NodeTailFacts 1014 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0377 support0130 1 transition2598 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0130 support0897 1 transition0573 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0897 support0898 1 finish0232 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0377 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0377 support0130 1 transition2598 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0130 support0899 1 transition0574 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0899 support0900 1 finish0233 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0377 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0377 support1370 1 transition2599 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1370 support1360 1 transition1506 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0377 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0377 support1370 1 transition2599 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1370 support1362 1 transition1507 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0377 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1015 : NodeFacts 1015 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0378 support0377 2 transition2600 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0378 support0378 2 transition2601 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1015 : NodeTailFacts 1015 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0378 support0377 2 transition2602 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0377 support0130 1 transition2069 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0130 support0187 1 finish0364 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0378 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0378 support0377 2 transition2602 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0377 support1133 1 transition2070 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1133 support1134 1 finish0365 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0378 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0378 support1553 2 transition2603 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1553 support1360 2 transition2072 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0378 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0378 support1553 2 transition2603 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1553 support1362 2 transition2073 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0378 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1016 : NodeFacts 1016 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0290 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0290 support0069 1 transition2060 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0069, supportNumbers0069, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0290 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0290 support0376 1 transition2061 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0376, supportNumbers0376, fromList]

theorem nodeTailFacts1016 : NodeTailFacts 1016 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0290 support0069 1 transition2062 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0069 support0702 1 transition0273 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0702 support0493 1 finish0122 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0290 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0290 support0069 1 transition2062 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0069 support0703 1 transition0274 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0703 support0704 1 finish0123 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0290 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0290 support1549 1 transition2063 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1549 support1550 1 transition2064 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1550 support1537 1 finish0588 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0290 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0290 support1549 1 transition2063 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1549 support1551 1 transition2065 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1551 support1552 1 finish0589 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0290 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1017 : NodeFacts 1017 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0291 support0377 1 transition2066 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0291 support0378 1 transition2067 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1017 : NodeTailFacts 1017 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0291 support0377 1 transition2068 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0377 support0130 1 transition2069 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0130 support0187 1 finish0364 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0291 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0291 support0377 1 transition2068 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0377 support1133 1 transition2070 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1133 support1134 1 finish0365 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0291 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0291 support1553 1 transition2071 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1553 support1360 2 transition2072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0291 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0291 support1553 1 transition2071 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1553 support1362 2 transition2073 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0291 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1018 : NodeFacts 1018 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0435 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0435 support0069 1 transition2922 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0069, supportNumbers0069, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0435 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0435 support0203 1 transition2923 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0203, supportNumbers0203, fromList]

theorem nodeTailFacts1018 : NodeTailFacts 1018 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0435 support0069 1 transition2924 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0069 support0702 1 transition0273 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0702 support0493 1 finish0122 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0435 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0435 support0069 1 transition2924 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0069 support0703 1 transition0274 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0703 support0704 1 finish0123 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0435 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0435 support1120 1 transition2925 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1120 support1121 1 transition0950 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1121 support0498 1 finish0356 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0435 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0435 support1120 1 transition2925 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1120 support1122 1 transition0951 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1122 support1123 1 finish0357 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0435 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1019 : NodeFacts 1019 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0436 support0290 2 transition2926 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0436 support0291 2 transition2927 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1019 : NodeTailFacts 1019 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0436 support0290 2 transition2928 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0290 support1356 1 transition1477 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1356 support0857 1 finish0490 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0436 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0436 support0290 2 transition2928 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0290 support1357 1 transition1478 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1357 support1358 1 finish0491 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0436 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0436 support1359 2 transition2929 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1359 support1360 1 transition1480 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1360 support1361 1 finish0492 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0436 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0436 support1359 2 transition2929 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1359 support1362 1 transition1481 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1362 support1363 1 finish0493 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0436 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1020 : NodeFacts 1020 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0034 support0034 1 transition2930 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0034 support0127 1 transition2931 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1020 : NodeTailFacts 1020 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0034 support0034 1 transition2932 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0034 support0583 1 transition0113 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0583 support0584 1 finish0054 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0034 support0034 1 transition2932 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0034 support0585 1 transition0114 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0585 support0586 1 finish0055 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0034 support0892 1 transition2933 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0892 support0712 1 transition0560 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0712 support0713 1 finish0128 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0034 support0892 1 transition2933 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0892 support0714 1 transition0561 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0714 support0715 1 finish0129 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1021 : NodeFacts 1021 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0128 support0204 1 transition0968 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0128 support0205 1 transition0969 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1021 : NodeTailFacts 1021 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0128 support0204 1 transition0970 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0204 support1124 1 transition0955 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1124 support0874 1 finish0358 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0128 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0128 support0204 1 transition0970 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0204 support1125 1 transition0956 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1125 support1126 1 finish0359 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0128 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0128 support1129 1 transition0971 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1129 support1130 1 transition0972 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1130 support1117 1 finish0362 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0128 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0128 support1129 1 transition0971 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1129 support1131 1 transition0973 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1131 support1132 1 finish0363 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0128 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1022 : NodeFacts 1022 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0129 support0036 1 transition0974 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0129 support0037 1 transition0975 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1022 : NodeTailFacts 1022 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0129 support0036 1 transition0976 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0036 support0073 1 transition0121 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0073 support0114 1 finish0058 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0129 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0129 support0036 1 transition0976 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0036 support0591 1 transition0122 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0591 support0592 1 finish0059 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0129 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0129 support0593 1 transition0977 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0593 support0506 2 transition0124 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0129 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0129 support0593 1 transition0977 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0593 support0508 2 transition0125 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0129 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1023 : NodeFacts 1023 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0034 support0069 1 transition0270 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0069, supportNumbers0069, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0034 support0070 1 transition0271 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0070, supportNumbers0070, fromList]

theorem nodeTailFacts1023 : NodeTailFacts 1023 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0034 support0069 1 transition0272 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0069 support0702 1 transition0273 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0702 support0493 1 finish0122 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0034 support0069 1 transition0272 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0069 support0703 1 transition0274 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0703 support0704 1 finish0123 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0034 support0705 1 transition0275 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0705 support0706 1 transition0276 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0706 support0688 1 finish0124 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0034 support0705 1 transition0275 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0705 support0707 1 transition0277 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0707 support0708 1 finish0125 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0034 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
