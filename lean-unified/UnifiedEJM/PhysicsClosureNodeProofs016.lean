import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureEdges

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeFacts1024 : NodeFacts 1024 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0035 support0071 1 transition0278 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0035 support0072 1 transition0279 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1024 : NodeTailFacts 1024 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0035 support0071 1 transition0280 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0071 support0034 1 transition0281 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0034 support0065 1 finish0126 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0035 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0035 support0071 1 transition0280 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0071 support0709 1 transition0282 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0709 support0710 1 finish0127 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0035 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0035 support0711 1 transition0283 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0711 support0712 2 transition0284 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0712 support0713 1 finish0128 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0035 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0035 support0711 1 transition0283 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0711 support0714 2 transition0285 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0714 support0715 1 finish0129 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0035 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1025 : NodeFacts 1025 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0125 support0204 1 transition0952 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0125 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0125 support0204 1 transition0953 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0204, supportNumbers0204, fromList]

theorem nodeTailFacts1025 : NodeTailFacts 1025 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0125 support0204 1 transition0954 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0204 support1124 1 transition0955 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1124 support0874 1 finish0358 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0125 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0125 support0204 1 transition0954 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0204 support1125 1 transition0956 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1125 support1126 1 finish0359 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0125 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0125 support0204 1 transition0957 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0204 support0204 1 transition0958 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0204 support0180 1 finish0360 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0125 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0125 support0204 1 transition0957 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0204 support1127 1 transition0959 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1127 support1128 1 finish0361 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0125 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1026 : NodeFacts 1026 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0126 support0014 1 transition0960 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0126 support0015 1 transition0961 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1026 : NodeTailFacts 1026 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0126 support0014 1 transition0962 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0014 support0501 1 transition0027 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0501 support0502 1 finish0012 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0126 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0126 support0014 1 transition0962 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0014 support0503 1 transition0028 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0503 support0504 1 finish0013 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0126 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0126 support0505 1 transition0963 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0505 support0506 1 transition0030 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0126 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0126 support0505 1 transition0963 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0505 support0508 1 transition0031 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0126 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1027 : NodeFacts 1027 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0127 support0128 1 transition0964 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0127 support0129 1 transition0965 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1027 : NodeTailFacts 1027 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0127 support0128 1 transition0966 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0128 support0893 1 transition0565 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0893 support0698 1 finish0230 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0127 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0127 support0128 1 transition0966 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0128 support0894 1 transition0566 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0894 support0895 1 finish0231 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0127 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0127 support0896 1 transition0967 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0896 support0506 1 transition0568 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0506 support0507 1 finish0014 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0127 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0127 support0896 1 transition0967 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0896 support0508 1 transition0569 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0508 support0509 1 finish0015 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0127 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1028 : NodeFacts 1028 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0292 support0379 1 transition2074 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0292 support0380 1 transition2075 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1028 : NodeTailFacts 1028 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0292 support0379 1 transition2076 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0379 support1554 1 transition2077 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1554 support0575 1 finish0590 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0292 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0292 support0379 1 transition2076 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0379 support1555 1 transition2078 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1555 support1556 1 finish0591 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0292 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0292 support1557 1 transition2079 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1557 support0712 1 transition2080 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0712 support0713 1 finish0128 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0292 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0292 support1557 1 transition2079 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1557 support0714 1 transition2081 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0714 support0715 1 finish0129 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0292 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1029 : NodeFacts 1029 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0016 support0016 1 transition0126 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0016 (1 / (2 : ℚ) ^ 4) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0016 support0016 1 transition0127 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0016, supportNumbers0016, fromList]

theorem nodeTailFacts1029 : NodeTailFacts 1029 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0016 support0016 1 transition0128 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0510 1 transition0035 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0510 support0511 1 finish0016 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0016 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0016 support0016 1 transition0128 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 4) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0512 1 transition0036 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0512 support0513 1 finish0017 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0016 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0016 support0016 1 transition0129 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0016 1 transition0130 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0016 support0594 1 finish0060 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0016 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0016 support0016 1 transition0129 (1 / (2 : ℚ) ^ 4) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0595 1 transition0131 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0595 support0044 1 finish0061 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0016 (1 / (2 : ℚ) ^ 4) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1030 : NodeFacts 1030 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0075 support0132 1 transition0582 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0075 support0133 1 transition0583 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1030 : NodeTailFacts 1030 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0075 support0132 1 transition0584 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0132 support0905 1 transition0585 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0905 support0906 1 finish0236 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0075 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0075 support0132 1 transition0584 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0132 support0907 1 transition0586 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0907 support0908 1 finish0237 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0075 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0075 support0909 1 transition0587 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0909 support0910 1 transition0588 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0910 support0911 1 finish0238 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0075 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0075 support0909 1 transition0587 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0909 support0912 1 transition0589 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0912 support0913 1 finish0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0075 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1031 : NodeFacts 1031 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0208 support0297 1 transition1518 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0208 support0298 1 transition1519 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1031 : NodeTailFacts 1031 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0208 support0297 1 transition1520 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0297 support0016 1 transition1521 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0016 support0594 1 finish0060 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0208 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0208 support0297 1 transition1520 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0297 support0595 1 transition1522 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0595 support0044 1 finish0061 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0208 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0208 support1371 1 transition1523 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1371 support0722 2 transition1524 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0722 support0723 1 finish0132 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0208 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0208 support1371 1 transition1523 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1371 support0724 2 transition1525 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0724 support0725 1 finish0133 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0208 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1032 : NodeFacts 1032 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0209 support0299 1 transition1526 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0209 support0300 1 transition1527 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1032 : NodeTailFacts 1032 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0209 support0299 1 transition1528 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0299 support1372 1 transition1529 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1372 support1373 1 finish0496 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0209 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0209 support0299 1 transition1528 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0299 support1374 1 transition1530 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1374 support1375 1 finish0497 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0209 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0209 support1376 1 transition1531 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1376 support0910 1 transition1532 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0910 support0911 1 finish0238 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0209 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0209 support1376 1 transition1531 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1376 support0912 1 transition1533 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0912 support0913 1 finish0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0209 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1033 : NodeFacts 1033 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0210 support0209 2 transition1534 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0210 support0210 2 transition1535 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1033 : NodeTailFacts 1033 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0210 support0209 2 transition1536 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0209 support0299 1 transition1001 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0299 support1145 1 finish0370 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0210 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0210 support0209 2 transition1536 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0209 support1146 1 transition1002 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1146 support0229 1 finish0371 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0210 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0210 support1147 2 transition1537 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1147 support0910 2 transition1004 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0910 support0911 1 finish0238 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0210 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0210 support1147 2 transition1537 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1147 support0912 2 transition1005 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0912 support0913 1 finish0239 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0210 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1034 : NodeFacts 1034 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0299 support0299 1 transition2614 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0299 support0300 1 transition2615 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1034 : NodeTailFacts 1034 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0299 support0299 1 transition2616 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0299 support1372 1 transition1529 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1372 support1373 1 finish0496 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0299 support0299 1 transition2616 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0299 support1374 1 transition1530 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1374 support1375 1 finish0497 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0299 support1376 1 transition2617 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1376 support0910 1 transition1532 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0910 support0911 1 finish0238 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0299 support1376 1 transition2617 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1376 support0912 1 transition1533 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0912 support0913 1 finish0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1035 : NodeFacts 1035 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0132 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0132 support0016 1 transition0992 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0016, supportNumbers0016, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0132 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0132 support0208 1 transition0993 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0208, supportNumbers0208, fromList]

theorem nodeTailFacts1035 : NodeTailFacts 1035 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0132 support0016 1 transition0994 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0510 1 transition0035 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0510 support0511 1 finish0016 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0132 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0132 support0016 1 transition0994 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0512 1 transition0036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0512 support0513 1 finish0017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0132 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0132 support1140 1 transition0995 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1140 support1141 1 transition0996 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1141 support1142 1 finish0368 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0132 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0132 support1140 1 transition0995 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1140 support1143 1 transition0997 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1143 support1144 1 finish0369 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0132 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1036 : NodeFacts 1036 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0133 support0209 1 transition0998 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0133 support0210 1 transition0999 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1036 : NodeTailFacts 1036 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0133 support0209 1 transition1000 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0209 support0299 1 transition1001 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0299 support1145 1 finish0370 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0133 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0133 support0209 1 transition1000 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0209 support1146 1 transition1002 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1146 support0229 1 finish0371 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0133 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0133 support1147 1 transition1003 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1147 support0910 2 transition1004 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0910 support0911 1 finish0238 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0133 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0133 support1147 1 transition1003 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1147 support0912 2 transition1005 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0912 support0913 1 finish0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0133 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1037 : NodeFacts 1037 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0297 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0297 support0016 1 transition2102 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0016, supportNumbers0016, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0297 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0297 support0075 1 transition2103 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0075, supportNumbers0075, fromList]

theorem nodeTailFacts1037 : NodeTailFacts 1037 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0297 support0016 1 transition2104 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0510 1 transition0035 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0510 support0511 1 finish0016 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0297 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0297 support0016 1 transition2104 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0512 1 transition0036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0512 support0513 1 finish0017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0297 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0297 support0721 1 transition2105 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0721 support0722 1 transition0302 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0722 support0723 1 finish0132 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0297 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0297 support0721 1 transition2105 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0721 support0724 1 transition0303 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0724 support0725 1 finish0133 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0297 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1038 : NodeFacts 1038 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0298 support0132 2 transition2106 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0298 support0133 2 transition2107 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1038 : NodeTailFacts 1038 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0298 support0132 2 transition2108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0132 support0905 1 transition0585 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0905 support0906 1 finish0236 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0298 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0298 support0132 2 transition2108 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0132 support0907 1 transition0586 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0907 support0908 1 finish0237 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0298 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0298 support0909 2 transition2109 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0909 support0910 1 transition0588 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0910 support0911 1 finish0238 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0298 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0298 support0909 2 transition2109 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0909 support0912 1 transition0589 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0912 support0913 1 finish0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0298 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1039 : NodeFacts 1039 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0299 support0299 1 transition2110 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0299 support0299 1 transition2111 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0299, supportNumbers0299, fromList]

theorem nodeTailFacts1039 : NodeTailFacts 1039 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0299 support0299 1 transition2112 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0299 support1372 1 transition1529 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1372 support1373 1 finish0496 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0299 support0299 1 transition2112 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0299 support1374 1 transition1530 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1374 support1375 1 finish0497 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0299 support0299 1 transition2113 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0299 support0299 1 transition2114 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0299 support1145 1 finish0370 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0299 support0299 1 transition2113 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0299 support1146 1 transition2115 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1146 support0229 1 finish0371 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0299 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1040 : NodeFacts 1040 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0300 support0209 1 transition2116 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0300 support0210 1 transition2117 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1040 : NodeTailFacts 1040 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0300 support0209 1 transition2118 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0209 support0299 1 transition1001 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0299 support1145 1 finish0370 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0300 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0300 support0209 1 transition2118 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0209 support1146 1 transition1002 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1146 support0229 1 finish0371 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0300 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0300 support1147 1 transition2119 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1147 support0910 2 transition1004 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0910 support0911 1 finish0238 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0300 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0300 support1147 1 transition2119 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1147 support0912 2 transition1005 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0912 support0913 1 finish0239 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0300 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1041 : NodeFacts 1041 := by
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

theorem nodeTailFacts1041 : NodeTailFacts 1041 := by
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

theorem nodeFacts1042 : NodeFacts 1042 := by
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

theorem nodeTailFacts1042 : NodeTailFacts 1042 := by
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

theorem nodeFacts1043 : NodeFacts 1043 := by
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

theorem nodeTailFacts1043 : NodeTailFacts 1043 := by
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

theorem nodeFacts1044 : NodeFacts 1044 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0134 support0211 1 transition1006 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0134 support0212 1 transition1007 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1044 : NodeTailFacts 1044 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0134 support0211 1 transition1008 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0211 support1148 1 transition1009 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1148 support1149 1 finish0372 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0134 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0134 support0211 1 transition1008 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0211 support1150 1 transition1010 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1150 support1151 1 finish0373 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0134 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0134 support1152 1 transition1011 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1152 support1153 1 transition1012 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1153 support1154 1 finish0374 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0134 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0134 support1152 1 transition1011 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1152 support1155 1 transition1013 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1155 support0938 1 finish0375 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0134 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1045 : NodeFacts 1045 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0437 support0076 1 transition2934 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0437 support0135 1 transition2935 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1045 : NodeTailFacts 1045 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0437 support0076 1 transition2936 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0076 support0726 1 transition0307 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0726 support0727 1 finish0134 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0437 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0437 support0076 1 transition2936 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0076 support0728 1 transition0308 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0728 support0729 1 finish0135 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0437 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0437 support0918 1 transition2937 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0918 support0601 1 transition0600 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0601 support0602 1 finish0064 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0437 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0437 support0918 1 transition2937 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0918 support0603 1 transition0601 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0603 support0604 1 finish0065 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0437 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1046 : NodeFacts 1046 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0438 support0077 2 transition2938 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0438 support0078 2 transition2939 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1046 : NodeTailFacts 1046 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0438 support0077 2 transition2940 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0077 support0732 1 transition0315 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0732 support0733 1 finish0138 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0438 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0438 support0077 2 transition2940 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0077 support0734 1 transition0316 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0734 support0735 1 finish0139 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0438 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0438 support0736 2 transition2941 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0736 support0737 1 transition0318 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0438 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0438 support0736 2 transition2941 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0736 support0739 1 transition0319 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0438 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1047 : NodeFacts 1047 := by
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

theorem nodeTailFacts1047 : NodeTailFacts 1047 := by
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

theorem nodeFacts1048 : NodeFacts 1048 := by
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

theorem nodeTailFacts1048 : NodeTailFacts 1048 := by
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

theorem nodeFacts1049 : NodeFacts 1049 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0004 support0016 1 transition0032 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0016, supportNumbers0016, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0004 support0017 1 transition0033 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0017, supportNumbers0017, fromList]

theorem nodeTailFacts1049 : NodeTailFacts 1049 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0004 support0016 1 transition0034 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0510 1 transition0035 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0510 support0511 1 finish0016 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0004 support0016 1 transition0034 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0512 1 transition0036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0512 support0513 1 finish0017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0004 support0514 1 transition0037 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0514 support0515 1 transition0038 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0515 support0516 1 finish0018 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0004 support0514 1 transition0037 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0514 support0517 1 transition0039 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0517 support0518 1 finish0019 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0004 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1050 : NodeFacts 1050 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0303 support0301 1 transition2134 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0303 support0302 1 transition2135 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1050 : NodeTailFacts 1050 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0303 support0301 1 transition2136 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0301 support1377 1 transition1547 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1377 support1378 1 finish0498 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0303 support0301 1 transition2136 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0301 support1379 1 transition1548 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1379 support0613 1 finish0499 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0303 support1380 1 transition2137 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1380 support0737 1 transition1550 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0303 support1380 1 transition2137 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1380 support0739 1 transition1551 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0303 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1051 : NodeFacts 1051 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0076 support0016 1 transition0590 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0016, supportNumbers0016, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0076 support0134 1 transition0591 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0134, supportNumbers0134, fromList]

theorem nodeTailFacts1051 : NodeTailFacts 1051 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0076 support0016 1 transition0592 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0510 1 transition0035 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0510 support0511 1 finish0016 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0076 support0016 1 transition0592 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0512 1 transition0036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0512 support0513 1 finish0017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0076 support0914 1 transition0593 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0914 support0915 1 transition0594 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0915 support0916 1 finish0240 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0076 support0914 1 transition0593 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0914 support0917 1 transition0595 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0917 support0744 1 finish0241 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0076 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1052 : NodeFacts 1052 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0381 support0437 1 transition2618 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0381 support0438 1 transition2619 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1052 : NodeTailFacts 1052 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0381 support0437 1 transition2620 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0437 support0076 1 transition2621 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0076 support0730 1 finish0136 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0381 support0437 1 transition2620 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0437 support0731 1 transition2622 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0731 support0088 1 finish0137 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0381 support1689 1 transition2623 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1689 support0601 2 transition2624 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0601 support0602 1 finish0064 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0381 support1689 1 transition2623 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1689 support0603 2 transition2625 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0603 support0604 1 finish0065 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0381 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1053 : NodeFacts 1053 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0137 support0215 1 transition1026 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0137 support0216 1 transition1027 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1053 : NodeTailFacts 1053 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0137 support0215 1 transition1028 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0215 support1159 1 transition1029 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1159 support1160 1 finish0378 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0137 support0215 1 transition1028 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0215 support1161 1 transition1030 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1161 support0522 1 finish0379 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0137 support1162 1 transition1031 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1162 support0737 1 transition1032 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0137 support1162 1 transition1031 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1162 support0739 1 transition1033 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0137 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1054 : NodeFacts 1054 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0138 support0137 2 transition1034 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0138 support0138 2 transition1035 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1054 : NodeTailFacts 1054 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0138 support0137 2 transition1036 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0137 support0215 1 transition0613 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0215 support0928 1 finish0246 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0138 support0137 2 transition1036 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0137 support0929 1 transition0614 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0929 support0148 1 finish0247 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0138 support0930 2 transition1037 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0930 support0737 2 transition0616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0138 support0930 2 transition1037 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0930 support0739 2 transition0617 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0138 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1055 : NodeFacts 1055 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0038 support0076 1 transition0304 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0038 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0038 support0076 1 transition0305 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0076, supportNumbers0076, fromList]

theorem nodeTailFacts1055 : NodeTailFacts 1055 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0038 support0076 1 transition0306 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0076 support0726 1 transition0307 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0726 support0727 1 finish0134 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0038 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0038 support0076 1 transition0306 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0076 support0728 1 transition0308 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0728 support0729 1 finish0135 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0038 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0038 support0076 1 transition0309 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0076 support0076 1 transition0310 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0076 support0730 1 finish0136 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0038 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0038 support0076 1 transition0309 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0076 support0731 1 transition0311 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0731 support0088 1 finish0137 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0038 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1056 : NodeFacts 1056 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0039 support0077 1 transition0312 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0039 support0078 1 transition0313 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1056 : NodeTailFacts 1056 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0039 support0077 1 transition0314 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0077 support0732 1 transition0315 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0732 support0733 1 finish0138 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0039 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0039 support0077 1 transition0314 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0077 support0734 1 transition0316 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0734 support0735 1 finish0139 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0039 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0039 support0736 1 transition0317 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0736 support0737 1 transition0318 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0039 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0039 support0736 1 transition0317 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0736 support0739 1 transition0319 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0039 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1057 : NodeFacts 1057 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0304 support0382 1 transition2138 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0304 support0383 1 transition2139 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1057 : NodeTailFacts 1057 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0304 support0382 1 transition2140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0382 support1562 1 transition2141 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1562 support1563 1 finish0594 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0304 support0382 1 transition2140 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0382 support1564 1 transition2142 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1564 support1565 1 finish0595 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0304 support1566 1 transition2143 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1566 support0737 1 transition2144 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0304 support1566 1 transition2143 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1566 support0739 1 transition2145 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0304 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1058 : NodeFacts 1058 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0135 support0077 1 transition1014 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0135 support0078 1 transition1015 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1058 : NodeTailFacts 1058 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0135 support0077 1 transition1016 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0077 support0732 1 transition0315 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0732 support0733 1 finish0138 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0135 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0135 support0077 1 transition1016 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0077 support0734 1 transition0316 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0734 support0735 1 finish0139 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0135 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0135 support0736 1 transition1017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0736 support0737 1 transition0318 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0135 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0135 support0736 1 transition1017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0736 support0739 1 transition0319 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0135 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1059 : NodeFacts 1059 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0136 support0213 1 transition1018 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0136 support0214 1 transition1019 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1059 : NodeTailFacts 1059 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0136 support0213 1 transition1020 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0213 support0004 1 transition1021 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0004 support1156 1 finish0376 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0136 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0136 support0213 1 transition1020 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0213 support1157 1 transition1022 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1157 support0222 1 finish0377 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0136 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0136 support1158 1 transition1023 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1158 support1153 2 transition1024 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1153 support1154 1 finish0374 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0136 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0136 support1158 1 transition1023 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1158 support1155 2 transition1025 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1155 support0938 1 finish0375 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0136 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1060 : NodeFacts 1060 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0215 support0215 1 transition2942 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0215 support0216 1 transition2943 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1060 : NodeTailFacts 1060 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0215 support0215 1 transition2944 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0215 support1159 1 transition1029 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1159 support1160 1 finish0378 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0215 support0215 1 transition2944 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0215 support1161 1 transition1030 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1161 support0522 1 finish0379 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0215 support1162 1 transition2945 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1162 support0737 1 transition1032 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0737 support0738 1 finish0140 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0215 support1162 1 transition2945 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1162 support0739 1 transition1033 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0739 support0527 1 finish0141 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0215 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1061 : NodeFacts 1061 := by
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

theorem nodeTailFacts1061 : NodeTailFacts 1061 := by
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

theorem nodeFacts1062 : NodeFacts 1062 := by
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

theorem nodeTailFacts1062 : NodeTailFacts 1062 := by
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

theorem nodeFacts1063 : NodeFacts 1063 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0040 support0040 1 transition2946 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0040 support0441 1 transition2947 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1063 : NodeTailFacts 1063 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0040 support0040 1 transition2948 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0040 support0605 1 transition0143 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0605 support0606 1 finish0066 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0040 support0040 1 transition2948 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0040 support0607 1 transition0144 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0607 support0599 1 finish0067 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0040 support1694 1 transition2949 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1694 support1571 1 transition2654 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1571 support1572 1 finish0598 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0040 support1694 1 transition2949 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1694 support1573 1 transition2655 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1573 support0604 1 finish0599 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1064 : NodeFacts 1064 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0439 support0217 1 transition2950 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0439 support0463 1 transition2951 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1064 : NodeTailFacts 1064 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0439 support0217 1 transition2952 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0217 support1163 1 transition1041 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1163 support1164 1 finish0380 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0439 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0439 support0217 1 transition2952 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0217 support1165 1 transition1042 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1165 support1151 1 finish0381 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0439 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0439 support1754 1 transition2953 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1754 support1755 1 transition2954 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1755 support1756 1 finish0682 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0439 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0439 support1754 1 transition2953 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1754 support1757 1 transition2955 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1757 support0927 1 finish0683 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0439 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1065 : NodeFacts 1065 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0440 support0308 1 transition2956 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0440 support0309 1 transition2957 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1065 : NodeTailFacts 1065 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0440 support0308 1 transition2958 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0308 support0388 1 transition1593 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0388 support1395 1 finish0506 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0440 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0440 support0308 1 transition2958 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0308 support1396 1 transition1594 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1396 support0148 1 finish0507 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0440 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0440 support1397 1 transition2959 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1397 support1171 2 transition1596 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0440 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0440 support1397 1 transition2959 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1397 support1173 2 transition1597 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0440 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1066 : NodeFacts 1066 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0384 support0040 1 transition2636 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0384 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0384 support0040 1 transition2637 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0040, supportNumbers0040, fromList]

theorem nodeTailFacts1066 : NodeTailFacts 1066 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0384 support0040 1 transition2638 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0040 support0605 1 transition0143 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0605 support0606 1 finish0066 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0384 support0040 1 transition2638 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0040 support0607 1 transition0144 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0607 support0599 1 finish0067 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0384 support0040 1 transition2639 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0040 support0040 1 transition2640 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0040 support1574 1 finish0600 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0384 support0040 1 transition2639 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0040 support0041 1 transition2641 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0041 support0088 1 finish0601 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0384 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1067 : NodeFacts 1067 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0385 support0439 1 transition2642 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0385 support0440 1 transition2643 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1067 : NodeTailFacts 1067 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0385 support0439 1 transition2644 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0439 support1690 1 transition2645 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1690 support1691 1 finish0654 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0385 support0439 1 transition2644 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0439 support1692 1 transition2646 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1692 support0613 1 finish0655 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0385 support1693 1 transition2647 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1693 support1171 1 transition2648 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0385 support1693 1 transition2647 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1693 support1173 1 transition2649 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0385 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1068 : NodeFacts 1068 := by
  intro c
  cases c
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0040 support0016 1 transition0320 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0016, supportNumbers0016, fromList]
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0040 support0079 1 transition0321 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0079, supportNumbers0079, fromList]

theorem nodeTailFacts1068 : NodeTailFacts 1068 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0040 support0016 1 transition0322 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 support0510 1 transition0035 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0510 support0511 1 finish0016 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0040 support0016 1 transition0322 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 support0512 1 transition0036 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0512 support0513 1 finish0017 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0040 support0740 1 transition0323 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0740 support0741 1 transition0324 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0741 support0742 1 finish0142 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0040 support0740 1 transition0323 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0740 support0743 1 transition0325 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0743 support0744 1 finish0143 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0040 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1069 : NodeFacts 1069 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0307 support0386 1 transition2158 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0307 support0387 1 transition2159 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1069 : NodeTailFacts 1069 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0307 support0386 1 transition2160 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0386 support0040 1 transition2161 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0040 support1574 1 finish0600 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0307 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0307 support0386 1 transition2160 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0386 support0041 1 transition2162 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0041 support0088 1 finish0601 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0307 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0307 support1575 1 transition2163 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1575 support1571 2 transition2164 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1571 support1572 1 finish0598 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0307 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0307 support1575 1 transition2163 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1575 support1573 2 transition2165 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1573 support0604 1 finish0599 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0307 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1070 : NodeFacts 1070 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0308 support0388 1 transition2166 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0308 support0389 1 transition2167 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1070 : NodeTailFacts 1070 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0308 support0388 1 transition2168 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0388 support1576 1 transition2169 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1576 support1577 1 finish0602 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0308 support0388 1 transition2168 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0388 support1578 1 transition2170 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1578 support1565 1 finish0603 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0308 support1579 1 transition2171 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1579 support1171 1 transition2172 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0308 support1579 1 transition2171 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1579 support1173 1 transition2173 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0308 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1071 : NodeFacts 1071 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0309 support0308 2 transition2174 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0309 support0309 2 transition2175 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1071 : NodeTailFacts 1071 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0309 support0308 2 transition2176 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0308 support0388 1 transition1593 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0388 support1395 1 finish0506 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0309 support0308 2 transition2176 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0308 support1396 1 transition1594 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1396 support0148 1 finish0507 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0309 support1397 2 transition2177 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1397 support1171 2 transition1596 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0309 support1397 2 transition2177 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1397 support1173 2 transition1597 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0309 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1072 : NodeFacts 1072 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0139 support0217 1 transition1038 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0139 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0139 support0217 1 transition1039 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0217, supportNumbers0217, fromList]

theorem nodeTailFacts1072 : NodeTailFacts 1072 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0139 support0217 1 transition1040 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0217 support1163 1 transition1041 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1163 support1164 1 finish0380 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0139 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0139 support0217 1 transition1040 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0217 support1165 1 transition1042 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1165 support1151 1 finish0381 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0139 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0139 support0217 1 transition1043 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0217 support0217 1 transition1044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0217 support1166 1 finish0382 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0139 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0139 support0217 1 transition1043 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0217 support0310 1 transition1045 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0310 support0222 1 finish0383 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0139 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1073 : NodeFacts 1073 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0140 support0218 1 transition1046 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0140 support0219 1 transition1047 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1073 : NodeTailFacts 1073 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0140 support0218 1 transition1048 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0218 support1167 1 transition1049 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1167 support1168 1 finish0384 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0140 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0140 support0218 1 transition1048 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0218 support1169 1 transition1050 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1169 support0735 1 finish0385 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0140 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0140 support1170 1 transition1051 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1170 support1171 1 transition1052 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0140 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0140 support1170 1 transition1051 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1170 support1173 1 transition1053 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0140 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1074 : NodeFacts 1074 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0441 support0439 1 transition2960 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0441 support0440 1 transition2961 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1074 : NodeTailFacts 1074 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0441 support0439 1 transition2962 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0439 support1690 1 transition2645 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1690 support1691 1 finish0654 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0441 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0441 support0439 1 transition2962 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0439 support1692 1 transition2646 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1692 support0613 1 finish0655 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0441 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0441 support1693 1 transition2963 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1693 support1171 1 transition2648 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0441 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0441 support1693 1 transition2963 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1693 support1173 1 transition2649 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0441 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1075 : NodeFacts 1075 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0442 support0464 1 transition2964 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0442 support0465 1 transition2965 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1075 : NodeTailFacts 1075 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0442 support0464 1 transition2966 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0464 support1758 1 transition2967 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1758 support1759 1 finish0684 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0442 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0442 support0464 1 transition2966 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0464 support1760 1 transition2968 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1760 support0522 1 finish0685 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0442 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0442 support1761 1 transition2969 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1761 support1171 1 transition2970 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1171 support1172 1 finish0386 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0442 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0442 support1761 1 transition2969 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1761 support1173 1 transition2971 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1173 support0527 1 finish0387 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0442 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1076 : NodeFacts 1076 := by
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

theorem nodeTailFacts1076 : NodeTailFacts 1076 := by
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

theorem nodeFacts1077 : NodeFacts 1077 := by
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

theorem nodeTailFacts1077 : NodeTailFacts 1077 := by
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

theorem nodeFacts1078 : NodeFacts 1078 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0005 support0018 1 transition0040 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0005 support0019 1 transition0041 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1078 : NodeTailFacts 1078 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0005 support0018 1 transition0042 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0018 support0519 1 transition0043 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0519 support0520 1 finish0020 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0005 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0005 support0018 1 transition0042 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0018 support0521 1 transition0044 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0521 support0522 1 finish0021 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0005 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0005 support0523 1 transition0045 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0523 support0524 1 transition0046 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0524 support0525 1 finish0022 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0005 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0005 support0523 1 transition0045 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0523 support0526 1 transition0047 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0526 support0527 1 finish0023 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0005 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1079 : NodeFacts 1079 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0328 support0088 1 transition2302 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0328 support0408 1 transition2303 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1079 : NodeTailFacts 1079 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0328 support0088 1 transition2304 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0088 support0766 1 transition0367 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0766 support0767 1 finish0160 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0328 support0088 1 transition2304 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0088 support0768 1 transition0368 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0768 support0088 1 finish0161 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0328 support1606 1 transition2305 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1606 support1607 1 transition2306 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1607 support1608 1 finish0616 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0328 support1606 1 transition2305 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1606 support1609 1 transition2307 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1609 support0612 2 finish0617 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0328 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1080 : NodeFacts 1080 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0329 support0084 1 transition2308 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0329 support0085 1 transition2309 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1080 : NodeTailFacts 1080 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0329 support0084 1 transition2310 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 support0148 1 transition0345 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0148 support0679 1 finish0152 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0329 support0084 1 transition2310 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 support0149 1 transition0346 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0149 support0148 2 finish0153 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0329 support0757 1 transition2311 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0757 support0616 2 transition0348 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0329 support0757 1 transition2311 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0757 support0618 2 transition0349 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0329 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1081 : NodeFacts 1081 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0144 support0144 1 transition1074 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · change (∑ d, mass (advance d ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) ≤ 1 / 4
    have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0144 support0144 1 transition1075 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    simp_rw [h]
    apply checked_smallMass
    norm_num [support0144, supportNumbers0144, fromList]

theorem nodeTailFacts1081 : NodeTailFacts 1081 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0144 support0144 1 transition1076 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0947 1 transition0643 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0947 support0948 1 finish0256 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0144 support0144 1 transition1076 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 5) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0949 1 transition0644 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0949 support0908 1 finish0257 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0144 support0144 1 transition1077 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0144 support0144 1 transition1078 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0144 support1185 1 finish0394 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0144 support0144 1 transition1077 (1 / (2 : ℚ) ^ 5) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0144 support0314 1 transition1079 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0314 support0229 1 finish0395 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0144 (1 / (2 : ℚ) ^ 5) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1082 : NodeFacts 1082 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0397 support0444 1 transition2704 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0397 support0445 1 transition2705 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1082 : NodeTailFacts 1082 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0397 support0444 1 transition2706 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0444 support1707 1 transition2707 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1707 support1708 1 finish0664 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0397 support0444 1 transition2706 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0444 support1709 1 transition2708 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1709 support0613 1 finish0665 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0397 support1710 1 transition2709 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1710 support0957 1 transition2710 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0957 support0958 1 finish0262 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0397 support1710 1 transition2709 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1710 support0959 1 transition2711 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0959 support0527 1 finish0263 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0397 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1083 : NodeFacts 1083 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0399 support0315 1 transition2716 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0399 support0398 1 transition2717 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1083 : NodeTailFacts 1083 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0399 support0315 1 transition2718 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0315 support1411 1 transition1631 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1411 support1412 1 finish0516 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0399 support0315 1 transition2718 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0315 support1413 1 transition1632 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1413 support0613 1 finish0517 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0399 support1593 1 transition2719 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1593 support0524 1 transition2222 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0524 support0525 1 finish0022 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0399 support1593 1 transition2719 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1593 support0526 1 transition2223 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0526 support0527 1 finish0023 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0399 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1084 : NodeFacts 1084 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0400 support0042 2 transition2720 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0400 support0043 2 transition2721 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1084 : NodeTailFacts 1084 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0400 support0042 2 transition2722 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0042 support0613 1 transition0151 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0613 support0562 1 finish0070 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0400 support0042 2 transition2722 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0042 support0614 1 transition0152 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0614 support0613 2 finish0071 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0400 support0615 2 transition2723 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0615 support0616 1 transition0154 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0400 support0615 2 transition2723 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0615 support0618 1 transition0155 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0400 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1085 : NodeFacts 1085 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0148 support0229 1 transition1102 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0148 support0230 1 transition1103 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1085 : NodeTailFacts 1085 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0148 support0229 1 transition1104 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0229 support1193 1 transition1105 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1193 support1194 1 finish0400 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0148 support0229 1 transition1104 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 6) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0229 support1195 1 transition1106 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1195 support0229 1 finish0401 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0148 support1196 1 transition1107 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1196 support1197 1 transition1108 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support1197 support1198 1 finish0402 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0148 support1196 1 transition1107 (1 / (2 : ℚ) ^ 6) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1196 support1199 1 transition1109 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support1199 support0954 2 finish0403 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0148 (1 / (2 : ℚ) ^ 6) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1086 : NodeFacts 1086 := by
  intro c
  cases c
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0149 support0084 1 transition1110 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t
  · constructor
    · rfl
    · intro d
      funext t
      have h := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0149 support0085 1 transition1111 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
      exact congrFun (h d) t

theorem nodeTailFacts1086 : NodeTailFacts 1086 := by
  intro pen last
  cases pen <;> cases last
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0149 support0084 1 transition1112 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0084 support0148 1 transition0345 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0148 support0679 1 finish0152 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0149 support0084 1 transition1112 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0084 support0149 1 transition0346 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0149 support0148 2 finish0153 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0149 support0757 1 transition1113 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0757 support0616 2 transition0348 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨false, bits4 4⟩ support0616 support0617 1 finish0072 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨false, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k
  · intro d k
    have h1 := fun d => funext (checked_transition ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0149 support0757 1 transition1113 (1 / (2 : ℚ) ^ 7) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h2 := fun d => funext (checked_transition ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0757 support0618 2 transition0349 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 8) (by norm_num [siteWeight]) d)
    have h3 := checked_finish ⟨true, bits4 4⟩ support0618 support0527 2 finish0073 (1 / (2 : ℚ) ^ 8) (1 / (2 : ℚ) ^ 7) (by norm_num)
    change finish d ⟨true, bits4 4⟩ (advance d ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (advance d ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (decode support0149 (1 / (2 : ℚ) ^ 7) d))) k = _
    simp_rw [h1, h2]
    exact h3 d k

theorem nodeFacts1087 : NodeFacts 1087 := by
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

theorem nodeTailFacts1087 : NodeTailFacts 1087 := by
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


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
