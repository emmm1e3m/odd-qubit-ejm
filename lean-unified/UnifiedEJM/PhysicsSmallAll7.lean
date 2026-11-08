import UnifiedEJM.PhysicsSmallCut7M96
import UnifiedEJM.PhysicsSmallBatch7B0
import UnifiedEJM.PhysicsSmallBatch7B4
import UnifiedEJM.PhysicsSmallBatch7B8
import UnifiedEJM.PhysicsSmallBatch7B12
import UnifiedEJM.PhysicsSmallBatch7B16
import UnifiedEJM.PhysicsSmallBatch7B20
import UnifiedEJM.PhysicsSmallBatch7B24
import UnifiedEJM.PhysicsSmallBatch7B28
import UnifiedEJM.PhysicsSmallBatch7B32
import UnifiedEJM.PhysicsSmallBatch7B36
import UnifiedEJM.PhysicsSmallBatch7B40
import UnifiedEJM.PhysicsSmallBatch7B44
import UnifiedEJM.PhysicsSmallBatch7B48
import UnifiedEJM.PhysicsSmallBatch7B52
open OddEJM Complex
open scoped BigOperators Matrix
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def smallCuts7 (i : Fin 56) : Finset (Fin 7) := (if i.val < 28 then (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then small7C96Set else (if i.val < 2 then small7C80Set else small7C72Set)) else (if i.val < 5 then (if i.val < 4 then small7C68Set else small7C66Set) else (if i.val < 6 then small7C65Set else small7C48Set))) else (if i.val < 10 then (if i.val < 8 then small7C40Set else (if i.val < 9 then small7C36Set else small7C34Set)) else (if i.val < 12 then (if i.val < 11 then small7C33Set else small7C24Set) else (if i.val < 13 then small7C20Set else small7C18Set)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then small7C17Set else (if i.val < 16 then small7C12Set else small7C10Set)) else (if i.val < 19 then (if i.val < 18 then small7C9Set else small7C6Set) else (if i.val < 20 then small7C5Set else small7C3Set))) else (if i.val < 24 then (if i.val < 22 then small7C112Set else (if i.val < 23 then small7C104Set else small7C100Set)) else (if i.val < 26 then (if i.val < 25 then small7C98Set else small7C97Set) else (if i.val < 27 then small7C88Set else small7C84Set))))) else (if i.val < 42 then (if i.val < 35 then (if i.val < 31 then (if i.val < 29 then small7C82Set else (if i.val < 30 then small7C81Set else small7C76Set)) else (if i.val < 33 then (if i.val < 32 then small7C74Set else small7C73Set) else (if i.val < 34 then small7C70Set else small7C69Set))) else (if i.val < 38 then (if i.val < 36 then small7C67Set else (if i.val < 37 then small7C56Set else small7C52Set)) else (if i.val < 40 then (if i.val < 39 then small7C50Set else small7C49Set) else (if i.val < 41 then small7C44Set else small7C42Set)))) else (if i.val < 49 then (if i.val < 45 then (if i.val < 43 then small7C41Set else (if i.val < 44 then small7C38Set else small7C37Set)) else (if i.val < 47 then (if i.val < 46 then small7C35Set else small7C28Set) else (if i.val < 48 then small7C26Set else small7C25Set))) else (if i.val < 52 then (if i.val < 50 then small7C22Set else (if i.val < 51 then small7C21Set else small7C19Set)) else (if i.val < 54 then (if i.val < 53 then small7C14Set else small7C13Set) else (if i.val < 55 then small7C11Set else small7C7Set))))))

theorem smallCuts7_cover : ∀ S : Finset (Fin 7),
    S ∈ Multipartite.cuts 7 → ¬PhysicsEntanglement.SingleCut S →
    ∃ i : Fin 56, S = smallCuts7 i ∨ Sᶜ = smallCuts7 i := by
  unfold PhysicsEntanglement.SingleCut
  decide +kernel

theorem smallCuts7_bound (t : ℝ) (i : Fin 56) :
    (Multipartite.cutPurity (smallCuts7 i) (UnifiedEJM.seed 7 t)).re < 1/2 := by
  fin_cases i
  · exact small7C96_lt_half t
  · exact small7C80_lt_half t
  · exact small7C72_lt_half t
  · exact small7C68_lt_half t
  · exact small7C66_lt_half t
  · exact small7C65_lt_half t
  · exact small7C48_lt_half t
  · exact small7C40_lt_half t
  · exact small7C36_lt_half t
  · exact small7C34_lt_half t
  · exact small7C33_lt_half t
  · exact small7C24_lt_half t
  · exact small7C20_lt_half t
  · exact small7C18_lt_half t
  · exact small7C17_lt_half t
  · exact small7C12_lt_half t
  · exact small7C10_lt_half t
  · exact small7C9_lt_half t
  · exact small7C6_lt_half t
  · exact small7C5_lt_half t
  · exact small7C3_lt_half t
  · exact small7C112_lt_half t
  · exact small7C104_lt_half t
  · exact small7C100_lt_half t
  · exact small7C98_lt_half t
  · exact small7C97_lt_half t
  · exact small7C88_lt_half t
  · exact small7C84_lt_half t
  · exact small7C82_lt_half t
  · exact small7C81_lt_half t
  · exact small7C76_lt_half t
  · exact small7C74_lt_half t
  · exact small7C73_lt_half t
  · exact small7C70_lt_half t
  · exact small7C69_lt_half t
  · exact small7C67_lt_half t
  · exact small7C56_lt_half t
  · exact small7C52_lt_half t
  · exact small7C50_lt_half t
  · exact small7C49_lt_half t
  · exact small7C44_lt_half t
  · exact small7C42_lt_half t
  · exact small7C41_lt_half t
  · exact small7C38_lt_half t
  · exact small7C37_lt_half t
  · exact small7C35_lt_half t
  · exact small7C28_lt_half t
  · exact small7C26_lt_half t
  · exact small7C25_lt_half t
  · exact small7C22_lt_half t
  · exact small7C21_lt_half t
  · exact small7C19_lt_half t
  · exact small7C14_lt_half t
  · exact small7C13_lt_half t
  · exact small7C11_lt_half t
  · exact small7C7_lt_half t

/-- 任意实际非单体二分割的全参数严格界，包括补系统表示。 -/
theorem small7_nonSingleCut_lt_half (t : ℝ) (S : Finset (Fin 7))
    (hS : S ∈ Multipartite.cuts 7) (hns : ¬PhysicsEntanglement.SingleCut S) :
    (Multipartite.cutPurity S (UnifiedEJM.seed 7 t)).re < 1/2 := by
  obtain ⟨i, hi⟩ := smallCuts7_cover S hS hns
  rcases hi with hi | hi
  · rw [hi]
    exact smallCuts7_bound t i
  · rw [← Multipartite.cutPurity_compl S, hi]
    exact smallCuts7_bound t i

end UnifiedEJM.PhysicsFinite
