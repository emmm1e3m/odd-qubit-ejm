import UnifiedEJM.PhysicsSmallBatch8B0
import UnifiedEJM.PhysicsSmallBatch8B4
import UnifiedEJM.PhysicsSmallBatch8B8
import UnifiedEJM.PhysicsSmallBatch8B12
import UnifiedEJM.PhysicsSmallBatch8B16
import UnifiedEJM.PhysicsSmallBatch8B20
import UnifiedEJM.PhysicsSmallBatch8B24
import UnifiedEJM.PhysicsSmallBatch8B28
import UnifiedEJM.PhysicsSmallBatch8B32
import UnifiedEJM.PhysicsSmallBatch8B36
import UnifiedEJM.PhysicsSmallBatch8B40
import UnifiedEJM.PhysicsSmallBatch8B44
import UnifiedEJM.PhysicsSmallBatch8B48
import UnifiedEJM.PhysicsSmallBatch8B52
import UnifiedEJM.PhysicsSmallBatch8B56
import UnifiedEJM.PhysicsSmallBatch8B60
import UnifiedEJM.PhysicsSmallBatch8B64
import UnifiedEJM.PhysicsSmallBatch8B68
import UnifiedEJM.PhysicsSmallBatch8B72
import UnifiedEJM.PhysicsSmallBatch8B76
import UnifiedEJM.PhysicsSmallBatch8B80
import UnifiedEJM.PhysicsSmallBatch8B84
import UnifiedEJM.PhysicsSmallBatch8B88
import UnifiedEJM.PhysicsSmallBatch8B92
import UnifiedEJM.PhysicsSmallBatch8B96
import UnifiedEJM.PhysicsSmallBatch8B100
import UnifiedEJM.PhysicsSmallBatch8B104
import UnifiedEJM.PhysicsSmallBatch8B108
import UnifiedEJM.PhysicsSmallBatch8B112
import UnifiedEJM.PhysicsSmallBatch8B116
open OddEJM Complex
open scoped BigOperators Matrix
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def smallCuts8 (i : Fin 119) : Finset (Fin 8) := (if i.val < 59 then (if i.val < 29 then (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then small8C192Set else (if i.val < 2 then small8C160Set else small8C144Set)) else (if i.val < 5 then (if i.val < 4 then small8C136Set else small8C132Set) else (if i.val < 6 then small8C130Set else small8C129Set))) else (if i.val < 10 then (if i.val < 8 then small8C96Set else (if i.val < 9 then small8C80Set else small8C72Set)) else (if i.val < 12 then (if i.val < 11 then small8C68Set else small8C66Set) else (if i.val < 13 then small8C65Set else small8C48Set)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then small8C40Set else (if i.val < 16 then small8C36Set else small8C34Set)) else (if i.val < 19 then (if i.val < 18 then small8C33Set else small8C24Set) else (if i.val < 20 then small8C20Set else small8C18Set))) else (if i.val < 25 then (if i.val < 23 then (if i.val < 22 then small8C17Set else small8C12Set) else (if i.val < 24 then small8C10Set else small8C9Set)) else (if i.val < 27 then (if i.val < 26 then small8C6Set else small8C5Set) else (if i.val < 28 then small8C3Set else small8C224Set))))) else (if i.val < 44 then (if i.val < 36 then (if i.val < 32 then (if i.val < 30 then small8C208Set else (if i.val < 31 then small8C200Set else small8C196Set)) else (if i.val < 34 then (if i.val < 33 then small8C194Set else small8C193Set) else (if i.val < 35 then small8C176Set else small8C168Set))) else (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then small8C164Set else small8C162Set) else (if i.val < 39 then small8C161Set else small8C152Set)) else (if i.val < 42 then (if i.val < 41 then small8C148Set else small8C146Set) else (if i.val < 43 then small8C145Set else small8C140Set)))) else (if i.val < 51 then (if i.val < 47 then (if i.val < 45 then small8C138Set else (if i.val < 46 then small8C137Set else small8C134Set)) else (if i.val < 49 then (if i.val < 48 then small8C133Set else small8C131Set) else (if i.val < 50 then small8C112Set else small8C104Set))) else (if i.val < 55 then (if i.val < 53 then (if i.val < 52 then small8C100Set else small8C98Set) else (if i.val < 54 then small8C97Set else small8C88Set)) else (if i.val < 57 then (if i.val < 56 then small8C84Set else small8C82Set) else (if i.val < 58 then small8C81Set else small8C76Set)))))) else (if i.val < 89 then (if i.val < 74 then (if i.val < 66 then (if i.val < 62 then (if i.val < 60 then small8C74Set else (if i.val < 61 then small8C73Set else small8C70Set)) else (if i.val < 64 then (if i.val < 63 then small8C69Set else small8C67Set) else (if i.val < 65 then small8C56Set else small8C52Set))) else (if i.val < 70 then (if i.val < 68 then (if i.val < 67 then small8C50Set else small8C49Set) else (if i.val < 69 then small8C44Set else small8C42Set)) else (if i.val < 72 then (if i.val < 71 then small8C41Set else small8C38Set) else (if i.val < 73 then small8C37Set else small8C35Set)))) else (if i.val < 81 then (if i.val < 77 then (if i.val < 75 then small8C28Set else (if i.val < 76 then small8C26Set else small8C25Set)) else (if i.val < 79 then (if i.val < 78 then small8C22Set else small8C21Set) else (if i.val < 80 then small8C19Set else small8C14Set))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then small8C13Set else small8C11Set) else (if i.val < 84 then small8C7Set else small8C240Set)) else (if i.val < 87 then (if i.val < 86 then small8C232Set else small8C228Set) else (if i.val < 88 then small8C226Set else small8C225Set))))) else (if i.val < 104 then (if i.val < 96 then (if i.val < 92 then (if i.val < 90 then small8C216Set else (if i.val < 91 then small8C212Set else small8C210Set)) else (if i.val < 94 then (if i.val < 93 then small8C209Set else small8C204Set) else (if i.val < 95 then small8C202Set else small8C201Set))) else (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then small8C198Set else small8C197Set) else (if i.val < 99 then small8C195Set else small8C184Set)) else (if i.val < 102 then (if i.val < 101 then small8C180Set else small8C178Set) else (if i.val < 103 then small8C177Set else small8C172Set)))) else (if i.val < 111 then (if i.val < 107 then (if i.val < 105 then small8C170Set else (if i.val < 106 then small8C169Set else small8C166Set)) else (if i.val < 109 then (if i.val < 108 then small8C165Set else small8C163Set) else (if i.val < 110 then small8C156Set else small8C154Set))) else (if i.val < 115 then (if i.val < 113 then (if i.val < 112 then small8C153Set else small8C150Set) else (if i.val < 114 then small8C149Set else small8C147Set)) else (if i.val < 117 then (if i.val < 116 then small8C142Set else small8C141Set) else (if i.val < 118 then small8C139Set else small8C135Set)))))))

theorem smallCuts8_cover : ∀ S : Finset (Fin 8),
    S ∈ Multipartite.cuts 8 → ¬PhysicsEntanglement.SingleCut S →
    ∃ i : Fin 119, S = smallCuts8 i ∨ Sᶜ = smallCuts8 i := by
  unfold PhysicsEntanglement.SingleCut
  decide +kernel

theorem smallCuts8_bound (t : ℝ) (i : Fin 119) :
    (Multipartite.cutPurity (smallCuts8 i) (UnifiedEJM.seed 8 t)).re < 1/2 := by
  fin_cases i
  · exact small8C192_lt_half t
  · exact small8C160_lt_half t
  · exact small8C144_lt_half t
  · exact small8C136_lt_half t
  · exact small8C132_lt_half t
  · exact small8C130_lt_half t
  · exact small8C129_lt_half t
  · exact small8C96_lt_half t
  · exact small8C80_lt_half t
  · exact small8C72_lt_half t
  · exact small8C68_lt_half t
  · exact small8C66_lt_half t
  · exact small8C65_lt_half t
  · exact small8C48_lt_half t
  · exact small8C40_lt_half t
  · exact small8C36_lt_half t
  · exact small8C34_lt_half t
  · exact small8C33_lt_half t
  · exact small8C24_lt_half t
  · exact small8C20_lt_half t
  · exact small8C18_lt_half t
  · exact small8C17_lt_half t
  · exact small8C12_lt_half t
  · exact small8C10_lt_half t
  · exact small8C9_lt_half t
  · exact small8C6_lt_half t
  · exact small8C5_lt_half t
  · exact small8C3_lt_half t
  · exact small8C224_lt_half t
  · exact small8C208_lt_half t
  · exact small8C200_lt_half t
  · exact small8C196_lt_half t
  · exact small8C194_lt_half t
  · exact small8C193_lt_half t
  · exact small8C176_lt_half t
  · exact small8C168_lt_half t
  · exact small8C164_lt_half t
  · exact small8C162_lt_half t
  · exact small8C161_lt_half t
  · exact small8C152_lt_half t
  · exact small8C148_lt_half t
  · exact small8C146_lt_half t
  · exact small8C145_lt_half t
  · exact small8C140_lt_half t
  · exact small8C138_lt_half t
  · exact small8C137_lt_half t
  · exact small8C134_lt_half t
  · exact small8C133_lt_half t
  · exact small8C131_lt_half t
  · exact small8C112_lt_half t
  · exact small8C104_lt_half t
  · exact small8C100_lt_half t
  · exact small8C98_lt_half t
  · exact small8C97_lt_half t
  · exact small8C88_lt_half t
  · exact small8C84_lt_half t
  · exact small8C82_lt_half t
  · exact small8C81_lt_half t
  · exact small8C76_lt_half t
  · exact small8C74_lt_half t
  · exact small8C73_lt_half t
  · exact small8C70_lt_half t
  · exact small8C69_lt_half t
  · exact small8C67_lt_half t
  · exact small8C56_lt_half t
  · exact small8C52_lt_half t
  · exact small8C50_lt_half t
  · exact small8C49_lt_half t
  · exact small8C44_lt_half t
  · exact small8C42_lt_half t
  · exact small8C41_lt_half t
  · exact small8C38_lt_half t
  · exact small8C37_lt_half t
  · exact small8C35_lt_half t
  · exact small8C28_lt_half t
  · exact small8C26_lt_half t
  · exact small8C25_lt_half t
  · exact small8C22_lt_half t
  · exact small8C21_lt_half t
  · exact small8C19_lt_half t
  · exact small8C14_lt_half t
  · exact small8C13_lt_half t
  · exact small8C11_lt_half t
  · exact small8C7_lt_half t
  · exact small8C240_lt_half t
  · exact small8C232_lt_half t
  · exact small8C228_lt_half t
  · exact small8C226_lt_half t
  · exact small8C225_lt_half t
  · exact small8C216_lt_half t
  · exact small8C212_lt_half t
  · exact small8C210_lt_half t
  · exact small8C209_lt_half t
  · exact small8C204_lt_half t
  · exact small8C202_lt_half t
  · exact small8C201_lt_half t
  · exact small8C198_lt_half t
  · exact small8C197_lt_half t
  · exact small8C195_lt_half t
  · exact small8C184_lt_half t
  · exact small8C180_lt_half t
  · exact small8C178_lt_half t
  · exact small8C177_lt_half t
  · exact small8C172_lt_half t
  · exact small8C170_lt_half t
  · exact small8C169_lt_half t
  · exact small8C166_lt_half t
  · exact small8C165_lt_half t
  · exact small8C163_lt_half t
  · exact small8C156_lt_half t
  · exact small8C154_lt_half t
  · exact small8C153_lt_half t
  · exact small8C150_lt_half t
  · exact small8C149_lt_half t
  · exact small8C147_lt_half t
  · exact small8C142_lt_half t
  · exact small8C141_lt_half t
  · exact small8C139_lt_half t
  · exact small8C135_lt_half t

/-- 任意实际非单体二分割的全参数严格界，包括补系统表示。 -/
theorem small8_nonSingleCut_lt_half (t : ℝ) (S : Finset (Fin 8))
    (hS : S ∈ Multipartite.cuts 8) (hns : ¬PhysicsEntanglement.SingleCut S) :
    (Multipartite.cutPurity S (UnifiedEJM.seed 8 t)).re < 1/2 := by
  obtain ⟨i, hi⟩ := smallCuts8_cover S hS hns
  rcases hi with hi | hi
  · rw [hi]
    exact smallCuts8_bound t i
  · rw [← Multipartite.cutPurity_compl S, hi]
    exact smallCuts8_bound t i

end UnifiedEJM.PhysicsFinite
