import UnifiedEJM.PhysicsSparseCertificate

open OddEJM
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer.SparseCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- 首站B的所有d参数；k=p=q=0。 -/
def initialBSupport : Support :=
  fromList [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

/-- 首站A包含v₁=0和1，每个元素的权重为1/2。 -/
def initialASupport : Support :=
  fromList [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
    576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591]

theorem initialB_checked : ∀ d t,
    initial ⟨false, firstWord⟩ t = decode initialBSupport 1 d t := by
  decide +kernel

theorem initialA_checked : ∀ d t,
    initial ⟨true, firstWord⟩ t = decode initialASupport (1 / 2) d t := by
  decide +kernel

end UnifiedEJM.WeightedTransfer.SparseCertificate
