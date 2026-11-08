import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureAggregation

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
open UnifiedEJM.ClosureAggregation
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- 中央一步所需的纯元数据性质，不涉及支撑或分布。 -/
def NodeMetadata (i : Fin 1756) : Prop := ∀ c : Bool,
  match nextNode i c with
  | none => True
  | some j => nodeScan j = scanStep (nodeScan i) c ∧
      (nodeData j).parity = !(nodeData i).parity


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
