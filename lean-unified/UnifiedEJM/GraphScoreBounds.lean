import UnifiedEJM.GraphNormalization
import UnifiedEJM.PhysicsCorrelationBound

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

/-- 真实物理系数的每个有限签名分数都介于零与一之间。 -/
theorem physical_score_bounds (n : ℕ) (u : ℂ) (hu : ‖u‖=1) (d k : Bits 4) :
    0 ≤ Complex.normSq (codeCorrelation (physicalCoefficients n u) d k) ∧
      Complex.normSq (codeCorrelation (physicalCoefficients n u) d k) ≤ 1 := by
  constructor
  · exact Complex.normSq_nonneg _
  · exact WeightedTransfer.codeCorrelation_normSq_le_one
      (physicalCoefficients n u) (physicalCoefficients_normalized n u hu) d k

theorem physical_angle_score_bounds (n : ℕ) (t : ℝ) (d k : Bits 4) :
    0 ≤ Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k) ∧
      Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k) ≤ 1 :=
  physical_score_bounds n _ (UnifiedEJM.anglePhase_norm t) d k

end UnifiedEJM.GraphBackground
