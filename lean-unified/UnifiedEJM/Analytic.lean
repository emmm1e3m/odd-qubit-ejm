import UnifiedEJM.Phase
import UnifiedEJM.Continuity

namespace UnifiedEJM
open OddEJM

/-- 新核相位对实参数逐振幅连续。 -/
theorem rawPhase_continuous {n : ℕ} (z : Bits n) :
    Continuous (fun t : ℝ => rawPhase (anglePhase t) z) := by
  have ha : Continuous (fun t : ℝ => anglePhase t) := by
    unfold anglePhase
    fun_prop
  by_cases hz : z = 0
  · simp only [rawPhase, hz, ite_true]
    exact continuous_const
  · simp only [rawPhase, hz, ite_false]
    exact continuous_const.mul (ha.pow _)

theorem measurement_continuous (n : ℕ) (label : Bits n) :
    Continuous (fun t : ℝ => measurement n t label) :=
  Physical.measurement_continuous (fun t => rawPhase (anglePhase t)) rawPhase_continuous label

/-- 连续性在有序测量投影层面成立。 -/
theorem measurement_projector_continuous (n : ℕ) (label : Bits n) :
    Continuous (fun t : ℝ => Physical.projector (measurement n t label)) :=
  Physical.measurement_projector_continuous (fun t => rawPhase (anglePhase t)) rawPhase_continuous label

end UnifiedEJM
