import UnifiedEJM.PhysicalInequivalence
import UnifiedEJM.LinePhase
import UnifiedEJM.MeasurementInvariants
import OddEJM.LocalExpectation

noncomputable section
namespace UnifiedEJM.FiniteInvariants
open UnifiedEJM.BipartiteInvariant
open OddEJM

/-- f159 的真实相位函数，以论文给出的16项f,k表表示。 -/
def diagonal159 (x : ℂ) (z : Bits 4) : ℂ := phase159 x (encode4 z)

theorem seed159_eq_state (x : ℂ) : seedState (diagonal159 x) = state159 x := by
  funext k
  exact (state159_actual_seed x k).symm

theorem seedBase_eq_state : seedState (@originalDiagonal 4) = stateBase := by
  funext k
  exact (stateBase_actual_seed k).symm

/-- 实际完整测量在LU、任意比特置换、任意结果重标及列相位下不等价。 -/
theorem measurements159_not_equivalent (x : ℂ) (hu : x * star x = 1) :
    ¬ EquivalentMeasurements (diagonal159 x) (@originalDiagonal 4) := by
  intro heq
  obtain ⟨h2,h1⟩ := equivalent_measurements_invariants _ _ heq
  rw [seed159_eq_state,seedBase_eq_state] at h1 h2
  exact no_matching_actual_invariants x hu ⟨h1,h2⟩

/-- 排除整个实参数相位线，因此包含论文引用的a∈[0,π/3]区间。 -/
theorem real_line159_not_equivalent (a : ℝ) :
    ¬ EquivalentMeasurements (diagonal159 (anglePhase a)) (@originalDiagonal 4) := by
  apply measurements159_not_equivalent
  simpa only [mul_comm] using anglePhase_star_mul a

/-- 实参数相位表确为酉对角门，排除的对象是完整正交测量。 -/
theorem diagonal159_unit (a : ℝ) (z : Bits 4) :
    star (diagonal159 (anglePhase a) z) * diagonal159 (anglePhase a) z = 1 := by
  apply phase159_unit
  simpa only [mul_comm] using anglePhase_star_mul a

theorem line159_measurement_orthonormal (a : ℝ) (k l : Bits 4) :
    inner (Physical.measurement (diagonal159 (anglePhase a)) k)
      (Physical.measurement (diagonal159 (anglePhase a)) l) = if k = l then 1 else 0 := by
  exact Physical.measurement_orthonormal (by decide) _ (diagonal159_unit a) k l

end UnifiedEJM.FiniteInvariants

