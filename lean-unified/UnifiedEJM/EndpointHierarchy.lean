import UnifiedEJM.EndpointDepth
import UnifiedEJM.CliffordDepth
import UnifiedEJM.PhysicsCircuit

noncomputable section
namespace UnifiedEJM.PhaseImplementation
open OddEJM CliffordFoundation PhysicsCircuit

/-- 原稿相位本身的单位复数封装；没有替换或删掉零串相位。 -/
def familyPhase {n : ℕ} (t : ℝ) : Phase n := fun z =>
  ⟨UnifiedEJM.rawPhase (anglePhase t) z, by
    constructor
    · exact UnifiedEJM.rawPhase_star_mul_self _ (anglePhase_norm t) z
    · rw [mul_comm]
      exact UnifiedEJM.rawPhase_star_mul_self _ (anglePhase_norm t) z⟩

/-- 原稿完整测量酉，含原来的CNOT电路和输入Hadamard层。 -/
def familyGate {n : ℕ} (hn : 0 < n) (t : ℝ) : Gate n :=
  measurementGate hn (diagonalGate (familyPhase t))

theorem familyGate_matrix {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (familyGate hn t : Matrix (Bits n) (Bits n) ℂ) =
      fun x k => Physical.measurement (UnifiedEJM.rawPhase (anglePhase t)) k x := by
  exact measurementGate_matrix hn (diagonalGate (familyPhase t)) _ rfl

/-- 每一列就是既有UnifiedEJM.measurement，没有重排或另选基矢相位。 -/
theorem familyGate_original_matrix {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (familyGate hn t : Matrix (Bits n) (Bits n) ℂ) =
      fun x k => UnifiedEJM.measurement n t k x := by
  exact familyGate_matrix hn t

theorem familyPhase_eq_phase4 {n : ℕ} (t : ℝ) (f : DiagonalDifference.Phase4 n)
    (h : ∀ z, UnifiedEJM.rawPhase (anglePhase t) z = root4 (f z)) :
    familyPhase t = phase4 f := by
  funext z
  apply Subtype.ext
  exact h z

theorem familyGate_reference {n : ℕ} (hn : 0 < n) :
    familyGate hn 0 = measurementGate hn (diagonal4 referenceExponent) := by
  unfold familyGate diagonal4
  rw [familyPhase_eq_phase4 0 referenceExponent reference_phase_exponent]

theorem familyGate_plus {n : ℕ} (hn : 0 < n) :
    familyGate hn (Real.pi/2) = measurementGate hn (diagonal4 plusExponent) := by
  unfold familyGate diagonal4
  rw [familyPhase_eq_phase4 (Real.pi/2) plusExponent plus_phase_exponent]

theorem familyGate_minus {n : ℕ} (hn : 0 < n) :
    familyGate hn (-Real.pi/2) = measurementGate hn (diagonal4 minusExponent) := by
  unfold familyGate diagonal4
  rw [familyPhase_eq_phase4 (-Real.pi/2) minusExponent minus_phase_exponent]

/-- 参考完整测量酉位于第n+1层。 -/
theorem reference_measurement_level {n : ℕ} (hn : 5 ≤ n) :
    IsLevel (n+1) (familyGate (by omega : 0 < n) 0) := by
  rw [familyGate_reference, isLevel_measurementGate_iff (by omega) (by omega),
    diagonal4_isLevel_iff (by omega)]
  exact referenceExponent_depth (by omega)

/-- 参考完整测量酉不在第n层，故上述级数精确。 -/
theorem reference_measurement_not_lower {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsLevel n (familyGate (by omega : 0 < n) 0) := by
  rw [familyGate_reference, isLevel_measurementGate_iff (by omega) (by omega),
    diagonal4_isLevel_iff (by omega)]
  exact referenceExponent_not_depth hn

/-- 半径增强端点的完整测量酉位于第n层。 -/
theorem minus_measurement_level {n : ℕ} (hn : 5 ≤ n) :
    IsLevel n (familyGate (by omega : 0 < n) (-Real.pi/2)) := by
  rw [familyGate_minus, isLevel_measurementGate_iff (by omega) (by omega),
    diagonal4_isLevel_iff (by omega)]
  exact minusExponent_depth hn

/-- 半径增强端点不在第n−1层。 -/
theorem minus_measurement_not_lower {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsLevel (n-1) (familyGate (by omega : 0 < n) (-Real.pi/2)) := by
  rw [familyGate_minus, isLevel_measurementGate_iff (by omega) (by omega),
    diagonal4_isLevel_iff (by omega)]
  exact minusExponent_not_depth hn

/-- 零半径端点完整测量酉的层级对任意n≥5均为4。 -/
theorem plus_measurement_level {n : ℕ} (hn : 5 ≤ n) :
    IsLevel 4 (familyGate (by omega : 0 < n) (Real.pi/2)) := by
  rw [familyGate_plus, isLevel_measurementGate_iff (by omega) (by omega),
    diagonal4_isLevel_iff (by omega)]
  exact plusExponent_depth

/-- 零半径端点完整测量酉不在第3层。 -/
theorem plus_measurement_not_lower {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsLevel 3 (familyGate (by omega : 0 < n) (Real.pi/2)) := by
  rw [familyGate_plus, isLevel_measurementGate_iff (by omega) (by omega),
    diagonal4_isLevel_iff (by omega)]
  exact plusExponent_not_depth hn

end UnifiedEJM.PhaseImplementation
