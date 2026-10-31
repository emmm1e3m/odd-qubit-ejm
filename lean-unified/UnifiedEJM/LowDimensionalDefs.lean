import OddEJM.Pauli
import OddEJM.OriginalPhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! 四比特全实相位直线：原门拉回的有限相位和及三阶必要条件。 -/
noncomputable section
namespace UnifiedEJM.LowDimensional
open scoped BigOperators
open Filter Topology
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

abbrev Direction := Fin 16 → ℝ

def flip : Fin 12 → Fin 16 → Fin 16 :=
  ![![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]]

def coeffR : Fin 12 → Fin 16 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, -1, -1], ![0, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 0, -1, 1], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, -1, 1, 1, 1, 1, 0, -1, -1, -1, 1, 1, 1, 1, -1, -1], ![0, 1, -1, 1, 1, -1, 1, 0, -1, 1, -1, 1, 1, -1, 1, -1], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def coeffI : Fin 12 → Fin 16 → ℝ :=
  ![![0, -1, -1, -1, -1, -1, -1, -1, 0, 1, 1, 1, 1, 1, 1, 1], ![0, 1, 1, -1, 1, -1, -1, 1, -1, 0, 1, -1, 1, -1, -1, 1], ![0, 0, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1], ![-1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1], ![0, 1, 0, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1], ![0, -1, 1, 0, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1], ![0, 0, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1]]

def frequency (d : Direction) (p : Fin 12) (z : Fin 16) : ℝ := d z - d (flip p z)

/-- 此函数是实际 signed Pauli 期望的十六倍。 -/
noncomputable def signal (d : Direction) (p : Fin 12) (t : ℝ) : ℝ :=
  ∑ z, (coeffR p z * Real.cos (frequency d p z * t) -
    coeffI p z * Real.sin (frequency d p z * t))

noncomputable def signalD1 (d : Direction) (p : Fin 12) (t : ℝ) : ℝ :=
  ∑ z, (-coeffR p z * frequency d p z * Real.sin (frequency d p z * t) -
    coeffI p z * frequency d p z * Real.cos (frequency d p z * t))

noncomputable def signalD2 (d : Direction) (p : Fin 12) (t : ℝ) : ℝ :=
  ∑ z, (-coeffR p z * frequency d p z ^ 2 * Real.cos (frequency d p z * t) +
    coeffI p z * frequency d p z ^ 2 * Real.sin (frequency d p z * t))

noncomputable def signalD3 (d : Direction) (p : Fin 12) (t : ℝ) : ℝ :=
  ∑ z, (coeffR p z * frequency d p z ^ 3 * Real.sin (frequency d p z * t) +
    coeffI p z * frequency d p z ^ 3 * Real.cos (frequency d p z * t))

def moment1 (d : Direction) (p : Fin 12) : ℝ := ∑ z, -coeffI p z * frequency d p z
def moment2 (d : Direction) (p : Fin 12) : ℝ := ∑ z, -coeffR p z * frequency d p z ^ 2
def moment3 (d : Direction) (p : Fin 12) : ℝ := ∑ z, coeffI p z * frequency d p z ^ 3

def kernelDirection (a b c k : ℝ) : Direction :=
  ![0,a,a,a-c,-a+b-c/2+k,-a+b-c/2+k,c,c,a-c,a,b-c,b,c,c,k,k]


end UnifiedEJM.LowDimensional
