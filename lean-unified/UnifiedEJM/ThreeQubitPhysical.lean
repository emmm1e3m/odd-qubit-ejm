import UnifiedEJM.ThreeQubit
import UnifiedEJM.ThreeQubitCircuit
import OddEJM.Density

noncomputable section
namespace UnifiedEJM.ThreeQubit
open OddEJM

open scoped Topology
/-- 原门、原指定基点及全部七个相位中的真正局部刚性。 -/
theorem physical_regularity_isolated :
    ∀ᶠ θ in nhds (0 : Space),
      (∀ p, (physicalExpectation θ p).re ^ 2 =
        (physicalExpectation θ 0).re ^ 2) → θ = 0 := by
  simpa only [← expectation_eq_physical] using regularity_isolated


/-- 规范相位原点逐振幅恢复指定基本对称相位种子。 -/
theorem physicalSeed_zero : physicalSeed 0 =
    circuit (fun z => normFactor 3 * originalDiagonal z) := by
  simp [physicalSeed, physicalDiagonal, phase, anglePhase]

/-- 与工程通用物理Pauli接口一致的分量次序。 -/
def standardComponents (θ : Space) : Fin 9 → ℂ :=
  ![localX (physicalSeed θ) 0, localY (physicalSeed θ) 0, localZ (physicalSeed θ) 0,
    localX (physicalSeed θ) 1, localY (physicalSeed θ) 1, localZ (physicalSeed θ) 1,
    localX (physicalSeed θ) 2, -localY (physicalSeed θ) 2, localZ (physicalSeed θ) 2]
lemma physical_components (θ : Space) : physicalExpectation θ = standardComponents θ := by
  have h0 : unitBit 3 0 = ![1,0,0] := by decide
  have h1 : unitBit 3 1 = ![0,1,0] := by decide
  have h2 : unitBit 3 2 = ![0,0,1] := by decide
  have hz : (0 : Bits 3) = ![0,0,0] := by decide
  have hn (ψ : Vec 3) (a b : Bits 3) :
      pauliExpectation ψ a b (-Complex.I) = -pauliExpectation ψ a b Complex.I := by
    simp [pauliExpectation, Finset.sum_neg_distrib]
  funext p
  fin_cases p <;> simp [physicalExpectation, standardComponents,
    localX, localY, localZ, opA, opB, opC, h0, h1, h2, hz, hn]

/-- 标准物理X/Y/Z分量下的最终三比特局部刚性。 -/
theorem canonical_three_qubit_rigidity :
    ∀ᶠ θ in nhds (0 : Space),
      (∀ p, (standardComponents θ p).re ^ 2 =
        (standardComponents θ 0).re ^ 2) → θ = 0 := by
  simpa only [physical_components] using physical_regularity_isolated

end UnifiedEJM.ThreeQubit
