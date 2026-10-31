import UnifiedEJM.ThreeQubitPhysical
import UnifiedEJM.Regularity

noncomputable section
open scoped Topology
namespace UnifiedEJM.ThreeQubit
open OddEJM

lemma geometric_component_squares (θ : Space) {r : ℝ}
    (h : Regularity.GeometricRegular (physicalDiagonal θ) r) (p : Fin 9) :
    (standardComponents θ p).re ^ 2 = r ^ 2 / 3 := by
  have hs (j : Fin 3) := Regularity.geometric_seed_squares (by decide : 2 ≤ 3) h j
  have hs' (j : Fin 3) :
      (localX (physicalSeed θ) j).re ^ 2 = r ^ 2 / 3 ∧
      (localY (physicalSeed θ) j).re ^ 2 = r ^ 2 / 3 ∧
      (localZ (physicalSeed θ) j).re ^ 2 = r ^ 2 / 3 := hs j
  fin_cases p
  · simpa [standardComponents] using (hs' 0).1
  · simpa [standardComponents] using (hs' 0).2.1
  · simpa [standardComponents] using (hs' 0).2.2
  · simpa [standardComponents] using (hs' 1).1
  · simpa [standardComponents] using (hs' 1).2.1
  · simpa [standardComponents] using (hs' 1).2.2
  · simpa [standardComponents] using (hs' 2).1
  · simpa [standardComponents] using (hs' 2).2.1
  · simpa [standardComponents] using (hs' 2).2.2

/-- 允许局部四面体旋转和结果重标号的完整测量几何仍在指定点局部孤立。 -/
theorem geometric_three_qubit_rigidity :
    ∀ᶠ θ in nhds (0 : Space),
      (∃ r, Regularity.GeometricRegular (physicalDiagonal θ) r) → θ = 0 := by
  filter_upwards [canonical_three_qubit_rigidity] with θ hθ
  rintro ⟨r, hr⟩
  apply hθ
  intro p
  exact (geometric_component_squares θ hr p).trans
    (geometric_component_squares θ hr 0).symm

end UnifiedEJM.ThreeQubit
