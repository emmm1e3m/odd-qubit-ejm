import UnifiedEJM.GraphBackground
import UnifiedEJM.PhysicsPurityPerturbation
import UnifiedEJM.Projective

noncomputable section
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

/-- 两条证明链使用的是同一个归一化背景，仅将整体相位放在线性电路内外。 -/
theorem backgroundSeed_eq_physicalBackground (n : ℕ) (t : ℝ) :
    PurityTail.backgroundSeed n t = physicalBackground n (anglePhase t) := by
  unfold PurityTail.backgroundSeed physicalBackground
  rw [show (fun z : Bits n => normFactor n * (-I * background (anglePhase t) z)) =
    (fun z => (-I) * (normFactor n * background (anglePhase t) z)) by
      funext z
      ring]
  exact Physical.circuit_scale _ _

/-- 背景的真实物理纯度界接入已核验的全态扰动估计。 -/
theorem actual_cut_lt_half_of_background {n : ℕ} (hn : 10 ≤ n) (t : ℝ)
    (S : Finset (Fin n))
    (hbg : (Multipartite.cutPurity S (physicalBackground n (anglePhase t))).re ≤ 3/8) :
    (Multipartite.cutPurity S (UnifiedEJM.seed n t)).re < 1/2 := by
  apply PurityTail.actual_cutPurity_lt_half hn t S
  simpa only [backgroundSeed_eq_physicalBackground] using hbg

end UnifiedEJM.GraphBackground
