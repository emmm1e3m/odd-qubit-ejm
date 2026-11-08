import UnifiedEJM.PhysicsSmallLayout
import UnifiedEJM.PhysicsEntanglement

open OddEJM Complex
open scoped BigOperators Matrix
namespace UnifiedEJM.PhysicsFinite
open PhysicsEntanglement
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- 三角多项式的整数L1分子；最终有限检查只需这个整数严格不等式。 -/
def l1Numerator (q : Fin 5 → G) : ℤ :=
  realCoeffs q 0 + |realCoeffs q 1| + |realCoeffs q 2| +
    |realCoeffs q 3| + |realCoeffs q 4|

theorem trig_le_l1 (q : Fin 5 → G) (t : ℝ) :
    trigEval (realCoeffs q) t ≤ (l1Numerator q : ℝ) := by
  simpa only [l1Numerator, Int.cast_add, Int.cast_abs] using
    trigEval_le (realCoeffs q) t

/-- 整数系数验证严格留有余量后，所有实参数同时满足纯度严格界。 -/
theorem laurent_lt_half (d : ℕ) (hd : 0 < d) (q : Fin 5 → G)
    (hq : 2 * l1Numerator q < (d : ℤ)) (t : ℝ) :
    ((d : ℂ)⁻¹ * laurentEval q (anglePhase t)).re < 1/2 := by
  rw [show (d : ℂ) = ((d : ℝ) : ℂ) by norm_cast, scaled_laurent_re]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (2 : ℝ) * (l1Numerator q : ℝ) < d := by exact_mod_cast hq
  have hcancel : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hdR)
  have hmul := mul_lt_mul_of_pos_left hqR (inv_pos.mpr hdR)
  have ht := mul_le_mul_of_nonneg_left (trig_le_l1 q t) (le_of_lt (inv_pos.mpr hdR))
  rw [div_eq_mul_inv]
  nlinarith

/-- 原门种子的矩阵系数证书与一个整数界足以推出全部实参数的严格界。 -/
theorem cut_lt_half_of_layout {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Finset (Fin n)) (e : ι × κ ≃ Bits n) (A B : ι → κ → G)
    (hmix : ∀ a c b d, splice S (e (a,b)) (e (c,d)) = e (a,d))
    (hA : ∀ a b, coeffA UnifiedEJM.q (e (a,b)) = A a b)
    (hB : ∀ a b, coeffB UnifiedEJM.q (e (a,b)) = B a b)
    (R : ι → ι → Fin 3 → G) (hR : reducedCoeffs A B = R)
    (q : Fin 5 → G) (htrace : traceCoeffs R = q)
    (d : ℕ) (hd : 0 < d)
    (hnorm : (((2 : ℂ)^(n+1))⁻¹)^2 = (d : ℂ)⁻¹)
    (hbound : 2 * l1Numerator q < (d : ℤ)) (t : ℝ) :
    (Multipartite.cutPurity S (UnifiedEJM.seed n t)).re < 1/2 := by
  have hu : anglePhase t * star (anglePhase t) = 1 := EvenFamily.angle_unit t
  have h := cut_laurent_layout S e A B hmix hA hB (anglePhase t) hu
  rw [hR, htrace, hnorm] at h
  change Multipartite.cutPurity S (UnifiedEJM.seed n t) = _ at h
  rw [h]
  exact laurent_lt_half d hd q hbound t

end UnifiedEJM.PhysicsFinite

