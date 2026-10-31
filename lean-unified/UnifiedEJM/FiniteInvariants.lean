import UnifiedEJM.FourQubit
noncomputable section
open scoped BigOperators Matrix
open Complex
namespace UnifiedEJM.FiniteInvariants
theorem purity_eq_sum (A : Mat) : purity A =
    ∑ i, ∑ j, (∑ k, A i k * star (A j k)) * (∑ l, A j l * star (A i l)) := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- 三个真正二体偏迹直接求出的全参数Laurent恒等式。 -/
theorem raw_purity_sum (x : ℂ) (hu : x * star x = 1) :
    sumPurity (numerator159 x) =
    2 * (6*x^16 - 3*x^14 + 74*x^12 + 48*x^10 + 698*x^8 +
      48*x^6 + 74*x^4 - 3*x^2 + 6) / x^8 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hu
  have hs : (starRingEnd ℂ) x = x⁻¹ := star_eq_inv x hu
  simp only [sumPurity, purity_eq_sum]
  simp [reshape12, reshape13, reshape14,
    numerator159, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    star_add, star_sub, star_mul, star_pow, star_inv₀, hs, Complex.star_def]
  field_simp [hx]
  ring_nf
  simp [Complex.I_sq,Complex.I_pow_three,Complex.I_pow_four]
  ring

end UnifiedEJM.FiniteInvariants




