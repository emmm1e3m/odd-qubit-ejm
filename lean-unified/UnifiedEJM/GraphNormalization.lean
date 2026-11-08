import UnifiedEJM.GraphCorrelation
import UnifiedEJM.GraphCoefficients

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

/-- 四位字符合成的内积恒等式，系数不需任何假设。 -/
theorem synthesis_inner (c d : Bits 4 → ℂ) :
    OddEJM.inner (fun x => ∑ h, c h * character h x)
      (fun x => ∑ h, d h * character h x) =
        16 * ∑ h, star (c h) * d h := by
  change (∑ x : Bits 4, star (∑ h, c h * character h x) *
    (∑ h, d h * character h x)) = 16 * ∑ h, star (c h) * d h
  simp only [star_sum, star_mul, character_star, Finset.sum_mul, Finset.mul_sum]
  have hc (h x : Bits 4) : character h x * star (c h) = star (c h) * character h x :=
    mul_comm _ _
  simp_rw [hc]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hrow (h : Bits 4) :
      (∑ x, ∑ l, star (c h) * character h x * (d l * character l x)) =
        16 * (star (c h) * d h) := by
    rw [Finset.sum_comm]
    have hpair (l : Bits 4) :
        (∑ x, star (c h) * character h x * (d l * character l x)) =
          (star (c h) * d l) * (if h=l then (2:ℂ)^4 else 0) := by
      rw [← character_orthogonality]
      simp only [character_star, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    simp_rw [hpair]
    simp
    ring
  exact Finset.sum_congr rfl (fun h _ => hrow h)

theorem fourier_normalized (f : Bits 4 → ℂ) (hf : ∀x, star (f x)*f x=1) :
    (∑ h, star (fourier f h)*fourier f h) = 1 := by
  have hi := synthesis_inner (fourier f) (fourier f)
  simp_rw [fourier_inversion] at hi
  have hin : OddEJM.inner f f = 16 := by
    change (∑ x : Bits 4, star (f x) * f x) = 16
    calc
      _ = ∑ _ : Bits 4, (1 : ℂ) := Finset.sum_congr rfl (fun x _ => hf x)
      _ = 16 := by norm_num [Bits, Bit]
  rw [hin] at hi
  apply mul_left_cancel₀ (by norm_num : (16:ℂ)≠0)
  simpa using hi.symm

theorem fourier_phase_normalized (u : ℂ) (hu : ‖u‖=1) :
    (∑ h, star (fourier (fun x => u^(F x).val) h) *
      fourier (fun x => u^(F x).val) h) = 1 := by
  apply fourier_normalized
  intro x
  have hunit : star u*u=1 := by
    simpa [Complex.star_def, hu] using Complex.conj_mul' u
  rw [star_pow, ← mul_pow, hunit, one_pow]

theorem graphCoefficient_normalized (n : ℕ) (u : ℂ) (hu : ‖u‖=1) :
    (∑ h, star (graphCoefficient n u h)*graphCoefficient n u h) = 1 := by
  have hphase (h : Bits 4) :
      star (graphCoefficient n u h)*graphCoefficient n u h =
        star (fourier (fun x => u^(F x).val) h)*fourier (fun x => u^(F x).val) h := by
    unfold graphCoefficient
    rw [star_mul]
    have huI : star ((-I)^(coord (featureMask n h) (n-1)).val) *
        (-I)^(coord (featureMask n h) (n-1)).val = 1 := by
      rw [star_pow, ← mul_pow]
      norm_num
    calc
      _ = (star ((-I)^(coord (featureMask n h) (n-1)).val) *
          (-I)^(coord (featureMask n h) (n-1)).val) *
          (star (fourier (fun x => u^(F x).val) h)*fourier (fun x => u^(F x).val) h) := by ring
      _ = _ := by rw [huI, one_mul]
  simp_rw [hphase]
  exact fourier_phase_normalized u hu

theorem physicalCoefficients_star_sum (n : ℕ) (u : ℂ) (hu : ‖u‖=1) :
    (∑ d, star (physicalCoefficients n u d)*physicalCoefficients n u d) = 1 := by
  rw [← (coordinatesEquiv n).sum_comp
    (fun d => star (physicalCoefficients n u d)*physicalCoefficients n u d)]
  simp only [coordinatesEquiv, physicalCoefficients, Equiv.coe_fn_mk,
    coordinates_left_inverse]
  exact graphCoefficient_normalized n u hu

/-- 真实背景的十六个固定图码系数严格归一，可直接输入Cauchy证书。 -/
theorem physicalCoefficients_normalized (n : ℕ) (u : ℂ) (hu : ‖u‖=1) :
    (∑ d, Complex.normSq (physicalCoefficients n u d)) = 1 := by
  have hc := physicalCoefficients_star_sum n u hu
  have hr := congrArg Complex.re hc
  simpa [Complex.mul_re, Complex.star_def, Complex.normSq_apply] using hr

end UnifiedEJM.GraphBackground
