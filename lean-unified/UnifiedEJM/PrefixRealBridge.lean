import UnifiedEJM.PrefixP12Bridge
import UnifiedEJM.PrefixAnalytic

open OddEJM Complex
open UnifiedEJM.PhysicsFinite UnifiedEJM.BoundaryAmplitude UnifiedEJM.PrefixKernel

namespace UnifiedEJM.PrefixCounts

noncomputable section

/-- 任意Gaussian Laurent系数的真实Fourier系数，无需额外共轭对称前提。 -/
def realFourier (q : Fin 5 → G) : Fin 5 → ℝ :=
  ![(q 2).re, (q 1).re + (q 3).re, (q 1).im - (q 3).im,
    (q 0).re + (q 4).re, (q 0).im - (q 4).im]

theorem laurentEval_realFourier (q : Fin 5 → G) (t : ℝ) :
    (laurentEval q (anglePhase t)).re = PrefixAnalytic.eval (realFourier q) t := by
  simp only [laurentEval, PrefixAnalytic.eval, realFourier, anglePhase,
    Complex.exp_ofReal_mul_I, GaussianInt.toComplex_def₂, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Matrix.cons_val_zero, Real.cos_two_mul', Real.sin_two_mul]
  simp [-GaussianInt.intCast_re, -GaussianInt.intCast_im]
  ring

/-- 原门归一化在实纯度中给出统一分母2^(2n+2)。 -/
theorem normalized_laurent_realFourier (n : ℕ) (q : Fin 5 → G) (t : ℝ) :
    (((((2 : ℂ)^(n+1))⁻¹)^2) * laurentEval q (anglePhase t)).re =
      PrefixAnalytic.eval (realFourier q) t / (2 : ℝ)^(2*n+2) := by
  have hs : (((2 : ℂ)^(n+1))⁻¹)^2 =
      (((((2 : ℝ)^(n+1))⁻¹)^2 : ℝ) : ℂ) := by push_cast; rfl
  have hp : ((2 : ℝ)^(n+1))^2 = (2 : ℝ)^(2*n+2) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, laurentEval_realFourier]
  rw [inv_pow, hp]
  ring

/-- 全部两侧至少三位的实际纯度，已转换为228使用的真实Fourier求值。 -/
theorem seed_prefix_longSum_re (LA LB : ℕ) (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (longN LA LB) (longK LA))
      (UnifiedEJM.seed (longN LA LB) t)).re =
      PrefixAnalytic.eval
        (realFourier (longSum (runInfo LA) (runInfo LB) (2^(LA-1)) (2^(LB-1)))) t /
          (2 : ℝ)^(2*longN LA LB+2) := by
  rw [seed_prefix_longSum, normalized_laurent_realFourier]

/-- 两位侧同样来自原seed；自由组任意正长度、首尾两个方向统一。 -/
theorem seed_prefix_p12Sum_re {L : ℕ} (hL : 1 ≤ L) (suffix : Bool) (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (smallN L) (smallK L suffix))
      (UnifiedEJM.seed (smallN L) t)).re =
      PrefixAnalytic.eval
        (realFourier (p12Sum (lengthParity (smallN L)) suffix (2^(L-1)))) t /
          (2 : ℝ)^(2*smallN L+2) := by
  rw [seed_prefix_p12Sum hL, normalized_laurent_realFourier]

end

end UnifiedEJM.PrefixCounts
