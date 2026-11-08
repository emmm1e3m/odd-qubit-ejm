import UnifiedEJM.GraphCoefficients
import UnifiedEJM.GraphCorrelation
import UnifiedEJM.PhysicsSmallBridge
import UnifiedEJM.PhysicsEntanglement
import UnifiedEJM.PhysicsSparseFinish

open OddEJM Complex
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer.SparseCertificate
open PhysicsFinite PhysicsEntanglement GraphBackground

/-- 仅有两个n奇偶分支；值true表示奇数。 -/
def parityCoordinates (odd : Bool) (d : Bits 4) : Bits 4 :=
  featureCoordinates (if odd then 5 else 6) d

/-- F的未归一Walsh和，直接在高斯整数内计算。 -/
def kernelWalsh (h : Bits 4) : G :=
  ∑ v, gsign (UnifiedEJM.F v) * gsign (OddEJM.dot h v)

def coefficientA (odd : Bool) (d : Bits 4) : G :=
  let h := parityCoordinates odd d
  (-gi) ^ (h 3).val * ((if h = 0 then 16 else 0) + kernelWalsh h)

def coefficientB (odd : Bool) (d : Bits 4) : G :=
  let h := parityCoordinates odd d
  (-gi) ^ (h 3).val * ((if h = 0 then 16 else 0) - kernelWalsh h)

/-- 这里没有输入系数正确性的假设：系数由原F的16项Walsh和定义。 -/
theorem physicalCoefficients_affine {n : ℕ} (hn : 5 ≤ n) (u : ℂ) (d : Bits 4) :
    physicalCoefficients n u d =
      ((coefficientA (decide (n % 2 ≠ 0)) d : ℂ) +
        u * (coefficientB (decide (n % 2 ≠ 0)) d : ℂ)) / 32 := by
  have hp : parityCoordinates (decide (n % 2 ≠ 0)) d = featureCoordinates n d := by
    by_cases h : n % 2 = 0 <;> simp [parityCoordinates, featureCoordinates, h]
  rw [physicalCoefficients, graphCoefficient_formula hn]
  have hw : ((kernelWalsh (featureCoordinates n d) : G) : ℂ) =
      16 * fourier (fun v => bitSign (UnifiedEJM.F v)) (featureCoordinates n d) := by
    simp [kernelWalsh, fourier, character, map_sum, map_mul]
  simp only [coefficientA, coefficientB, hp, map_mul, map_add, map_sub, map_pow,
    map_neg, gi_complex, hw]
  by_cases hz : featureCoordinates n d = 0 <;>
    norm_num [hz, GaussianInt.toComplex_def] <;> ring

/-- S的三个Laurent系数，顺序为-1,0,1。 -/
def correlationCoeffs (A B : Bits 4 → G) (d k : Bits 4) : Fin 3 → G :=
  ![∑ l, A l * star (B (l + d)) * gsign (OddEJM.dot (l + d) k),
    ∑ l, (A l * star (A (l + d)) + B l * star (B (l + d))) *
      gsign (OddEJM.dot (l + d) k),
    ∑ l, B l * star (A (l + d)) * gsign (OddEJM.dot (l + d) k)]

def squaredCoeffs (A B : Bits 4 → G) (d k : Bits 4) : Fin 5 → G :=
  coefficientTerm (correlationCoeffs A B d k) (correlationCoeffs A B d k)

private theorem affine_pair (a b c d u : ℂ) (hu : u * star u = 1) :
    (a + u * b) * star (c + u * d) =
      a * star d * star u + (a * star c + b * star d) + b * star c * u := by
  simp only [star_add, star_mul]
  linear_combination b * star d * hu

theorem affineCorrelation_reduced (A B : Bits 4 → G) (d k : Bits 4)
    (u : ℂ) (hu : u * star u = 1) :
    codeCorrelation (fun l => ((A l : ℂ) + u * (B l : ℂ)) / 32) d k =
      reducedEval (correlationCoeffs A B d k) u / 1024 := by
  unfold codeCorrelation
  simp only [reducedEval, correlationCoeffs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
    map_sum, map_add, map_mul, GaussianInt.toComplex_star, gsign_complex]
  simp only [character]
  rw [show (∑ l, ((A l : ℂ) + u * (B l : ℂ)) / 32 *
      star (((A (l + d) : ℂ) + u * (B (l + d) : ℂ)) / 32) *
      bitSign (OddEJM.dot (l + d) k)) =
    (∑ l, ((A l : ℂ) + u * (B l : ℂ)) *
      star ((A (l + d) : ℂ) + u * (B (l + d) : ℂ)) *
      bitSign (OddEJM.dot (l + d) k)) / 1024 by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [star_div₀, star_ofNat]
      ring]
  congr 1
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [affine_pair _ _ _ _ u hu]
  simp only [Complex.star_def]
  ring

/-- 由|u|=1直接展开平方模，无三角表假设。 -/
theorem reduced_normSq (p : Fin 3 → G) (u : ℂ) (hu : u * star u = 1) :
    (Complex.normSq (reducedEval p u) : ℂ) =
      laurentEval (coefficientTerm p p) u := by
  have h := reduced_product p ![star (p 2), star (p 1), star (p 0)] u hu
  have hs : reducedEval ![star (p 2), star (p 1), star (p 0)] u =
      star (reducedEval p u) := by
    simp [reducedEval, star_add, star_mul, GaussianInt.toComplex_star]
    ring
  rw [hs] at h
  rw [← Complex.mul_conj]
  simpa [convolutionCoeffs, coefficientTerm, Complex.star_def, add_comm, add_left_comm, add_assoc] using h

theorem affineCorrelation_normSq (A B : Bits 4 → G) (d k : Bits 4)
    (u : ℂ) (hu : u * star u = 1) :
    (Complex.normSq (codeCorrelation
      (fun l => ((A l : ℂ) + u * (B l : ℂ)) / 32) d k) : ℂ) =
      laurentEval (squaredCoeffs A B d k) u / 1048576 := by
  calc
    _ = (Complex.normSq (reducedEval (correlationCoeffs A B d k) u) : ℂ) / 1048576 := by
      rw [affineCorrelation_reduced A B d k u hu, Complex.normSq_div]
      norm_num
    _ = _ := by
      rw [reduced_normSq _ u hu]
      rfl

/-- 单点真实背景相关函数的全参数三角表达式。 -/
theorem physicalCorrelation_trig {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (d k : Bits 4) :
    Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k) =
      trigEval (realCoeffs (squaredCoeffs
        (coefficientA (decide (n % 2 ≠ 0)))
        (coefficientB (decide (n % 2 ≠ 0))) d k)) t / 1048576 := by
  have heq : physicalCoefficients n (anglePhase t) =
      fun l => ((coefficientA (decide (n % 2 ≠ 0)) l : ℂ) +
        anglePhase t * (coefficientB (decide (n % 2 ≠ 0)) l : ℂ)) / 32 := by
    funext l
    exact physicalCoefficients_affine hn _ l
  rw [heq]
  have h := affineCorrelation_normSq
    (coefficientA (decide (n % 2 ≠ 0))) (coefficientB (decide (n % 2 ≠ 0)))
    d k (anglePhase t) (by simpa only [mul_comm] using anglePhase_star_mul t)
  have hr := congrArg Complex.re h
  simpa [Complex.div_re, laurentEval_re] using hr

end UnifiedEJM.WeightedTransfer.SparseCertificate

