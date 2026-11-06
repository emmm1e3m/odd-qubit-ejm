import UnifiedEJM.PhysicsFiniteTables
import UnifiedEJM.Multipartite

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite

variable {ι : Type*} [Fintype ι]

/-- 仿射振幅的两个未共轭因子相乘得到二次多项式。 -/
def pairCoeffs (A B : ι → G) (i j : ι) : Fin 3 → G :=
  ![A i * A j, A i * B j + B i * A j, B i * B j]

/-- 频率按-2,-1,0,1,2排列。 -/
def coefficientTerm (p q : Fin 3 → G) : Fin 5 → G :=
  ![p 0 * star (q 2), p 0 * star (q 1) + p 1 * star (q 2),
    p 0 * star (q 0) + p 1 * star (q 1) + p 2 * star (q 2),
    p 1 * star (q 0) + p 2 * star (q 1), p 2 * star (q 0)]

def gCoefficients (mix : ι → ι → ι) (A B : ι → G) (k : Fin 5) : G :=
  ∑ i, ∑ j, coefficientTerm (pairCoeffs A B i j)
    (pairCoeffs A B (mix i j) (mix j i)) k

noncomputable def laurentEval (coeff : Fin 5 → G) (u : ℂ) : ℂ :=
  (coeff 0 : ℂ) * star u ^ 2 + (coeff 1 : ℂ) * star u + (coeff 2 : ℂ) +
    (coeff 3 : ℂ) * u + (coeff 4 : ℂ) * u^2

private theorem four_affine_product (a b c d e f g h u v : ℂ) (hu : u*v = 1) :
    (a+u*b)*(c+u*d)*(e+v*f)*(g+v*h) =
      a*c*f*h*v^2 + (a*c*(e*h+f*g)+(a*d+b*c)*f*h)*v +
      (a*c*e*g+(a*d+b*c)*(e*h+f*g)+b*d*f*h) +
      ((a*d+b*c)*e*g+b*d*(e*h+f*g))*u + b*d*e*g*u^2 := by
  linear_combination ((a*d+b*c)*(e*h+f*g) + u*b*d*(e*h+f*g) +
    v*(a*d+b*c)*f*h + (u*v+1)*b*d*f*h) * hu

theorem affine_term (A B : ι → G) (i j k l : ι) (u : ℂ) (hu : u * star u = 1) :
    ((A i : ℂ)+u*(B i : ℂ))*((A j : ℂ)+u*(B j : ℂ))*
      star ((A k : ℂ)+u*(B k : ℂ))*star ((A l : ℂ)+u*(B l : ℂ)) =
      laurentEval (coefficientTerm (pairCoeffs A B i j) (pairCoeffs A B k l)) u := by
  simp only [star_add, star_mul]
  rw [mul_comm (star (B k : ℂ)) (star u), mul_comm (star (B l : ℂ)) (star u)]
  rw [four_affine_product _ _ _ _ _ _ _ _ u (star u) hu]
  simp [laurentEval, coefficientTerm, pairCoeffs, map_add, map_mul, star_add, star_mul]
  ring

/-- 五个整数系数精确决定所有实参数的双副本纯度。 -/
theorem affine_swap_sum (mix : ι → ι → ι) (A B : ι → G) (u : ℂ)
    (hu : u * star u = 1) :
    (∑ i, ∑ j, ((A i : ℂ)+u*(B i : ℂ))*((A j : ℂ)+u*(B j : ℂ))*
      star ((A (mix i j) : ℂ)+u*(B (mix i j) : ℂ))*
      star ((A (mix j i) : ℂ)+u*(B (mix j i) : ℂ))) =
      laurentEval (gCoefficients mix A B) u := by
  simp_rw [affine_term A B _ _ _ _ u hu]
  simp only [laurentEval, gCoefficients, map_sum, Finset.sum_add_distrib,
    Finset.sum_mul]

end UnifiedEJM.PhysicsFinite
