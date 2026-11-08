import UnifiedEJM.PhysicsLaurent
import Mathlib.Tactic
open OddEJM Complex
open scoped BigOperators Matrix
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def reducedCoeffs (A B : ι → κ → G) (a c : ι) : Fin 3 → G :=
  ![(∑ b, A a b * star (B c b)),
    (∑ b, (A a b * star (A c b) + B a b * star (B c b))),
    (∑ b, B a b * star (A c b))]

def convolutionCoeffs (p q : Fin 3 → G) : Fin 5 → G :=
  ![p 0*q 0, p 0*q 1+p 1*q 0,
    p 0*q 2+p 1*q 1+p 2*q 0, p 1*q 2+p 2*q 1, p 2*q 2]

def traceCoeffs (R : ι → ι → Fin 3 → G) (k : Fin 5) : G :=
  ∑ a, ∑ c, convolutionCoeffs (R a c) (R c a) k

noncomputable def reducedEval (R : Fin 3 → G) (u : ℂ) : ℂ :=
  (R 0 : ℂ)*star u + (R 1 : ℂ) + (R 2 : ℂ)*u

theorem reduced_affine (A B : ι → κ → G) (a c : ι) (u : ℂ)
    (hu : u*star u=1) :
    (∑ b, ((A a b : ℂ)+u*(B a b))*star ((A c b : ℂ)+u*(B c b))) =
      reducedEval (reducedCoeffs A B a c) u := by
  simp only [reducedEval, reducedCoeffs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, map_sum, map_add, map_mul,
    GaussianInt.toComplex_star, Finset.sum_mul, Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simp only [star_add, star_mul, Complex.star_def] at hu ⊢
  linear_combination (B a b : ℂ) * (starRingEnd ℂ) (B c b : ℂ) * hu

theorem reduced_product (p q : Fin 3 → G) (u : ℂ) (hu : u*star u=1) :
    reducedEval p u * reducedEval q u = laurentEval (convolutionCoeffs p q) u := by
  simp [reducedEval, laurentEval, convolutionCoeffs, map_add, map_mul]
  simp only [Complex.star_def] at hu ⊢
  linear_combination ((p 0 : ℂ)*(q 2 : ℂ)+(p 2 : ℂ)*(q 0 : ℂ))*hu

theorem trace_reduced (R : ι → ι → Fin 3 → G) (u : ℂ) (hu : u*star u=1) :
    (∑ a, ∑ c, reducedEval (R a c) u * reducedEval (R c a) u) =
      laurentEval (traceCoeffs R) u := by
  simp_rw [reduced_product _ _ _ hu]
  simp only [laurentEval, traceCoeffs, map_sum, Finset.sum_add_distrib, Finset.sum_mul]

end UnifiedEJM.PhysicsFinite



