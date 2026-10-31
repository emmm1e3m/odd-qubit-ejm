import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace UnifiedEJM.Inequivalence

def radiusPolynomial : ℚ[X] := X^6 + 2*X^4 - 2*X^3 + 2*X^2 + 1

def purityPolynomial : ℚ[X] :=
  6*X^16 - 3*X^14 + 74*X^12 + 48*X^10 + 134*X^8 +
  48*X^6 + 74*X^4 - 3*X^2 + 6

def polynomialA : ℚ[X] :=
  38748*X^15 - 43566*X^14 - 21726*X^13 + 14997*X^12 +
  449440*X^11 - 543239*X^10 + 307430*X^9 - 411045*X^8 +
  495016*X^7 - 1134777*X^6 + 154146*X^5 - 394403*X^4 +
  113680*X^3 - 483031*X^2 + 130296*X + 182138

def polynomialB : ℚ[X] :=
  -6458*X^5 + 7261*X^4 - 12524*X^3 + 28569*X^2 - 21716*X + 17553

/-- 多项式环中的同一整数Bezout恒等式。 -/
theorem polynomial_bezout :
    polynomialA * radiusPolynomial + polynomialB * purityPolynomial = C 287456 := by
  unfold polynomialA polynomialB radiusPolynomial purityPolynomial
  rw [C_ofNat]
  ring

theorem polynomials_coprime : IsCoprime radiusPolynomial purityPolynomial := by
  refine ⟨C (1/287456) * polynomialA, C (1/287456) * polynomialB, ?_⟩
  calc
    _ = C (1/287456) * (polynomialA * radiusPolynomial + polynomialB * purityPolynomial) := by ring
    _ = 1 := by rw [polynomial_bezout,← C_mul]; norm_num

/-- 正式附录使用的非零resultant判断，内核从互素证书推出。 -/
theorem resultant_nonzero : radiusPolynomial.resultant purityPolynomial ≠ 0 := by
  exact Polynomial.resultant_ne_zero _ _ polynomials_coprime

def firstQuotient : ℚ[X] :=
  6*X^10 - 15*X^8 + 12*X^7 + 92*X^6 - 54*X^5 - 88*X^4 +
  268*X^3 + 33*X^2 - 616*X + 602

def firstRemainder : ℚ[X] :=
  816*X^5 - 2340*X^4 + 2168*X^3 - 1240*X^2 + 616*X - 596

/-- 附录列出的首次多项式除法余式，直接核验其商余恒等式。 -/
theorem first_division_identity :
    purityPolynomial = firstQuotient * radiusPolynomial + firstRemainder := by
  unfold purityPolynomial firstQuotient radiusPolynomial firstRemainder
  ring

end UnifiedEJM.Inequivalence

