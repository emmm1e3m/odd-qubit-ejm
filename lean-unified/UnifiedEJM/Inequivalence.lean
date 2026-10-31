import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace UnifiedEJM.Inequivalence

/-- 单体谱匹配所需的正号多项式。 -/
def radiusPoly (x : ℂ) : ℂ := x^6 + 2*x^4 - 2*x^3 + 2*x^2 + 1

/-- 三种二二划分纯度和匹配所需的多项式。 -/
def purityPoly (x : ℂ) : ℂ :=
  6*x^16 - 3*x^14 + 74*x^12 + 48*x^10 + 134*x^8 +
  48*x^6 + 74*x^4 - 3*x^2 + 6

def bezoutA (x : ℂ) : ℂ :=
  38748*x^15 - 43566*x^14 - 21726*x^13 + 14997*x^12 +
  449440*x^11 - 543239*x^10 + 307430*x^9 - 411045*x^8 +
  495016*x^7 - 1134777*x^6 + 154146*x^5 - 394403*x^4 +
  113680*x^3 - 483031*x^2 + 130296*x + 182138

def bezoutB (x : ℂ) : ℂ :=
  -6458*x^5 + 7261*x^4 - 12524*x^3 + 28569*x^2 - 21716*x + 17553

/-- 直接由内核校验的整数Bezout证书；不依赖外部resultant计算。 -/
theorem bezout_identity (x : ℂ) :
    bezoutA x * radiusPoly x + bezoutB x * purityPoly x = 287456 := by
  unfold bezoutA bezoutB radiusPoly purityPoly
  ring

theorem no_common_root (x : ℂ) : ¬ (radiusPoly x = 0 ∧ purityPoly x = 0) := by
  rintro ⟨hP, hQ⟩
  have h := bezout_identity x
  rw [hP, hQ] at h
  norm_num at h

@[simp] theorem purityPoly_neg (x : ℂ) : purityPoly (-x) = purityPoly x := by
  unfold purityPoly
  ring

/-- 同时排除正、负共同Bloch分量，故排除不限于原参数段。 -/
theorem no_signed_common_root (x : ℂ)
    (hP : radiusPoly x = 0 ∨ radiusPoly (-x) = 0) : purityPoly x ≠ 0 := by
  intro hQ
  rcases hP with hP | hP
  · exact no_common_root x ⟨hP,hQ⟩
  · exact no_common_root (-x) ⟨hP, by simpa using hQ⟩

/-- 论文的Laurent共同分量。 -/
def commonComponent (x : ℂ) : ℂ :=
  (x^6 + 2*x^4 + 2*x^2 + 1) / (16*x^3)

/-- 论文的三种二二划分纯度和闭式。 -/
def puritySumFormula (x : ℂ) : ℂ :=
  (6*x^16 - 3*x^14 + 74*x^12 + 48*x^10 + 698*x^8 +
  48*x^6 + 74*x^4 - 3*x^2 + 6) / (512*x^8)

theorem radius_match_polynomial (x : ℂ) (hx : x ≠ 0)
    (hc : commonComponent x = 1/8 ∨ commonComponent x = -(1/8)) :
    radiusPoly x = 0 ∨ radiusPoly (-x) = 0 := by
  have hx3 : (16:ℂ)*x^3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hx)
  rcases hc with hc | hc
  · left
    have h := (div_eq_iff hx3).mp hc
    unfold radiusPoly
    linear_combination h
  · right
    have h := (div_eq_iff hx3).mp hc
    unfold radiusPoly
    linear_combination h

theorem purity_match_polynomial (x : ℂ) (hx : x ≠ 0)
    (hS : puritySumFormula x = 141/128) : purityPoly x = 0 := by
  have hx8 : (512:ℂ)*x^8 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hx)
  have h := (div_eq_iff hx8).mp hS
  unfold purityPoly
  linear_combination h

theorem no_matching_formulas (x : ℂ) (hx : x ≠ 0)
    (hc : commonComponent x = 1/8 ∨ commonComponent x = -(1/8)) :
    puritySumFormula x ≠ 141/128 := by
  intro hS
  exact no_signed_common_root x (radius_match_polynomial x hx hc)
    (purity_match_polynomial x hx hS)

end UnifiedEJM.Inequivalence

