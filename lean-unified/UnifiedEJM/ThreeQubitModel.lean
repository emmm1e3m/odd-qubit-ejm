import OddEJM.Pauli
import OddEJM.OriginalPhase
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators Topology
open Filter
namespace UnifiedEJM.ThreeQubit
abbrev Space := Fin 7 → ℝ

/-- 七个物理非零字符串的独立相位；物理零串相位固定为零。 -/
def phaseLin (k : Fin 8) : Space →L[ℝ] ℝ :=
  if h : k.val = 0 then 0 else ContinuousLinearMap.proj ⟨k.val - 1, by omega⟩
def phase (θ : Space) (k : Fin 8) : ℝ := phaseLin k θ

/-- CNOT链和末位Hadamard的精确有符号振幅表，公共因子为1/4。 -/
def gate : Matrix (Fin 8) (Fin 8) ℝ := ![![1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, -1, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, -1], ![0, 0, 1, 1, 0, 0, 0, 0], ![1, -1, 0, 0, 0, 0, 0, 0]]
/-- 指定f0相位的实部与虚部。 -/
def baseRe : Fin 8 → ℝ := ![1, 1, 1, 0, 1, 0, 0, -1]
def baseIm : Fin 8 → ℝ := ![0, 0, 0, 1, 0, 1, 1, 0]

def inputRe (θ : Space) (k : Fin 8) : ℝ :=
  baseRe k * Real.cos (phase θ k) - baseIm k * Real.sin (phase θ k)
def inputIm (θ : Space) (k : Fin 8) : ℝ :=
  baseRe k * Real.sin (phase θ k) + baseIm k * Real.cos (phase θ k)
def ampRe (θ : Space) (j : Fin 8) : ℝ := (1/4:ℝ) * ∑ k, gate j k * inputRe θ k
def ampIm (θ : Space) (j : Fin 8) : ℝ := (1/4:ℝ) * ∑ k, gate j k * inputIm θ k
/-- 原三比特电路作用于等模相位输入后的实际复振幅。 -/
def state (θ : Space) (j : Fin 8) : ℂ := ampRe θ j + Complex.I * ampIm θ j

def flip : Fin 9 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7]]
def pauliRe : Fin 9 → Fin 8 → ℝ := ![![1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, -1, -1, -1, -1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, -1, -1, 1, 1, -1, -1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, -1, 1, -1, 1, -1, 1, -1]]
def pauliIm : Fin 9 → Fin 8 → ℝ := ![![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, -1, -1, -1, -1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, -1, -1, 1, 1, -1, -1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, -1, 1, -1, 1, -1, 1], ![0, 0, 0, 0, 0, 0, 0, 0]]
/-- 实际单比特Pauli有限求和；次序X1,Y1,Z1,...,X3,-Y3,Z3。 -/
def expectation (θ : Space) (p : Fin 9) : ℝ :=
  ∑ j, (pauliRe p j *
    (ampRe θ (flip p j) * ampRe θ j + ampIm θ (flip p j) * ampIm θ j) +
    pauliIm p j *
    (ampIm θ (flip p j) * ampRe θ j - ampRe θ (flip p j) * ampIm θ j))
/-- 七个独立signed分量差；其零点包含全部规则测量。 -/
def residual (θ : Space) : Space := fun p => expectation θ (p.succ.castLE (by decide : 8 ≤ 9)) - expectation θ 0

def realDeriv (j : Fin 8) : Space →L[ℝ] ℝ :=
  (1/4:ℝ) • ∑ k, (-(gate j k * baseIm k)) • phaseLin k
def imagDeriv (j : Fin 8) : Space →L[ℝ] ℝ :=
  (1/4:ℝ) • ∑ k, (gate j k * baseRe k) • phaseLin k

lemma inputRe_derivative (k : Fin 8) :
    HasStrictFDerivAt (fun θ => inputRe θ k) (-baseIm k • phaseLin k) 0 := by
  have h := (((phaseLin k).hasStrictFDerivAt (x := (0 : Space))).cos.const_mul (baseRe k)).sub
    (((phaseLin k).hasStrictFDerivAt (x := (0 : Space))).sin.const_mul (baseIm k))
  convert h using 1 <;> ext θ <;> simp [inputRe, phase, Pi.sub_apply, map_zero, neg_smul]
lemma inputIm_derivative (k : Fin 8) :
    HasStrictFDerivAt (fun θ => inputIm θ k) (baseRe k • phaseLin k) 0 := by
  have h := (((phaseLin k).hasStrictFDerivAt (x := (0 : Space))).sin.const_mul (baseRe k)).add
    (((phaseLin k).hasStrictFDerivAt (x := (0 : Space))).cos.const_mul (baseIm k))
  simpa [inputIm, phase, map_zero, Pi.add_def] using h
lemma ampRe_derivative (j : Fin 8) :
    HasStrictFDerivAt (fun θ => ampRe θ j) (realDeriv j) 0 := by
  have h := (HasStrictFDerivAt.sum (u := Finset.univ)
    (fun k _ => (inputRe_derivative k).const_mul (gate j k))).const_mul (1/4:ℝ)
  convert h using 1 <;> ext θ <;> simp [ampRe, realDeriv, smul_smul, mul_neg, neg_smul, Finset.sum_neg_distrib, ContinuousLinearMap.sum_apply]
lemma ampIm_derivative (j : Fin 8) :
    HasStrictFDerivAt (fun θ => ampIm θ j) (imagDeriv j) 0 := by
  have h := (HasStrictFDerivAt.sum (u := Finset.univ)
    (fun k _ => (inputIm_derivative k).const_mul (gate j k))).const_mul (1/4:ℝ)
  simpa [ampIm, imagDeriv, smul_smul] using h

def expectationDeriv (p : Fin 9) : Space →L[ℝ] ℝ :=
  ∑ j, (pauliRe p j •
    ((ampRe 0 (flip p j) • realDeriv j + ampRe 0 j • realDeriv (flip p j)) +
      (ampIm 0 (flip p j) • imagDeriv j + ampIm 0 j • imagDeriv (flip p j))) +
    pauliIm p j •
    ((ampIm 0 (flip p j) • realDeriv j + ampRe 0 j • imagDeriv (flip p j)) -
      (ampRe 0 (flip p j) • imagDeriv j + ampIm 0 j • realDeriv (flip p j))))
lemma expectation_derivative (p : Fin 9) :
    HasStrictFDerivAt (fun θ => expectation θ p) (expectationDeriv p) 0 := by
  have h (j : Fin 8) :=
    ((((ampRe_derivative (flip p j)).mul (ampRe_derivative j)).add
      ((ampIm_derivative (flip p j)).mul (ampIm_derivative j))).const_mul (pauliRe p j)).add
    ((((ampIm_derivative (flip p j)).mul (ampRe_derivative j)).sub
      ((ampRe_derivative (flip p j)).mul (ampIm_derivative j))).const_mul (pauliIm p j))
  convert (HasStrictFDerivAt.sum (u := Finset.univ) (fun j _ => h j)) using 1 <;>
    ext θ <;> simp [expectation, expectationDeriv, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Finset.sum_apply, ContinuousLinearMap.sum_apply]

def jacobian : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi (fun p => expectationDeriv (p.succ.castLE (by decide : 8 ≤ 9)) - expectationDeriv 0)
lemma residual_derivative : HasStrictFDerivAt residual jacobian 0 := by
  exact hasStrictFDerivAt_pi.mpr fun p =>
    (expectation_derivative (p.succ.castLE (by decide : 8 ≤ 9))).sub (expectation_derivative 0)


end UnifiedEJM.ThreeQubit
