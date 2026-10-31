import UnifiedEJM.CurvedMain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # 四比特闭式曲线在指定基点的精确斜率 -/
namespace UnifiedEJM.Curved

private lemma sin_hasDerivAt_zero : HasDerivAt Real.sin 1 0 := by
  simpa using Real.hasDerivAt_sin 0

private lemma cos_hasDerivAt_zero : HasDerivAt Real.cos 0 0 := by
  simpa using Real.hasDerivAt_cos 0

lemma A_hasDerivAt_zero : HasDerivAt A 2 0 := by
  have h := cos_hasDerivAt_zero.mul
    ((hasDerivAt_const (0:ℝ) (1:ℝ)).add (sin_hasDerivAt_zero.const_mul 2))
  change HasDerivAt (fun u => Real.cos u*(1+2*Real.sin u)) 2 0
  convert h using 1 <;> norm_num

lemma B_hasDerivAt_zero : HasDerivAt B 1 0 := by
  have h := ((cos_hasDerivAt_zero.const_mul 2).add sin_hasDerivAt_zero).add_const 1
  change HasDerivAt (fun u => 2*Real.cos u+Real.sin u+1) 1 0
  convert h using 1 <;> norm_num

lemma C_hasDerivAt_zero : HasDerivAt C 2 0 := by
  have h := (sin_hasDerivAt_zero.const_mul 2).mul cos_hasDerivAt_zero
  change HasDerivAt (fun u => 2*Real.sin u*Real.cos u) 2 0
  convert h using 1 <;> norm_num

lemma paperDisc_hasDerivAt_zero : HasDerivAt paperDisc (-2) 0 := by
  have h := (B_hasDerivAt_zero.pow 2).sub ((A_hasDerivAt_zero.const_mul 4).mul C_hasDerivAt_zero)
  change HasDerivAt (fun u => (B u)^2-4*A u*C u) (-2) 0
  convert h using 1 <;> norm_num [A,B,C]

lemma sqrt_paperDisc_hasDerivAt_zero :
    HasDerivAt (fun u => Real.sqrt (paperDisc u)) (-1/3) 0 := by
  have h := paperDisc_hasDerivAt_zero.sqrt (by norm_num [paperDisc,A,B,C])
  norm_num [paperDisc,A,B,C] at h ⊢
  exact h

lemma paperRoot_zero : paperRoot 0=0 := by simp [paperRoot,C]

/-- 原论文根号闭式直接求导，不以形式的隐式微分作为前提。 -/
lemma paperRoot_hasDerivAt_zero : HasDerivAt paperRoot (2/3) 0 := by
  have h := (C_hasDerivAt_zero.const_mul 2).div
    (B_hasDerivAt_zero.add sqrt_paperDisc_hasDerivAt_zero)
    (by norm_num [paperDisc,A,B,C])
  norm_num [paperRoot,paperDisc,A,B,C] at h ⊢
  exact h

lemma paperDelta_hasDerivAt_zero : HasDerivAt paperDelta (-4/3) 0 := by
  have h := paperRoot_hasDerivAt_zero.arctan.const_mul (-2)
  change HasDerivAt (fun u => -2*Real.arctan (paperRoot u)) (-4/3) 0
  convert h using 1 <;> norm_num [paperRoot_zero]

/-- q=-δ 的原弧度参数导数为4/3。 -/
lemma q_hasDerivAt_zero : HasDerivAt (fun b => -paperDelta b) (4/3) 0 := by
  convert paperDelta_hasDerivAt_zero.neg using 1 <;> norm_num

lemma paperGain_hasDerivAt_zero : HasDerivAt paperGain (4/3) 0 := by
  have h := ((hasDerivAt_id (0:ℝ)).add paperDelta_hasDerivAt_zero).cos.sub
    paperDelta_hasDerivAt_zero.sin
  norm_num [paperGain,paperDelta_zero] at h ⊢
  exact h

/-- 与CurvedMain真实偏迹相同的半径函数，在基点的精确导数。 -/
theorem radius_hasDerivAt_zero : HasDerivAt radius (Real.sqrt 3/6) 0 := by
  have h := paperGain_hasDerivAt_zero.const_mul (Real.sqrt 3/8)
  convert h using 1
  · rfl
  · ring

lemma radius_deriv_zero : deriv radius 0=Real.sqrt 3/6 :=
  radius_hasDerivAt_zero.deriv

end UnifiedEJM.Curved
