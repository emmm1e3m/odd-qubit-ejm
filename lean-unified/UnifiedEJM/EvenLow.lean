import UnifiedEJM.EvenAxes
import OddEJM.Finite
import Mathlib.Tactic

namespace UnifiedEJM.EvenLow
open OddEJM Complex
open UnifiedEJM.EvenWalsh
open scoped BigOperators

/-- p=0,1,2 分别对应 X、signed Y、Z。 -/
def aMask (n j : ℕ) (p : Fin 3) : Bits n :=
  if p = 2 then unitBit n (n-1)
  else if j = n-1 then
    if p = 1 then unitBit n (n-1) + unitBit n (n-2) else unitBit n (n-2)
  else (unitBit n j + if j=0 then 0 else unitBit n (j-1)) +
    if p=1 then unitBit n (n-1) else 0

def bMask (n j : ℕ) (p : Fin 3) : Bits n :=
  if p = 0 then if j = n-1 then unitBit n (n-1) else 0
  else if p=1 ∧ j=n-1 then unitBit n (n-1) else UnifiedEJM.MaskFacts.cutTail n j

def pauliCoeff (p : Fin 3) : ℂ := if p=1 then I else 1

def isClassI (n j : ℕ) (p : Fin 3) : Bool := p=2 ∨ j=0 ∨ j=n-1

/-- AND 颜色对的整数系数；它们决定任意复相位的背景相关和。 -/
def axisCoeff (n j : ℕ) (p : Fin 3) (r s : Bit) : ℤ :=
  ∑ z : Bits n, if qA z=r ∧ qA (z+aMask n j p)=s
    then intSign (dot (aMask n j p + bMask n j p) z) else 0

def maskCertificate (n j : ℕ) (p : Fin 3) : Prop :=
  aMask n j p ≠ 0 ∧
  dot (bMask n j p) (aMask n j p) = (if p=1 then 1 else 0) ∧
  weight (aMask n j p) = (if isClassI n j p then (if p=1 then 2 else 1)
    else (if p=1 then 3 else 2)) ∧
  qA (aMask n j p) = (if isClassI n j p then 1 else 0) ∧
  ∀ r s : Bit, axisCoeff n j p r s = 0

instance (n j : ℕ) (p : Fin 3) : Decidable (maskCertificate n j p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- n=2,4,6 的全部实际拉回和 144 项整数背景系数由内核精确核查。 -/
theorem low_checked : ∀ n : Fin 7, n.val=2 ∨ n.val=4 ∨ n.val=6 →
    ∀ j : Fin n.val, ∀ p : Fin 3, maskCertificate n.val j.val p := by decide

theorem low_certificate {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6)
    (j : ℕ) (hj : j<n) (p : Fin 3) : maskCertificate n j p :=
  low_checked ⟨n,by omega⟩ hn ⟨j,hj⟩ p

theorem coefficient_cast (n j : ℕ) (p : Fin 3) (r s : Bit) :
    (axisCoeff n j p r s : ℂ) = ∑ z : Bits n,
      if qA z=r ∧ qA (z+aMask n j p)=s then character (aMask n j p+bMask n j p) z else 0 := by
  simp [axisCoeff, Int.cast_sum, character]

/-- 整数系数证书提升到任意复输入相位，未作参数采样。 -/
theorem axis_correlation_zero {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6)
    (j : ℕ) (hj : j<n) (p : Fin 3) (u : ℂ) :
    (∑ z : Bits n, character (aMask n j p+bMask n j p) z *
      (u^(qA z).val * star (u^(qA (z+aMask n j p)).val))) = 0 := by
  have hc := (low_certificate hn j hj p).2.2.2.2
  have hp (z : Bits n) :
      character (aMask n j p+bMask n j p) z *
          (u^(qA z).val * star (u^(qA (z+aMask n j p)).val)) =
      ∑ r : Bit, ∑ s : Bit,
        (if qA z=r ∧ qA (z+aMask n j p)=s
         then character (aMask n j p+bMask n j p) z else 0) *
         u^r.val * star (u^s.val) := by
    simp [ite_and, Finset.sum_ite_irrel, eq_comm, mul_assoc]
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s _
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← coefficient_cast, hc]
  simp

theorem background_zero {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6)
    (j : ℕ) (hj : j<n) (p : Fin 3) (u : ℂ) :
    pauliExpectation (EvenRaw.background qA UnifiedEJM.q u 1)
      (aMask n j p) (bMask n j p) (pauliCoeff p) = 0 := by
  have heq : EvenRaw.background (n:=n) qA UnifiedEJM.q u 1 =
      fun z => I^weight z * u^(qA z).val := by funext z; simp [EvenRaw.background]
  rw [heq, EvenRaw.phase_background_sum, axis_correlation_zero hn j hj p u, mul_zero]

theorem coefficient_hermitian {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6)
    (j : ℕ) (hj : j<n) (p : Fin 3) :
    pauliCoeff p * character (bMask n j p) (aMask n j p) = star (pauliCoeff p) := by
  have hd := (low_certificate hn j hj p).2.1
  simp only [character, hd]
  by_cases hp : p=1 <;> simp [pauliCoeff, hp, bitSign, Complex.star_def]

theorem coefficient_gamma {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6)
    (j : ℕ) (hj : j<n) (p : Fin 3) :
    pauliCoeff p * star (I ^ weight (aMask n j p)) =
      if isClassI n j p then -I else -1 := by
  have hw := (low_certificate hn j hj p).2.2.1
  rw [hw]
  by_cases hI : isClassI n j p
  · simp only [if_pos hI]
    by_cases hp : p=1 <;> norm_num [pauliCoeff, hp, Complex.star_def]
  · simp only [if_neg hI]
    by_cases hp : p=1 <;> norm_num [pauliCoeff, hp, Complex.star_def]

/-- 小偶数维原 AND 轴的全部未归一化 signed 分量。 -/
theorem raw_components {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6)
    (α : ℝ) (j : ℕ) (hj : j<n) (p : Fin 3) :
    pauliExpectation (EvenFamily.diagonal n α 0)
      (aMask n j p) (bMask n j p) (pauliCoeff p) = ((2 * Real.cos α : ℝ) : ℂ) := by
  have hqa := (low_certificate hn j hj p).2.2.2.1
  have hne := (low_certificate hn j hj p).1
  unfold EvenFamily.diagonal
  rw [EvenRaw.raw_expectation qA UnifiedEJM.q _ _ _ _ _ (qA_zero n) (q_zero n)
    hne (coefficient_hermitian hn j hj p)]
  simp only [OddEJM.anglePhase_zero, background_zero hn j hj p, zero_add,
    coefficient_gamma hn j hj p, hqa, one_pow, mul_one]
  by_cases hI : isClassI n j p
  · simp only [if_pos hI, ZMod.val_one_eq_one_mod, Nat.one_mod, pow_one]
    have hc := EvenRaw.classI_cross α 0
    simp only [OddEJM.anglePhase_zero, Real.sin_zero, sub_zero, mul_one] at hc
    rw [hc]
  · simp only [if_neg hI, ZMod.val_zero, pow_zero, star_one, mul_one]
    have hc := EvenRaw.classII_cross α 0
    simp only [OddEJM.anglePhase_zero, Real.sin_zero, sub_zero, star_one, mul_one] at hc
    rw [hc]

theorem normalized_components {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6)
    (α : ℝ) (j : ℕ) (hj : j<n) (p : Fin 3) :
    pauliExpectation (fun z => normFactor n * EvenFamily.diagonal n α 0 z)
      (aMask n j p) (bMask n j p) (pauliCoeff p) =
      ((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) := by
  apply EvenRaw.normalized_expectation (by omega)
  exact raw_components hn α j hj p

private theorem cutTail_circuit (n j : ℕ) :
    UnifiedEJM.MaskFacts.cutTail n j = setBit (CircuitPauli.tailMask n j) (n-1) 0 := by
  rw [UnifiedEJM.MaskFacts.cutTail_eq_setBit]
  rfl

theorem seed_localX_low {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6) (α : ℝ)
    (j : ℕ) (hj : j<n) :
    pauliExpectation (EvenFamily.seed n α 0) (unitBit n j) 0 1 =
      ((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) := by
  let f : Vec n := fun z => normFactor n * EvenFamily.diagonal n α 0 z
  have he := normalized_components hn α j hj 0
  change pauliExpectation f _ _ _ = _ at he
  by_cases hl : j=n-1
  · subst j
    rw [show EvenFamily.seed n α 0 = circuit f from rfl]
    rw [CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
      (CircuitPauli.localX_last (by omega) f)]
    simpa [aMask, bMask, pauliCoeff] using he
  · have hjn : j<n-1 := by omega
    rw [show EvenFamily.seed n α 0 = circuit f from rfl]
    rw [CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
      (CircuitPauli.localX_beforeLast j hjn f)]
    simpa [aMask, bMask, pauliCoeff, hl] using he

theorem seed_localZ_low {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6) (α : ℝ)
    (j : ℕ) (hj : j<n) :
    pauliExpectation (EvenFamily.seed n α 0) 0 (unitBit n j) 1 =
      ((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) := by
  let f : Vec n := fun z => normFactor n * EvenFamily.diagonal n α 0 z
  have he := normalized_components hn α j hj 2
  change pauliExpectation f _ _ _ = _ at he
  rw [show EvenFamily.seed n α 0 = circuit f from rfl]
  rw [CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
    (CircuitPauli.localZ_table (by omega) j hj f)]
  simpa [aMask, bMask, pauliCoeff, cutTail_circuit] using he

theorem seed_localY_low {n : ℕ} (hn : n=2 ∨ n=4 ∨ n=6) (α : ℝ)
    (j : ℕ) (hj : j<n) :
    pauliExpectation (EvenFamily.seed n α 0) (unitBit n j) (unitBit n j) I =
      if j=n-1 then -((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ)
      else ((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) := by
  let f : Vec n := fun z => normFactor n * EvenFamily.diagonal n α 0 z
  have he := normalized_components hn α j hj 1
  change pauliExpectation f _ _ _ = _ at he
  by_cases hl : j=n-1
  · subst j
    rw [if_pos rfl, show EvenFamily.seed n α 0 = circuit f from rfl]
    rw [CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
      (CircuitPauli.localY_last (by omega) f)]
    rw [EvenFamily.expectation_neg]
    congr 1
    simpa [aMask, bMask, pauliCoeff] using he
  · have hjn : j<n-1 := by omega
    rw [if_neg hl, show EvenFamily.seed n α 0 = circuit f from rfl]
    rw [CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
      (CircuitPauli.localY_beforeLast j hjn f)]
    simpa [aMask, bMask, pauliCoeff, hl, cutTail_circuit] using he

/-- 前作 AND 轴的全偶数维实际种子分量；低维没有遗留。 -/
theorem seed_localX_all {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (α : ℝ)
    (j : ℕ) (hj : j<n) :
    pauliExpectation (EvenFamily.seed n α 0) (unitBit n j) 0 1 =
      ((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) := by
  by_cases hn8 : 8 ≤ n
  · simpa [EvenFamily.component] using EvenFamily.seed_localX hn8 hev α 0 j hj
  · have hp := Nat.even_iff.mp hev
    exact seed_localX_low (by omega) α j hj

theorem seed_localY_all {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (α : ℝ)
    (j : ℕ) (hj : j<n) :
    pauliExpectation (EvenFamily.seed n α 0) (unitBit n j) (unitBit n j) I =
      if j=n-1 then -((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ)
      else ((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) := by
  by_cases hn8 : 8 ≤ n
  · simpa [EvenFamily.component] using EvenFamily.seed_localY hn8 hev α 0 j hj
  · have hp := Nat.even_iff.mp hev
    exact seed_localY_low (by omega) α j hj

theorem seed_localZ_all {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (α : ℝ)
    (j : ℕ) (hj : j<n) :
    pauliExpectation (EvenFamily.seed n α 0) 0 (unitBit n j) 1 =
      ((Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) := by
  by_cases hn8 : 8 ≤ n
  · simpa [EvenFamily.component] using EvenFamily.seed_localZ hn8 hev α 0 j hj
  · have hp := Nat.even_iff.mp hev
    exact seed_localZ_low (by omega) α j hj

/-- 所有偶数 n≥2、所有测量列的真实单比特偏迹。 -/
theorem measurement_reduced_all {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (α : ℝ)
    (label : Bits n) (j : Fin n) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (EvenFamily.measurement n α 0 label) j = (1/2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      ((Real.sqrt 3 * Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) •
        ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ)) := by
  have hh := Physical.measurement_reduced_from_seed (by omega) (EvenFamily.diagonal n α 0)
    (EvenFamily.diagonal_unit n α 0) (Real.cos α / (2:ℝ)^(n-1)) label j
    (seed_localX_all hn hev α j.val j.isLt) (seed_localY_all hn hev α j.val j.isLt)
    (seed_localZ_all hn hev α j.val j.isLt)
  simpa only [EvenFamily.measurement, mul_div_assoc] using hh

/-- 二比特空 AND 乘积与四比特单坐标支持，逐输入核查。 -/
theorem qA_two : ∀ z : Bits 2, qA z=1 := by decide
theorem qA_four : ∀ z : Bits 4, qA z=1-z 1 := by decide
theorem qA_six : ∀ z : Bits 6, qA z=(1-z 1)*(1-z 3) := by decide

theorem dA_two (z : Bits 2) : dA z=if z=0 then 0 else 1 := by simp [dA,qA_two]
theorem dA_four (z : Bits 4) : dA z=if z=0 then 0 else 1-z 1 := by simp [dA,qA_four]

theorem cosine_radius_nonnegative (n : ℕ) (α : ℝ) (hα : α ∈ Geometry.parameterInterval) :
    0 ≤ Real.sqrt 3 * Real.cos α / (2:ℝ)^(n-1) := by
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 3)
    (Real.cos_nonneg_of_mem_Icc hα)) (by positivity)

theorem measurement_basepoint (n : ℕ) (hn : 1 ≤ n) (label : Bits n) :
    EvenFamily.measurement n 0 0 label =
      circuit (fun z => normFactor n * originalDiagonal z * character label z) := by
  rw [EvenFamily.first_axis_measurement hn]
  simp

theorem measurement_cosine_endpoint {n : ℕ} (hn : 2 ≤ n) (hev : Even n)
    (label : Bits n) (j : Fin n) :
    reduced (EvenFamily.measurement n (Real.pi/2) 0 label) j =
      (1/2 : ℂ) • (1 : Matrix Bit Bit ℂ) := by
  rw [measurement_reduced_all hn hev]
  simp

/-- 原 AND 相位全偶数定理：正交完备、精确偏迹与原相位逐列对应。 -/
theorem even_cosine_family {n : ℕ} (hn : 2 ≤ n) (hev : Even n) :
    (∀ α k l, inner (EvenFamily.measurement n α 0 k) (EvenFamily.measurement n α 0 l) =
      if k=l then 1 else 0) ∧
    (∀ α (label : Bits n) (j : Fin n),
      let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
      reduced (EvenFamily.measurement n α 0 label) j = (1/2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
        ((Real.sqrt 3 * Real.cos α / (2:ℝ)^(n-1) : ℝ) : ℂ) •
          ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ))) ∧
    (∀ α label, EvenFamily.measurement n α 0 label =
      circuit (fun z => normFactor n *
        (originalDiagonal z * anglePhase α ^ (dA z).val) * character label z)) ∧
    (∀ α z w, (∑ label, EvenFamily.measurement n α 0 label z *
        star (EvenFamily.measurement n α 0 label w)) = if z=w then 1 else 0) := by
  refine ⟨fun α k l => EvenFamily.measurement_orthonormal (by omega) α 0 k l,
    measurement_reduced_all hn hev, ?_, ?_⟩
  · exact fun α label => EvenFamily.first_axis_measurement (by omega) α label
  · exact fun α z w => EvenFamily.measurement_complete (by omega) α 0 z w

end UnifiedEJM.EvenLow
