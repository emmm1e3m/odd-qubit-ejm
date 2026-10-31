import UnifiedEJM.LowBoolean
import UnifiedEJM.BooleanLines
import UnifiedEJM.BooleanDelta

/-! 把低维边界字符排除接到实际电路的局部 Pauli 等平方条件。 -/
noncomputable section
namespace UnifiedEJM.LowBooleanPhysical
open OddEJM Complex MaskFacts
open UnifiedEJM.BooleanLines UnifiedEJM.LowBoolean
open scoped BigOperators

theorem pull_internalX {n : ℕ} (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) :
    PullII (adjacentMask n j) 0 1 := by
  have hp : j-1 < n := by omega
  have hlt : j < n := by omega
  have hne : j-1 ≠ j := by omega
  have hne' : j ≠ j-1 := by omega
  have hw : weight (adjacentMask n j) = 2 := weight_pair (j-1) j hp hlt hne
  have ha : adjacentMask n j ≠ 0 := nonzero_of_weight (by omega)
  refine ⟨ha, by simpa using ha, ?_, ?_, ?_⟩
  · simp only [add_zero,adjacentMask,dot_add,dot_unit _ _ hp,dot_unit _ _ hlt]
    simp [unitBit,hne,hne',CharTwo.add_self_eq_zero]
  · simp [character,dot]
  · norm_num [hw]

theorem pull_lastX {n : ℕ} (hn : 2 ≤ n) :
    PullI (unitBit n (n-2)) (unitBit n (n-1)) 1 := by
  have h2 : n-2 < n := by omega
  have hne : n-2 ≠ n-1 := by omega
  have hw := weight_unit (n:=n) (n-2) h2
  have hd : dot (unitBit n (n-2) + unitBit n (n-1)) (unitBit n (n-2)) = 1 := by
    rw [dot_unit _ _ h2]
    simp [unitBit,hne]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_⟩
  · simp only [character,dot_unit _ _ h2]
    simp [unitBit,hne]
  · simp [hw]

theorem pull_firstY {n : ℕ} (hn : 2 ≤ n) :
    PullI (unitBit n 0 + unitBit n (n-1)) (cutTail n 0) I := by
  have h0 : 0 < n := by omega
  have hl : n-1 < n := by omega
  have hne : 0 ≠ n-1 := by omega
  have hw := weight_pair (n:=n) 0 (n-1) h0 hl hne
  have hd : dot ((unitBit n 0 + unitBit n (n-1)) + cutTail n 0)
      (unitBit n 0 + unitBit n (n-1)) = 1 := by
    rw [h_firstY (by omega),dot_add,dot_unit _ _ h0,dot_unit _ _ hl]
    simp [tailMask,show 1 ≤ n-1 by omega]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_⟩
  · simp only [character,dot_add,dot_unit _ _ h0,dot_unit _ _ hl]
    simp [cutTail,show 0 < n-1 by omega]
  · norm_num [hw]

theorem pull_internalY {n : ℕ} (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) :
    PullII (internalYMask n j) (cutTail n j) I := by
  have hp : j-1 < n := by omega
  have hlt : j < n := by omega
  have hl : n-1 < n := by omega
  have hpj : j-1 ≠ j := by omega
  have hjp : j ≠ j-1 := by omega
  have hpl : j-1 ≠ n-1 := by omega
  have hjl : j ≠ n-1 := by omega
  have hlp : n-1 ≠ j-1 := by omega
  have hw : weight (internalYMask n j) = 3 :=
    weight_triple (j-1) j (n-1) hp hlt hl hpj hpl hjl
  have ha : internalYMask n j ≠ 0 := nonzero_of_weight (by omega)
  have hh : internalYMask n j + cutTail n j ≠ 0 := by
    rw [h_internalY j hj hjn]
    intro hz
    have hz' := congrFun hz (⟨n-1,hl⟩ : Fin n)
    simp [internalYCharacter,unitBit,tailMask,hlp,show j+1 ≤ n-1 by omega] at hz'
  refine ⟨ha,hh,?_,?_,?_⟩
  · rw [h_internalY j hj hjn]
    simp only [internalYMask,adjacentMask,dot_add,dot_unit _ _ hp,dot_unit _ _ hlt,
      dot_unit _ _ hl]
    simp [internalYCharacter,unitBit,tailMask,hjp,hlp,
      show ¬j+1 ≤ j-1 by omega,show ¬j+1 ≤ j by omega,
      show j+1 ≤ n-1 by omega,CharTwo.add_self_eq_zero]
  · simp only [character,internalYMask,adjacentMask,dot_add,
      dot_unit _ _ hp,dot_unit _ _ hlt,dot_unit _ _ hl]
    simp [cutTail,show ¬j ≤ j-1 by omega,hjn]
  · norm_num [hw,pow_succ]

theorem pull_lastY {n : ℕ} (hn : 2 ≤ n) :
    PullI (unitBit n (n-1) + unitBit n (n-2)) (unitBit n (n-1)) I := by
  have hl : n-1 < n := by omega
  have hp : n-2 < n := by omega
  have hlp : n-1 ≠ n-2 := by omega
  have hpl : n-2 ≠ n-1 := by omega
  have hw := weight_pair (n:=n) (n-1) (n-2) hl hp hlp
  have hd : dot ((unitBit n (n-1) + unitBit n (n-2)) + unitBit n (n-1))
      (unitBit n (n-1) + unitBit n (n-2)) = 1 := by
    rw [h_lastY,dot_add,dot_unit _ _ hl,dot_unit _ _ hp]
    simp [unitBit,hlp]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_⟩
  · simp only [character,dot_add,dot_unit _ _ hl,dot_unit _ _ hp]
    simp [unitBit,hpl]
  · norm_num [hw]

theorem pull_localZ {n : ℕ} (hn : 2 ≤ n) (j : ℕ) (hj : j < n) :
    PullI (unitBit n (n-1)) (cutTail n j) 1 := by
  have hl : n-1 < n := by omega
  have hw := weight_unit (n:=n) (n-1) hl
  have hd : dot (unitBit n (n-1) + cutTail n j) (unitBit n (n-1)) = 1 := by
    rw [h_localZ j hj,dot_unit _ _ hl]
    simp [tailMask,show j ≤ n-1 by omega]
  refine ⟨nonzero_of_weight (by omega), nonzero_of_dot_one hd, hd, ?_, ?_⟩
  · simp only [character,dot_unit _ _ hl]
    simp [cutTail]
  · simp [hw]

def seedY {n : ℕ} (q : Bits n → Bit) (t : ℝ) (j : ℕ) : ℝ :=
  (pauliExpectation (BooleanLines.seed q t) (unitBit n j) (unitBit n j) I).re

def seedZ {n : ℕ} (q : Bits n → Bit) (t : ℝ) (j : ℕ) : ℝ :=
  (pauliExpectation (BooleanLines.seed q t) 0 (unitBit n j) 1).re

/-- 实际种子态所有局部 Pauli 分量等平方；不预设同号。 -/
def LocallyRegular {n : ℕ} (q : Bits n → Bit) : Prop :=
  ∀ᶠ t in nhds (0 : ℝ), ∀ j, j < n →
    seedX q t j ^ 2 = seedX q t 0 ^ 2 ∧
    seedY q t j ^ 2 = seedX q t 0 ^ 2 ∧
    seedZ q t j ^ 2 = seedX q t 0 ^ 2

private theorem cutTail_circuit (n j : ℕ) :
    cutTail n j = setBit (CircuitPauli.tailMask n j) (n-1) 0 := by
  rw [cutTail_eq_setBit]
  rfl

theorem seedX_last {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1) (t : ℝ) :
    seedX q t (n-1) =
      (coeffI (q (unitBit n (n-2))) (walsh q (tailMask n (n-2))).re).eval t / (2:ℝ)^n := by
  unfold seedX BooleanLines.seed
  have he := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z => normFactor n * raw q (anglePhase t) z) _ _ _ _ _ _
    (CircuitPauli.localX_last hn (fun z => normFactor n * raw q (anglePhase t) z))
  rw [he, normalized_expectation_re, raw_I_coeff q hq (pull_lastX hn), h_lastX hn]

theorem seedX_internal {n : ℕ} (q : Bits n → Bit) (hq : q 0 = 1)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (t : ℝ) :
    seedX q t j = (coeffII (q (adjacentMask n j))
      (walsh (derivative q (adjacentMask n j)) (adjacentMask n j)).re).eval t / (2:ℝ)^n := by
  unfold seedX BooleanLines.seed
  have he := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z => normFactor n * raw q (anglePhase t) z)
    (unitBit n j) 0 (adjacentMask n j) 0 1 1
    (by simpa [adjacentMask, show j ≠ 0 by omega, add_comm] using
      CircuitPauli.localX_beforeLast j hjn (fun z => normFactor n * raw q (anglePhase t) z))
  rw [he, normalized_expectation_re, raw_II_coeff q hq (pull_internalX j hj hjn)]
  simp

theorem seedZ_coeff {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (j : ℕ) (hj : j < n) (t : ℝ) :
    seedZ q t j =
      (coeffI (q (unitBit n (n-1))) (walsh q (tailMask n j)).re).eval t / (2:ℝ)^n := by
  unfold seedZ BooleanLines.seed
  have he := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z => normFactor n * raw q (anglePhase t) z)
    0 (unitBit n j) (unitBit n (n-1)) (cutTail n j) 1 1
    (by rw [cutTail_circuit]; exact CircuitPauli.localZ_table (by omega) j hj _)
  rw [he, normalized_expectation_re, raw_I_coeff q hq (pull_localZ hn j hj), h_localZ j hj]

theorem seedY_first {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1) (t : ℝ) :
    seedY q t 0 = (coeffI (q (unitBit n 0 + unitBit n (n-1)))
      (walsh q (tailMask n 1)).re).eval t / (2:ℝ)^n := by
  unfold seedY BooleanLines.seed
  have he := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z => normFactor n * raw q (anglePhase t) z)
    (unitBit n 0) (unitBit n 0) (unitBit n 0 + unitBit n (n-1)) (cutTail n 0) I I
    (by
      rw [cutTail_circuit]
      simpa using (CircuitPauli.localY_beforeLast 0 (by omega : 0<n-1)
        (fun z => normFactor n * raw q (anglePhase t) z)))
  rw [he, normalized_expectation_re, raw_I_coeff q hq (pull_firstY hn), h_firstY hn]

theorem seedY_internal {n : ℕ} (q : Bits n → Bit) (hq : q 0 = 1)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (t : ℝ) :
    seedY q t j = (coeffII (q (internalYMask n j))
      (walsh (derivative q (internalYMask n j)) (internalYCharacter n j)).re).eval t / (2:ℝ)^n := by
  unfold seedY BooleanLines.seed
  have he := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z => normFactor n * raw q (anglePhase t) z)
    (unitBit n j) (unitBit n j) (internalYMask n j) (cutTail n j) I I
    (by rw [cutTail_circuit]; simpa [internalYMask, adjacentMask, show j ≠ 0 by omega, add_comm]
      using CircuitPauli.localY_beforeLast j hjn (fun z => normFactor n * raw q (anglePhase t) z))
  rw [he, normalized_expectation_re, raw_II_coeff q hq (pull_internalY j hj hjn), h_internalY j hj hjn]

theorem seedY_last {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1) (t : ℝ) :
    seedY q t (n-1) = -(coeffI (q (unitBit n (n-1) + unitBit n (n-2)))
      (walsh q (unitBit n (n-2))).re).eval t / (2:ℝ)^n := by
  unfold seedY BooleanLines.seed
  have he := CircuitPauli.circuit_expectation (by omega : 0<n)
    (fun z => normFactor n * raw q (anglePhase t) z) _ _ _ _ _ _
    (CircuitPauli.localY_last hn (fun z => normFactor n * raw q (anglePhase t) z))
  rw [he]
  have hneg (f : Vec n) (a b : Bits n) :
      pauliExpectation f a b (-I) = -pauliExpectation f a b I := by
    simp [pauliExpectation, mul_neg, neg_mul, Finset.sum_neg_distrib]
  rw [hneg, Complex.neg_re, normalized_expectation_re,
    raw_I_coeff q hq (pull_lastY hn), h_lastY]
  ring

theorem coeffI_at_zero (s : Bit) (W : ℝ) : (coeffI s W).eval 0 = 2 := by
  simp [coeffI, Trig.eval]
  ring

theorem coeffII_at_zero (k : Bit) (V : ℝ) : (coeffII k V).eval 0 = 2 := by
  simp [coeffII, Trig.eval]
  ring

theorem coeff_eq_of_normalized_sq (n : ℕ) (p p' : Trig)
    (hp : p.eval 0 = 2) (hp' : p'.eval 0 = 2)
    (h : ∀ᶠ t in nhds (0 : ℝ), (p.eval t / (2:ℝ)^n)^2 = (p'.eval t / (2:ℝ)^n)^2) :
    p = p' := by
  apply Trig.eq_of_eventually_sq_eq p p' (by rw [hp]; norm_num) (by rw [hp']; norm_num)
  filter_upwards [h] with t ht
  have hd : (2:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp at ht
  exact ht

theorem coeffI_value_eq {s s' : Bit} {W W' : ℝ}
    (he : coeffI s W = coeffI s' W') : s = s' := by
  have hc := congrArg Trig.cosine he
  simp only [coeffI] at hc
  apply ZMod.val_injective 2
  have hr : (s.val : ℝ) = (s'.val : ℝ) := by linarith
  exact_mod_cast hr

theorem coeffII_value_eq {s s' : Bit} {W W' : ℝ}
    (he : coeffII s W = coeffII s' W') : s = s' := by
  have hc := congrArg Trig.sine he
  simp only [coeffII] at hc
  apply ZMod.val_injective 2
  have hr : (s.val : ℝ) = (s'.val : ℝ) := by linarith
  exact_mod_cast hr

def firstCoeff {n : ℕ} (q : Bits n → Bit) : Trig :=
  coeffI (q (unitBit n 0)) (walsh q (unitBit n 0)).re

theorem regular_coeff_Xlast {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) :
    coeffI (q (unitBit n (n-2))) (walsh q (tailMask n (n-2))).re = firstCoeff q := by
  apply coeff_eq_of_normalized_sq n _ _ (coeffI_at_zero _ _) (coeffI_at_zero _ _)
  filter_upwards [hr] with t ht
  simpa only [seedX_last hn q hq, seedX_first hn q hq, firstCoeff]
    using (ht (n-1) (by omega)).1

theorem regular_coeff_Yfirst {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) :
    coeffI (q (unitBit n 0 + unitBit n (n-1))) (walsh q (tailMask n 1)).re = firstCoeff q := by
  apply coeff_eq_of_normalized_sq n _ _ (coeffI_at_zero _ _) (coeffI_at_zero _ _)
  filter_upwards [hr] with t ht
  simpa only [seedY_first hn q hq, seedX_first hn q hq, firstCoeff]
    using (ht 0 (by omega)).2.1

theorem regular_coeff_Ylast {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) :
    coeffI (q (unitBit n (n-1) + unitBit n (n-2)))
      (walsh q (unitBit n (n-2))).re = firstCoeff q := by
  apply coeff_eq_of_normalized_sq n _ _ (coeffI_at_zero _ _) (coeffI_at_zero _ _)
  filter_upwards [hr] with t ht
  have h := (ht (n-1) (by omega)).2.1
  rw [seedY_last hn q hq, seedX_first hn q hq] at h
  simpa only [neg_div, neg_sq, firstCoeff] using h

theorem regular_coeff_Z {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) (j : ℕ) (hj : j < n) :
    coeffI (q (unitBit n (n-1))) (walsh q (tailMask n j)).re = firstCoeff q := by
  apply coeff_eq_of_normalized_sq n _ _ (coeffI_at_zero _ _) (coeffI_at_zero _ _)
  filter_upwards [hr] with t ht
  simpa only [seedZ_coeff hn q hq j hj, seedX_first hn q hq, firstCoeff] using (ht j hj).2.2

theorem regular_coeff_Xinternal {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) :
    coeffII (q (adjacentMask n j))
      (walsh (derivative q (adjacentMask n j)) (adjacentMask n j)).re = firstCoeff q := by
  apply coeff_eq_of_normalized_sq n _ _ (coeffII_at_zero _ _) (coeffI_at_zero _ _)
  filter_upwards [hr] with t ht
  simpa only [seedX_internal q hq j hj hjn, seedX_first hn q hq, firstCoeff]
    using (ht j (by omega)).1

theorem regular_coeff_Yinternal {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) :
    coeffII (q (internalYMask n j))
      (walsh (derivative q (internalYMask n j)) (internalYCharacter n j)).re = firstCoeff q := by
  apply coeff_eq_of_normalized_sq n _ _ (coeffII_at_zero _ _) (coeffI_at_zero _ _)
  filter_upwards [hr] with t ht
  simpa only [seedY_internal q hq j hj hjn, seedX_first hn q hq, firstCoeff]
    using (ht j (by omega)).2.1

/-- 邻域内的几何约束强制所有实参数上的实际 signed 分量一致。 -/
theorem regular_global_components {n : ℕ} (hn : 2 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) (t : ℝ) (j : ℕ) (hj : j < n) :
    seedX q t j = seedX q t 0 ∧
    seedY q t j = (if j = n-1 then -seedX q t 0 else seedX q t 0) ∧
    seedZ q t j = seedX q t 0 := by
  constructor
  · by_cases hl : j = n-1
    · subst j
      rw [seedX_last hn q hq, regular_coeff_Xlast hn q hq hr, seedX_first hn q hq] <;> rfl
    · by_cases h0 : j = 0
      · subst j; rfl
      · rw [seedX_internal q hq j (by omega) (by omega),
          regular_coeff_Xinternal hn q hq hr j (by omega) (by omega), seedX_first hn q hq] <;> rfl
  constructor
  · by_cases hl : j = n-1
    · subst j
      rw [seedY_last hn q hq, regular_coeff_Ylast hn q hq hr, seedX_first hn q hq]
      simp [firstCoeff] <;> ring
    · rw [ite_eq_right hl]
      by_cases h0 : j = 0
      · subst j
        rw [seedY_first hn q hq, regular_coeff_Yfirst hn q hq hr, seedX_first hn q hq] <;> rfl
      · rw [seedY_internal q hq j (by omega) (by omega),
          regular_coeff_Yinternal hn q hq hr j (by omega) (by omega), seedX_first hn q hq] <;> rfl
  · rw [seedZ_coeff hn q hq j hj, regular_coeff_Z hn q hq hr j hj, seedX_first hn q hq] <;> rfl

/-- 全部物理局部分量的等平方，给出统一的 I/II 翻转真值。 -/
theorem regular_pullback_values {n : ℕ} (hn : 3 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) :
    PullbackValues q (q (unitBit n 0)) (q (adjacentMask n 1)) := by
  have htwo := regular_coeff_Xinternal (by omega : 2 ≤ n) q hq hr 1 (by omega) (by omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact coeffI_value_eq (regular_coeff_Yfirst (by omega) q hq hr)
  · exact coeffI_value_eq (regular_coeff_Z (by omega) q hq hr 0 (by omega))
  · exact coeffI_value_eq (regular_coeff_Xlast (by omega) q hq hr)
  · simpa only [add_comm] using coeffI_value_eq (regular_coeff_Ylast (by omega) q hq hr)
  · intro j hj hjn
    exact coeffII_value_eq ((regular_coeff_Xinternal (by omega) q hq hr j hj hjn).trans htwo.symm)
  · intro j hj hjn
    exact coeffII_value_eq ((regular_coeff_Yinternal (by omega) q hq hr j hj hjn).trans htwo.symm)

theorem regular_walsh_first {n : ℕ} (hn : 3 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) :
    (walsh q (unitBit n 0)).re =
      2 * (((q (unitBit n 0)).val : ℝ) + ((q (adjacentMask n 1)).val : ℝ) - 1) := by
  have he := regular_coeff_Xinternal (by omega : 2 ≤ n) q hq hr 1 (by omega) (by omega)
  exact ((equal_coefficients _ _ _ _).mp he.symm).1

theorem regular_walsh_Z {n : ℕ} (hn : 3 ≤ n) (q : Bits n → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) (j : ℕ) (hj : j < n) :
    (walsh q (tailMask n j)).re =
      2 * (((q (unitBit n 0)).val : ℝ) + ((q (adjacentMask n 1)).val : ℝ) - 1) := by
  have he := (regular_coeff_Z (by omega) q hq hr j hj).trans
    (regular_coeff_Xinternal (by omega) q hq hr 1 (by omega) (by omega)).symm
  have hv := (regular_pullback_values hn q hq hr).localZ
  simpa only [hv] using ((equal_coefficients _ _ _ _).mp he).1

theorem actual_three_parameters_zero (q : Bits 3 → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) : q (unitBit 3 0) = 0 ∧ q (adjacentMask 3 1) = 0 := by
  exact three_qubit_physical_parameters_zero q _ _ hq
    (regular_pullback_values (by omega) q hq hr) (regular_walsh_first (by omega) q hq hr)
    (regular_walsh_Z (by omega) q hq hr)

theorem actual_three_trivial_support (q : Bits 3 → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) : q = qDelta := by
  obtain ⟨hs, hk⟩ := actual_three_parameters_zero q hq hr
  have hv := regular_pullback_values (by omega : 3 ≤ 3) q hq hr
  have hi := values3_I q _ _ hv
  have hii := values3_II q _ _ hv
  rw [hs] at hi
  rw [hk] at hii
  funext z
  have hp : z = 0 ∨ z = decode3 1 ∨ z = decode3 2 ∨ z = decode3 3 ∨
      z = decode3 4 ∨ z = decode3 5 ∨ z = decode3 6 ∨ z = decode3 7 := by
    revert z
    decide
  rcases hp with h | h | h | h | h | h | h | h
  · subst z; simp [hq]
  · subst z; rw [hi 1 (by decide)]; simp [qDelta, show decode3 1 ≠ 0 by decide]
  · subst z; rw [hi 2 (by decide)]; simp [qDelta, show decode3 2 ≠ 0 by decide]
  · subst z; rw [hi 3 (by decide)]; simp [qDelta, show decode3 3 ≠ 0 by decide]
  · subst z; rw [hi 4 (by decide)]; simp [qDelta, show decode3 4 ≠ 0 by decide]
  · subst z; rw [hi 5 (by decide)]; simp [qDelta, show decode3 5 ≠ 0 by decide]
  · subst z; rw [hii 6 (by decide)]; simp [qDelta, show decode3 6 ≠ 0 by decide]
  · subst z; rw [hii 7 (by decide)]; simp [qDelta, show decode3 7 ≠ 0 by decide]

theorem actual_four_sine_zero (q : Bits 4 → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) : q (adjacentMask 4 1) = 0 := by
  exact four_qubit_physical_sine_parameter_zero q _ _ hq
    (regular_pullback_values (by omega) q hq hr) (regular_walsh_Z (by omega) q hq hr)

theorem actual_three_constant (q : Bits 3 → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) (t : ℝ) : seedX q t 0 = 1/4 := by
  have hs := actual_three_parameters_zero q hq hr
  rw [actual_seed_four_law (by omega) q hq]
  · norm_num [hs.1, hs.2, law, Trig.eval]
  · filter_upwards [hr] with u hu
    exact (hu 1 (by omega)).1.symm

theorem actual_four_bound (q : Bits 4 → Bit) (hq : q 0 = 1)
    (hr : LocallyRegular q) (t : ℝ) : |seedX q t 0| ≤ 1/8 := by
  have hk := actual_four_sine_zero q hq hr
  have hreg : ∀ᶠ u in nhds (0:ℝ), seedX q u 0 ^ 2 = seedX q u 1 ^ 2 := by
    filter_upwards [hr] with u hu
    exact (hu 1 (by omega)).1.symm
  rw [actual_seed_four_law (by omega) q hq hreg, hk]
  have hb := scaled_no_sine_law_bound (1/8) (by norm_num) (q (unitBit 4 0)) t
  have he : (law (q (unitBit 4 0)) 0).eval t / (2:ℝ)^4 =
      (1/8) * ((1 - ((q (unitBit 4 0)).val : ℝ)) +
        ((q (unitBit 4 0)).val : ℝ) * Real.cos t) := by
    simp [law, Trig.eval]
    ring
  rw [he]
  exact hb

theorem regular_two_values (q : Bits 2 → Bit) (hq : q 0 = 1) (hr : LocallyRegular q) :
    PullbackValues q (q (unitBit 2 0)) 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact coeffI_value_eq (regular_coeff_Yfirst (by omega) q hq hr)
  · exact coeffI_value_eq (regular_coeff_Z (by omega) q hq hr 0 (by omega))
  · exact coeffI_value_eq (regular_coeff_Xlast (by omega) q hq hr)
  · simpa only [add_comm] using coeffI_value_eq (regular_coeff_Ylast (by omega) q hq hr)
  · intro j hj hjn; omega
  · intro j hj hjn; omega

theorem actual_two_classification (q : Bits 2 → Bit) (hq : q 0 = 1) (hr : LocallyRegular q) :
    q = (fun z => if z = 0 then 1 else 0) ∨ q = (fun _ => 1) :=
  two_qubit_support_dichotomy q _ _ hq (regular_two_values q hq hr)

theorem actual_two_law (q : Bits 2 → Bit) (hq : q 0 = 1) (hr : LocallyRegular q) (t : ℝ) :
    seedX q t 0 = (1/2) * ((1 - ((q (unitBit 2 0)).val : ℝ)) +
      ((q (unitBit 2 0)).val : ℝ) * Real.cos t) := by
  rw [seedX_first (by omega) q hq,
    two_qubit_walsh_first q _ _ hq (regular_two_values q hq hr)]
  simp [coeffI, Trig.eval]
  ring

theorem actual_two_bound (q : Bits 2 → Bit) (hq : q 0 = 1) (hr : LocallyRegular q) (t : ℝ) :
    |seedX q t 0| ≤ 1/2 := by
  rw [actual_two_law q hq hr]
  exact scaled_no_sine_law_bound (1/2) (by norm_num) _ t

theorem delta_coeffI {n : ℕ} {a b : Bits n} {c : ℂ} (hp : PullI a b c) (t : ℝ) :
    (coeffI (qDelta a) (walsh qDelta (a+b)).re).eval t = 2 := by
  rw [← raw_I_coeff qDelta (qDelta_zero n) hp]
  exact delta_I_value hp t

theorem delta_coeffII {n : ℕ} {a b : Bits n} {c : ℂ} (hp : PullII a b c) (t : ℝ) :
    (coeffII (qDelta a) (walsh (derivative qDelta a) (a+b)).re).eval t = 2 := by
  rw [← raw_II_coeff qDelta (qDelta_zero n) hp]
  exact delta_II_value hp t

/-- 同一指定基点在所有 n≥2 的实际局部三分量；用于低维界的达到性。 -/
theorem delta_seed_components {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (j : ℕ) (hj : j < n) :
    seedX (qDelta : Bits n → Bit) t j = 2/(2:ℝ)^n ∧
    seedY (qDelta : Bits n → Bit) t j =
      (if j = n-1 then -(2/(2:ℝ)^n) else 2/(2:ℝ)^n) ∧
    seedZ (qDelta : Bits n → Bit) t j = 2/(2:ℝ)^n := by
  have hq := qDelta_zero n
  constructor
  · by_cases hl : j = n-1
    · subst j
      rw [seedX_last hn qDelta hq, ← h_lastX hn, delta_coeffI (pull_lastX hn)]
    · by_cases h0 : j = 0
      · subst j
        rw [seedX_first hn qDelta hq]
        have h := delta_coeffI (first_pullI (by omega : 0<n)) t
        simpa only [add_zero] using congrArg (fun x : ℝ => x/(2:ℝ)^n) h
      · rw [seedX_internal qDelta hq j (by omega) (by omega)]
        have h := delta_coeffII (pull_internalX (n:=n) j (by omega) (by omega)) t
        simpa only [add_zero] using congrArg (fun x : ℝ => x/(2:ℝ)^n) h
  constructor
  · by_cases hl : j = n-1
    · subst j
      rw [seedY_last hn qDelta hq]
      have he := delta_coeffI (pull_lastY hn) t
      rw [h_lastY] at he
      rw [he]
      simp
      ring
    · rw [ite_eq_right hl]
      by_cases h0 : j = 0
      · subst j
        rw [seedY_first hn qDelta hq, ← h_firstY hn, delta_coeffI (pull_firstY hn)]
      · rw [seedY_internal qDelta hq j (by omega) (by omega),
          ← h_internalY j (by omega) (by omega),
          delta_coeffII (pull_internalY j (by omega) (by omega))]
  · rw [seedZ_coeff hn qDelta hq j hj, ← h_localZ j hj, delta_coeffI (pull_localZ hn j hj)]

theorem delta_locallyRegular {n : ℕ} (hn : 2 ≤ n) :
    LocallyRegular (qDelta : Bits n → Bit) := by
  apply Filter.Eventually.of_forall
  intro t j hj
  obtain ⟨hx, hy, hz⟩ := delta_seed_components hn t j hj
  have hx0 := (delta_seed_components hn t 0 (by omega)).1
  rw [hx, hy, hz, hx0]
  constructor
  · rfl
  constructor
  · split_ifs <;> ring
  · rfl

theorem delta_locally_regular {n : ℕ} (hn : 2 ≤ n) :
    LocallyRegular (qDelta : Bits n → Bit) := delta_locallyRegular hn

end UnifiedEJM.LowBooleanPhysical


