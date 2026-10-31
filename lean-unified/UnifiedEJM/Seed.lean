import UnifiedEJM.LocalExpectation
import UnifiedEJM.Background
import OddEJM.Orthonormal
import OddEJM.Pauli
import UnifiedEJM.Masks
import UnifiedEJM.Walsh

namespace UnifiedEJM
open OddEJM

open scoped BigOperators
open Complex

/-- 原始期望分子除以计算基维数，恰为公共Bloch分量。 -/
theorem normalized_raw_expectation {n : ℕ} (hn : 0 < n) (t : ℝ)
    (a b : Bits n) (c : ℂ)
    (hraw : pauliExpectation (rawPhase (anglePhase t)) a b c =
      ((2 * (1 - Real.sin t) : ℝ) : ℂ)) :
    pauliExpectation (fun z => normFactor n * rawPhase (anglePhase t) z) a b c =
      (componentScale n t : ℂ) := by
  rw [pauliExpectation_scale, hraw]
  have hp : (2 : ℂ) ^ n = (2 : ℂ) ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hc := normFactor_card n
  rw [hp] at hc
  have hd : (2 : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [componentScale, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  apply (eq_div_iff hd).mpr
  calc
    _ = (star (normFactor n) * normFactor n * ((2 : ℂ) ^ (n - 1) * 2)) *
        (1 - (Real.sin t : ℂ)) := by ring
    _ = 1 - (Real.sin t : ℂ) := by rw [hc, one_mul]

theorem normalized_classI {n : ℕ} (hn : 0 < n) (t : ℝ)
    (a b : Bits n) (c : ℂ) (h : MaskFacts.ClassI a b c)
    (hQ : walsh (fun z : Bits n => Q20 (compress z)) (a + b) = 0) :
    pauliExpectation (fun z => normFactor n * rawPhase (anglePhase t) z) a b c =
      (componentScale n t : ℂ) := by
  apply normalized_raw_expectation hn t a b c
  apply rawPhase_expectation_classI t c a b h.ha h.hc
  · exact background_pauli_zero_classI _ _ _ _ h.hh h.hd hQ
  · exact h.hg
  · exact h.hq

theorem normalized_classII {n : ℕ} (hn : 0 < n) (t : ℝ)
    (a b : Bits n) (c : ℂ) (h : MaskFacts.ClassII a b c)
    (hQ : walsh (derivative (fun z : Bits n => Q20 (compress z)) a) (a + b) = 0) :
    pauliExpectation (fun z => normFactor n * rawPhase (anglePhase t) z) a b c =
      (componentScale n t : ℂ) := by
  apply normalized_raw_expectation hn t a b c
  apply rawPhase_expectation_classII t c a b h.ha h.hc
  · apply background_pauli_zero_classII _ _ _ _ h.hh h.hd
    · simpa only [mul_comm] using anglePhase_star_mul t
    · exact hQ
  · exact h.hg
  · exact h.hq

theorem pauliExpectation_neg_phase {n : ℕ} (f : Vec n) (a b : Bits n) (c : ℂ) :
    pauliExpectation f a b (-c) = -pauliExpectation f a b c := by
  simp [pauliExpectation, mul_neg, neg_mul, Finset.sum_neg_distrib]

private theorem cutTail_circuit (n j : ℕ) :
    MaskFacts.cutTail n j = setBit (CircuitPauli.tailMask n j) (n - 1) 0 := by
  rw [MaskFacts.cutTail_eq_setBit]
  rfl

/-- 任意 n≥5的实际种子态，每个物理X期望都有相同的解析值。 -/
theorem seed_localX {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (j : ℕ) (hj : j < n) :
    pauliExpectation (seed n t) (unitBit n j) 0 1 = (componentScale n t : ℂ) := by
  let f : Vec n := fun z => normFactor n * rawPhase (anglePhase t) z
  by_cases hjlast : j = n - 1
  · subst j
    calc
      _ = pauliExpectation f (unitBit n (n - 2)) (unitBit n (n - 1)) 1 :=
        CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
          (CircuitPauli.localX_last (by omega) f)
      _ = _ := by
        apply normalized_classI (by omega) t _ _ _ (MaskFacts.lastX hn)
        rw [MaskFacts.h_lastX (by omega)]
        exact walsh_Q_tail hn (n - 2) (by omega)
  · have hjn : j < n - 1 := by omega
    by_cases hjzero : j = 0
    · subst j
      calc
        _ = pauliExpectation f (unitBit n 0) 0 1 := by
          apply CircuitPauli.circuit_expectation (by omega) f
          simpa using CircuitPauli.localX_beforeLast 0 (by omega) f
        _ = _ := by
          apply normalized_classI (by omega) t _ _ _ (MaskFacts.firstX hn)
          change walsh q (unitBit n 0 + 0) = 0
          rw [add_zero]
          exact walsh_Q_first hn
    · have hjpos : 1 ≤ j := by omega
      calc
        _ = pauliExpectation f (adjacentMask n j) 0 1 := by
          apply CircuitPauli.circuit_expectation (by omega) f
          simpa only [ite_eq_right hjzero, adjacentMask, add_comm] using
            CircuitPauli.localX_beforeLast j hjn f
        _ = _ := by
          apply normalized_classII (by omega) t _ _ _ (MaskFacts.internalX hn j hjpos hjn)
          change walsh (derivative q (adjacentMask n j)) (adjacentMask n j + 0) = 0
          rw [add_zero]
          exact walsh_DQ_X hn j hjpos hjn

/-- 任意 n≥5的实际种子态，每个物理Z期望都有相同的解析值。 -/
theorem seed_localZ {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (j : ℕ) (hj : j < n) :
    pauliExpectation (seed n t) 0 (unitBit n j) 1 = (componentScale n t : ℂ) := by
  let f : Vec n := fun z => normFactor n * rawPhase (anglePhase t) z
  calc
    _ = pauliExpectation f (unitBit n (n - 1)) (MaskFacts.cutTail n j) 1 := by
      apply CircuitPauli.circuit_expectation (by omega) f
      rw [cutTail_circuit]
      exact CircuitPauli.localZ_table (by omega) j hj f
    _ = _ := by
      apply normalized_classI (by omega) t _ _ _ (MaskFacts.localZ hn j hj)
      rw [MaskFacts.h_localZ j hj]
      exact walsh_Q_tail hn j hj

/-- 末位Hadamard使最后一个标准Y期望带负号。 -/
theorem seed_localY {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (j : ℕ) (hj : j < n) :
    pauliExpectation (seed n t) (unitBit n j) (unitBit n j) I =
      if j = n - 1 then -(componentScale n t : ℂ) else (componentScale n t : ℂ) := by
  let f : Vec n := fun z => normFactor n * rawPhase (anglePhase t) z
  by_cases hjlast : j = n - 1
  · subst j
    rw [ite_eq_left rfl]
    calc
      _ = pauliExpectation f (unitBit n (n - 1) + unitBit n (n - 2))
          (unitBit n (n - 1)) (-I) :=
        CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
          (CircuitPauli.localY_last (by omega) f)
      _ = -pauliExpectation f (unitBit n (n - 1) + unitBit n (n - 2))
          (unitBit n (n - 1)) I := pauliExpectation_neg_phase _ _ _ _
      _ = _ := by
        congr 1
        apply normalized_classI (by omega) t _ _ _ (MaskFacts.lastY hn)
        rw [MaskFacts.h_lastY]
        exact walsh_Q_penultimate hn
  · rw [ite_eq_right hjlast]
    have hjn : j < n - 1 := by omega
    by_cases hjzero : j = 0
    · subst j
      calc
        _ = pauliExpectation f (unitBit n 0 + unitBit n (n - 1))
            (MaskFacts.cutTail n 0) I := by
          apply CircuitPauli.circuit_expectation (by omega) f
          rw [cutTail_circuit]
          simpa using
            CircuitPauli.localY_beforeLast 0 (by omega) f
        _ = _ := by
          apply normalized_classI (by omega) t _ _ _ (MaskFacts.firstY hn)
          rw [MaskFacts.h_firstY (by omega)]
          exact walsh_Q_tail hn 1 (by omega)
    · have hjpos : 1 ≤ j := by omega
      calc
        _ = pauliExpectation f (internalYMask n j) (MaskFacts.cutTail n j) I := by
          apply CircuitPauli.circuit_expectation (by omega) f
          rw [cutTail_circuit]
          simpa only [ite_eq_right hjzero, internalYMask, adjacentMask, add_comm] using
            CircuitPauli.localY_beforeLast j hjn f
        _ = _ := by
          apply normalized_classII (by omega) t _ _ _ (MaskFacts.internalY hn j hjpos hjn)
          rw [MaskFacts.h_internalY j hjpos hjn]
          exact walsh_DQ_Y hn j hjpos hjn

end UnifiedEJM

