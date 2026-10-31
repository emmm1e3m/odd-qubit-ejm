import UnifiedEJM.SixCertificate
import UnifiedEJM.EvenRaw
import OddEJM.Pauli

namespace UnifiedEJM.SixCertificate
open OddEJM Complex
open scoped BigOperators

def A (p : Fin 18) : Bits 6 := decode6 (flipCode p)
def B (p : Fin 18) : Bits 6 := A p + decode6 (charCode p)
def C (p : Fin 18) : ℂ := if 6 ≤ p.val ∧ p.val < 12 then I else 1

def rowX (j : Fin 6) : Fin 18 := ⟨j.val, by omega⟩
def rowY (j : Fin 6) : Fin 18 := ⟨6+j.val, by omega⟩
def rowZ (j : Fin 6) : Fin 18 := ⟨12+j.val, by omega⟩

theorem X_masks : ∀ j : Fin 6,
    A (rowX j) = setBit (difference (unitBit 6 j.val)) 5 0 ∧
    B (rowX j) = setBit 0 5 (coord (difference (unitBit 6 j.val)) 5) := by decide

theorem Y_masks : ∀ j : Fin 6,
    A (rowY j) = setBit (difference (unitBit 6 j.val)) 5 1 ∧
    B (rowY j) = setBit (CircuitPauli.tailMask 6 j.val) 5
      (coord (difference (unitBit 6 j.val)) 5) := by decide

theorem Z_masks : ∀ j : Fin 6,
    A (rowZ j) = setBit 0 5 1 ∧
    B (rowZ j) = setBit (CircuitPauli.tailMask 6 j.val) 5 0 := by decide

lemma Y_phase : ∀ j : Fin 6,
    I * bitSign (coord (difference (unitBit 6 j.val)) 5) =
      if j.val=5 then -I else I := by
  intro j
  fin_cases j <;> norm_num [coord, difference, unitBit, bitSign]

lemma expectation_neg (f : Vec 6) (a b : Bits 6) (c : ℂ) :
    pauliExpectation f a b (-c) = -pauliExpectation f a b c := by
  simp [pauliExpectation, mul_neg, neg_mul, Finset.sum_neg_distrib]

/-- 固定整数掩码确为原电路的每个实际X拉回。 -/
theorem pull_X (j : Fin 6) (f : Vec 6) :
    pauliExpectation (circuit f) (unitBit 6 j.val) 0 1 =
      pauliExpectation f (A (rowX j)) (B (rowX j)) (C (rowX j)) := by
  rw [(X_masks j).1, (X_masks j).2]
  have hc : C (rowX j) = 1 := by simp [C, rowX, show ¬6 ≤ j.val by omega]
  rw [hc]
  exact CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
    (CircuitPauli.localX_pullback (by omega) j.val f)

/-- 末位signed Y取反，全部18项表仍保持论文的统一符号。 -/
theorem pull_Y (j : Fin 6) (f : Vec 6) :
    (if j.val=5 then -pauliExpectation (circuit f) (unitBit 6 j.val) (unitBit 6 j.val) I
     else pauliExpectation (circuit f) (unitBit 6 j.val) (unitBit 6 j.val) I) =
      pauliExpectation f (A (rowY j)) (B (rowY j)) (C (rowY j)) := by
  rw [(Y_masks j).1, (Y_masks j).2]
  have hc : C (rowY j) = I := by simp [C, rowY, show 6+j.val < 12 by omega]
  rw [hc]
  have ht := CircuitPauli.circuit_expectation (by omega : 0<6) f _ _ _ _ _ _
    (CircuitPauli.localY_pullback (by omega) j.val j.isLt f)
  change pauliExpectation (circuit f) _ _ _ =
    pauliExpectation f (setBit (difference (unitBit 6 j.val)) 5 1)
      (setBit (CircuitPauli.tailMask 6 j.val) 5 (coord (difference (unitBit 6 j.val)) 5))
      (I * bitSign (coord (difference (unitBit 6 j.val)) 5)) at ht
  rw [Y_phase] at ht
  by_cases hj : j.val=5
  · simp only [hj, ite_true, expectation_neg] at ht ⊢
    rw [ht, neg_neg]
  · simp only [hj, ite_false] at ht ⊢
    exact ht

theorem pull_Z (j : Fin 6) (f : Vec 6) :
    pauliExpectation (circuit f) 0 (unitBit 6 j.val) 1 =
      pauliExpectation f (A (rowZ j)) (B (rowZ j)) (C (rowZ j)) := by
  rw [(Z_masks j).1, (Z_masks j).2]
  have hc : C (rowZ j) = 1 := by simp [C, rowZ]
  rw [hc]
  exact CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
    (CircuitPauli.localZ_pullback (by omega) j.val j.isLt f)

def weightTable : Fin 18 → ℕ := ![1,2,2,2,2,1,2,3,3,3,3,2,1,1,1,1,1,1]
theorem weight_checked : ∀ p : Fin 18, weight (A p) = weightTable p := by decide

theorem dot_checked : ∀ p : Fin 18, dot (B p) (A p) =
    if 6 ≤ p.val ∧ p.val < 12 then (1 : Bit) else 0 := by decide

/-- 三种相位因子由拉回Pauli与Hamming相位直接算出。 -/
theorem gamma_checked : ∀ p : Fin 18,
    C p * star (I ^ weight (A p)) = gamma p := by
  intro p
  rw [weight_checked]
  fin_cases p <;> norm_num [C, gamma, weightTable, Complex.star_def]

theorem nonzero_flip : ∀ p : Fin 18, A p ≠ 0 := by decide

theorem hermitian_checked : ∀ p : Fin 18, C p * character (B p) (A p) = star (C p) := by
  intro p
  unfold character
  rw [dot_checked]
  fin_cases p <;> norm_num [C, bitSign, Complex.star_def]
theorem character_mask (p : Fin 18) : A p + B p = decode6 (charCode p) := by
  unfold B
  rw [← add_assoc, bits_add_self, zero_add]

/-- 联合颜色表左侧是实际未归一化背景振幅的Pauli期望。 -/
theorem actual_background (p : Fin 18) (phases : Fin 4 → ℂ) :
    pauliExpectation (fun z => I ^ weight z * phases (colour z)) (A p) (B p) (C p) =
      gamma p * colourSum p phases := by
  rw [EvenRaw.phase_background_sum, gamma_checked, character_mask]
  rfl

end UnifiedEJM.SixCertificate

