import UnifiedEJM.PhysicsBackgroundTables

open OddEJM Complex
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer.SparseCertificate
open PhysicsFinite PhysicsEntanglement GraphBackground

/-- 真实背景的512种逻辑相关函数由九类整数多项式给出。 -/
theorem physicalCorrelation_fastTrig {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (d k : Bits 4) :
    Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k) =
      trigEval (fastTrig (decide (n % 2 ≠ 0)) d k) t / 64 := by
  rw [physicalCorrelation_trig hn, squaredCoeffs_trig]
  simp [trigEval]
  ring

/-- 任意支撑多重集的真实终端配对，p=q=0之外的项不作贡献。 -/
theorem terminal_pairing (support : Support) (w : ℚ) (score : Logical → Logical → ℝ) :
    (∑ d, ∑ k, (decode support w d (k, 0, 0) : ℝ) * score d k) =
      (w : ℝ) * (support.map (fun x =>
        if x.2.2.1 = 0 ∧ x.2.2.2 = 0 then score x.1 x.2.1 else 0)).sum := by
  induction support using Multiset.induction_on with
  | empty => simp
  | @cons x xs ih =>
      have hs : x ::ₘ xs = ({x} : Support) + xs := by simp
      rw [hs]
      simp only [decode_add, Rat.cast_add, add_mul, Finset.sum_add_distrib,
        Multiset.map_add, Multiset.sum_add, mul_add]
      rw [ih]
      congr 1
      rcases x with ⟨d, k, p, q⟩
      by_cases hp : p = 0 <;> by_cases hq : q = 0 <;>
        simp [decode_singleton, Prod.mk.injEq, hp, hq, eq_comm, ite_and,
          apply_ite, mul_ite, ite_mul]

/-- 终端三角系数由实际支撑逐项求和，不使用Python给出的numerator。 -/
def terminalCoeffs (odd : Bool) (support : Support) (j : Fin 5) : ℤ :=
  (support.map (fun x => if x.2.2.1 = 0 ∧ x.2.2.2 = 0
    then fastTrig odd x.1 x.2.1 j else 0)).sum

theorem terminalCoeffs_trig (odd : Bool) (support : Support) (t : ℝ) :
    trigEval (terminalCoeffs odd support) t =
      (support.map (fun x => if x.2.2.1 = 0 ∧ x.2.2.2 = 0
        then trigEval (fastTrig odd x.1 x.2.1) t else 0)).sum := by
  induction support using Multiset.induction_on with
  | empty => simp [terminalCoeffs, trigEval]
  | @cons x xs ih =>
      by_cases h : x.2.2.1 = 0 ∧ x.2.2.2 = 0
      · have hc : terminalCoeffs odd (x ::ₘ xs) =
            fun j => fastTrig odd x.1 x.2.1 j + terminalCoeffs odd xs j := by
          funext j
          simp [terminalCoeffs, h]
        rw [hc]
        simp only [Multiset.map_cons, Multiset.sum_cons, if_pos h]
        rw [← ih]
        simp only [trigEval, Int.cast_add]
        ring
      · have hc : terminalCoeffs odd (x ::ₘ xs) = terminalCoeffs odd xs := by
          funext j
          simp [terminalCoeffs, h]
        rw [hc]
        simpa only [Multiset.map_cons, Multiset.sum_cons, if_neg h, zero_add] using ih

theorem terminal_physical_formula {n : ℕ} (hn : 5 ≤ n) (support : Support)
    (w : ℚ) (t : ℝ) :
    (∑ d, ∑ k, (decode support w d (k, 0, 0) : ℝ) *
      Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k)) =
      (w : ℝ) * trigEval (terminalCoeffs (decide (n % 2 ≠ 0)) support) t / 64 := by
  rw [terminal_pairing]
  simp_rw [physicalCorrelation_fastTrig hn]
  rw [terminalCoeffs_trig]
  have hs : (support.map (fun x =>
      if x.2.2.1 = 0 ∧ x.2.2.2 = 0
      then trigEval (fastTrig (decide (n % 2 ≠ 0)) x.1 x.2.1) t / 64 else 0)).sum =
      (support.map (fun x => if x.2.2.1 = 0 ∧ x.2.2.2 = 0
      then trigEval (fastTrig (decide (n % 2 ≠ 0)) x.1 x.2.1) t else 0)).sum / 64 := by
    induction support using Multiset.induction_on with
    | empty => simp
    | @cons x xs ih =>
        by_cases h : x.2.2.1 = 0 ∧ x.2.2.2 = 0
        · simp only [Multiset.map_cons, Multiset.sum_cons, if_pos h, add_div, ih]
        · simp only [Multiset.map_cons, Multiset.sum_cons, if_neg h, zero_add, ih]
  rw [hs]
  ring

/-- 证书只要求三个整数系数的精确界；系数到真实|S|²的链条已在上面证明。 -/
theorem terminal_bound_of_integer_certificate {n : ℕ} (hn : 5 ≤ n)
    (support : Support) (E : ℕ)
    (hbound : 8 * trigL1 (terminalCoeffs (decide (n % 2 ≠ 0)) support) ≤
      3 * (64 * (2 : ℤ) ^ E)) (t : ℝ) :
    (∑ d, ∑ k, (decode support (1 / (2 : ℚ) ^ E) d (k, 0, 0) : ℝ) *
      Complex.normSq (codeCorrelation (physicalCoefficients n (anglePhase t)) d k)) ≤
      3 / 8 := by
  rw [terminal_physical_formula hn]
  have hpoly := trigEval_le_L1 (terminalCoeffs (decide (n % 2 ≠ 0)) support) t
  have hnum : 8 * (trigL1 (terminalCoeffs (decide (n % 2 ≠ 0)) support) : ℝ) ≤
      3 * (64 * (2 : ℝ) ^ E) := by exact_mod_cast hbound
  have hp : (0 : ℝ) < 2 ^ E := pow_pos (by norm_num) _
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  rw [one_div_mul_eq_div, div_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ E * 64)).mpr
  nlinarith

end UnifiedEJM.WeightedTransfer.SparseCertificate

