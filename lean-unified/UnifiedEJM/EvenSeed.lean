import UnifiedEJM.EvenRaw
import UnifiedEJM.JointWalsh
import UnifiedEJM.Physical
import UnifiedEJM.EvenGeometry

namespace UnifiedEJM.EvenFamily
open OddEJM Complex
open UnifiedEJM.EvenWalsh
open scoped BigOperators

noncomputable def diagonal (n : ℕ) (α β : ℝ) : Vec n :=
  EvenRaw.raw qA UnifiedEJM.q (anglePhase α) (anglePhase β)
noncomputable def seed (n : ℕ) (α β : ℝ) : Vec n := Physical.seed (diagonal n α β)
noncomputable def measurement (n : ℕ) (α β : ℝ) (label : Bits n) : Vec n :=
  Physical.measurement (diagonal n α β) label
noncomputable def component (n : ℕ) (α β : ℝ) : ℝ :=
  (Real.cos α - Real.sin β) / (2 : ℝ) ^ (n-1)

lemma expectation_neg {n : ℕ} (f : Vec n) (a b : Bits n) (c : ℂ) :
    pauliExpectation f a b (-c) = -pauliExpectation f a b c := by
  simp [pauliExpectation, mul_neg, neg_mul, Finset.sum_neg_distrib]

lemma angle_unit (t : ℝ) : anglePhase t * star (anglePhase t) = 1 := by
  simpa only [mul_comm] using anglePhase_star_mul t

theorem diagonal_unit (n : ℕ) (α β : ℝ) (z : Bits n) :
    star (diagonal n α β z) * diagonal n α β z = 1 := by
  have hn := EvenRaw.raw_norm qA UnifiedEJM.q (anglePhase α) (anglePhase β)
    (anglePhase_norm α) (anglePhase_norm β) z
  simpa only [Complex.star_def, diagonal, hn, one_pow, Complex.ofReal_one] using
    Complex.conj_mul' (diagonal n α β z)

@[simp] theorem diagonal_origin (n : ℕ) (α β : ℝ) : diagonal n α β 0 = 1 := by
  simp [diagonal]

lemma normalized_classI {n : ℕ} (hn : 0 < n) (α β : ℝ)
    (a b : Bits n) (c : ℂ) (h : UnifiedEJM.MaskFacts.ClassI a b c)
    (hbg : pauliExpectation (jointBackground (anglePhase α) (anglePhase β)) a b c = 0)
    (hqa : qA a = 1) :
    pauliExpectation (fun z => normFactor n * diagonal n α β z) a b c =
      (component n α β : ℂ) := by
  apply EvenRaw.normalized_expectation hn _ _ _ _ _
  exact EvenRaw.raw_expectation_classI qA UnifiedEJM.q α β a b c
    (qA_zero n) (q_zero n) h.ha h.hc hbg h.hg hqa h.hq

lemma normalized_classII {n : ℕ} (hn : 0 < n) (α β : ℝ)
    (a b : Bits n) (c : ℂ) (h : UnifiedEJM.MaskFacts.ClassII a b c)
    (hbg : pauliExpectation (jointBackground (anglePhase α) (anglePhase β)) a b c = 0)
    (hqa : qA a = 0) :
    pauliExpectation (fun z => normFactor n * diagonal n α β z) a b c =
      (component n α β : ℂ) := by
  apply EvenRaw.normalized_expectation hn _ _ _ _ _
  exact EvenRaw.raw_expectation_classII qA UnifiedEJM.q α β a b c
    (qA_zero n) (q_zero n) h.ha h.hc hbg h.hg hqa h.hq

private theorem cutTail_circuit (n j : ℕ) :
    UnifiedEJM.MaskFacts.cutTail n j = setBit (CircuitPauli.tailMask n j) (n-1) 0 := by
  rw [UnifiedEJM.MaskFacts.cutTail_eq_setBit]
  rfl

/-- 全部偶数n≥8的实际种子X期望，混合背景假设已完全消去。 -/
theorem seed_localX {n : ℕ} (hn : 8 ≤ n) (he : Even n) (α β : ℝ)
    (j : ℕ) (hj : j < n) :
    pauliExpectation (seed n α β) (unitBit n j) 0 1 = (component n α β : ℂ) := by
  let f : Vec n := fun z => normFactor n * diagonal n α β z
  have hn5 : 5 ≤ n := by omega
  by_cases hjlast : j = n-1
  · subst j
    calc
      _ = pauliExpectation f (unitBit n (n-2)) (unitBit n (n-1)) 1 :=
        CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
          (CircuitPauli.localX_last (by omega) f)
      _ = _ := normalized_classI (by omega) α β _ _ _ (UnifiedEJM.MaskFacts.lastX hn5)
        (background_lastX_zero hn5 _ _ (angle_unit α)) (qA_of_ezero ezero_penultimate)
  · have hjn : j < n-1 := by omega
    by_cases hjzero : j = 0
    · subst j
      calc
        _ = pauliExpectation f (unitBit n 0) 0 1 := by
          apply CircuitPauli.circuit_expectation (by omega) f
          simpa using CircuitPauli.localX_beforeLast 0 (by omega) f
        _ = _ := normalized_classI (by omega) α β _ _ _ (UnifiedEJM.MaskFacts.firstX hn5)
          (background_firstX_zero hn5 _ _ (angle_unit α)) (qA_of_ezero ezero_first)
    · have hjpos : 1 ≤ j := by omega
      calc
        _ = pauliExpectation f (adjacentMask n j) 0 1 := by
          apply CircuitPauli.circuit_expectation (by omega) f
          simpa only [ite_eq_right hjzero, adjacentMask, add_comm] using
            CircuitPauli.localX_beforeLast j hjn f
        _ = _ := normalized_classII (by omega) α β _ _ _
          (UnifiedEJM.MaskFacts.internalX hn5 j hjpos hjn)
          (background_internalX_zero hn he j hjpos hjn _ _ (angle_unit β))
          (qA_adjacent hn5 he j hjpos hjn)

/-- 全部实际种子Z期望。 -/
theorem seed_localZ {n : ℕ} (hn : 8 ≤ n) (_he : Even n) (α β : ℝ)
    (j : ℕ) (hj : j < n) :
    pauliExpectation (seed n α β) 0 (unitBit n j) 1 = (component n α β : ℂ) := by
  let f : Vec n := fun z => normFactor n * diagonal n α β z
  have hn5 : 5 ≤ n := by omega
  calc
    _ = pauliExpectation f (unitBit n (n-1)) (UnifiedEJM.MaskFacts.cutTail n j) 1 := by
      apply CircuitPauli.circuit_expectation (by omega) f
      rw [cutTail_circuit]
      exact CircuitPauli.localZ_table (by omega) j hj f
    _ = _ := normalized_classI (by omega) α β _ _ _ (UnifiedEJM.MaskFacts.localZ hn5 j hj)
      (background_localZ_zero hn5 j hj _ _ (angle_unit α))
      (qA_of_ezero (ezero_last (by omega)))

/-- 末位Y的负号由原始Hadamard/CNOT门共轭证明。 -/
theorem seed_localY {n : ℕ} (hn : 8 ≤ n) (he : Even n) (α β : ℝ)
    (j : ℕ) (hj : j < n) :
    pauliExpectation (seed n α β) (unitBit n j) (unitBit n j) I =
      if j = n-1 then -(component n α β : ℂ) else (component n α β : ℂ) := by
  let f : Vec n := fun z => normFactor n * diagonal n α β z
  have hn5 : 5 ≤ n := by omega
  by_cases hjlast : j = n-1
  · subst j
    rw [ite_eq_left rfl]
    calc
      _ = pauliExpectation f (unitBit n (n-1) + unitBit n (n-2))
          (unitBit n (n-1)) (-I) :=
        CircuitPauli.circuit_expectation (by omega) f _ _ _ _ _ _
          (CircuitPauli.localY_last (by omega) f)
      _ = -pauliExpectation f (unitBit n (n-1) + unitBit n (n-2))
          (unitBit n (n-1)) I := expectation_neg _ _ _ _
      _ = _ := by
        congr 1
        exact normalized_classI (by omega) α β _ _ _ (UnifiedEJM.MaskFacts.lastY hn5)
          (background_lastY_zero hn5 _ _ (angle_unit α))
          (qA_of_ezero (ezero_add (ezero_last (by omega)) ezero_penultimate))
  · rw [ite_eq_right hjlast]
    have hjn : j < n-1 := by omega
    by_cases hjzero : j = 0
    · subst j
      calc
        _ = pauliExpectation f (unitBit n 0 + unitBit n (n-1))
            (UnifiedEJM.MaskFacts.cutTail n 0) I := by
          apply CircuitPauli.circuit_expectation (by omega) f
          rw [cutTail_circuit]
          simpa using CircuitPauli.localY_beforeLast 0 (by omega) f
        _ = _ := normalized_classI (by omega) α β _ _ _ (UnifiedEJM.MaskFacts.firstY hn5)
          (background_firstY_zero hn5 _ _ (angle_unit α))
          (qA_of_ezero (ezero_add ezero_first (ezero_last (by omega))))
    · have hjpos : 1 ≤ j := by omega
      calc
        _ = pauliExpectation f (internalYMask n j) (UnifiedEJM.MaskFacts.cutTail n j) I := by
          apply CircuitPauli.circuit_expectation (by omega) f
          rw [cutTail_circuit]
          simpa only [ite_eq_right hjzero, internalYMask, adjacentMask, add_comm] using
            CircuitPauli.localY_beforeLast j hjn f
        _ = _ := normalized_classII (by omega) α β _ _ _
          (UnifiedEJM.MaskFacts.internalY hn5 j hjpos hjn)
          (background_internalY_zero hn he j hjpos hjn _ _ (angle_unit β))
          (qA_internalY hn5 he j hjpos hjn)

/-- 完整测量的真实单比特偏迹，无待证背景或种子分量前提。 -/
theorem measurement_reduced {n : ℕ} (hn : 8 ≤ n) (he : Even n) (α β : ℝ)
    (label : Bits n) (j : Fin n) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement n α β label) j = (1/2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      (EvenEmbedding.radius n α β : ℂ) •
        ((v 0 : ℂ) • sigmaX + (v 1 : ℂ) • sigmaY + (v 2 : ℂ) • sigmaZ)) := by
  have hh := Physical.measurement_reduced_from_seed (by omega) (diagonal n α β)
    (diagonal_unit n α β) (component n α β) label j
    (seed_localX hn he α β j.val j.isLt) (seed_localY hn he α β j.val j.isLt)
    (seed_localZ hn he α β j.val j.isLt)
  simpa only [measurement, EvenEmbedding.radius, component, mul_div_assoc] using hh

theorem measurement_orthonormal {n : ℕ} (hn : 0 < n) (α β : ℝ) (k l : Bits n) :
    inner (measurement n α β k) (measurement n α β l) = if k=l then 1 else 0 :=
  Physical.measurement_orthonormal hn _ (diagonal_unit n α β) k l

theorem measurement_complete {n : ℕ} (hn : 0 < n) (α β : ℝ) (z w : Bits n) :
    (∑ label, measurement n α β label z * star (measurement n α β label w)) =
      if z=w then 1 else 0 :=
  Physical.measurement_complete hn _ (diagonal_unit n α β) z w

end UnifiedEJM.EvenFamily

