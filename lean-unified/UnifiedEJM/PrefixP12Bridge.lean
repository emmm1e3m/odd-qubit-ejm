import UnifiedEJM.PrefixPairPacking

open OddEJM Complex
open UnifiedEJM.PhysicsFinite UnifiedEJM.BoundaryAmplitude UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

noncomputable section

/-- 两位侧的单串H接口，保持有限核不透明以避免复数强转展开。 -/
def smallWordH (nu : Bit) (f s t p l : Bit) (c : Fin 4) : Fin 2 → G :=
  H ![f,s,p,l] (t + catParity (1+nu) c)
    (decide (s=f ∧ t=f ∧ p=f ∧ l=f) && catMatches c f) nu

theorem evaluatedBoundary_smallPack_H {L : ℕ} (hL : 1 ≤ L) (suffix : Bool)
    (u : ℂ) (f s t : Bit) (a : Bits L) (p l : Bit) :
    evaluatedBoundary u (smallPack suffix f s t a p l) =
      affineEval (smallWordH (lengthParity (smallN L)) f s t p l (wordClass a)) u := by
  rw [evaluatedBoundary_smallPack hL, smallN_parity L, boundaryValue_H]
  rfl

theorem p12H_smallWordH (nu : Bit) (suffix : Bool) (f s t p l c d : Fin 4) :
    p12H nu suffix f s t p l c d =
      ![smallWordH nu (pair f).1 (pair s).1 (pair t).1 (pair p).1 (pair l).1 c,
        smallWordH nu (pair f).2 (pair s).2 (pair t).2 (pair p).2 (pair l).2 d,
        smallWordH nu (pair f).2 (pair s).2
          (if suffix then (pair t).2 else (pair t).1) (pair p).1 (pair l).1
          (if suffix then d else c),
        smallWordH nu (pair f).1 (pair s).1
          (if suffix then (pair t).1 else (pair t).2) (pair p).2 (pair l).2
          (if suffix then c else d)] := by
  funext r
  cases suffix <;> fin_cases r <;> rfl

theorem boundaryCopies_smallPack {L : ℕ} (hL : 1 ≤ L) (suffix : Bool) (u : ℂ)
    (first second third : Fin 4) (a : Fin L → Fin 4) (penult last : Fin 4) :
    boundaryCopies (prefixSet (smallN L) (smallK L suffix)) u
      (smallPack suffix first second third a penult last) =
      fun r => affineEval (p12H (lengthParity (smallN L)) suffix first second third penult last
        (wordClass ((pairWordsEquiv L a).1)) (wordClass ((pairWordsEquiv L a).2)) r) u := by
  cases suffix <;> simp only [boundaryCopies, pairWords_smallPack, p12H_smallWordH]
  all_goals
    simp_rw [splice_smallPack, evaluatedBoundary_smallPack_H hL]
    funext r
    fin_cases r <;> rfl

theorem prefixSign_smallPack {L : ℕ} (suffix : Bool) (first second third : Fin 4)
    (a : Fin L → Fin 4) (penult last : Fin 4) :
    prefixSign (smallK L suffix) (smallPack suffix first second third a penult last) =
      ((if suffix then
        gsign ((pair third).1+(pair third).2) ^
          (if (pair penult).1 = (pair penult).2 then 0 else 1)
      else gsign ((pair second).1+(pair second).2) ^
          (if (pair third).1 = (pair third).2 then 0 else 1) : G) : ℂ) := by
  simp only [prefixSign, pairWords_smallPack, smallPack_cut_left, smallPack_cut_right]
  cases suffix <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    exact boundary_sign_pair _ _ _ _

/-- 两位侧也逐项接回原四副本和，包含首两位和末两位两个方向。 -/
theorem prefixTerm_smallPack {L : ℕ} (hL : 1 ≤ L) (suffix : Bool)
    (u : ℂ) (hu : u * star u = 1) (first second third : Fin 4)
    (a : Fin L → Fin 4) (penult last : Fin 4) :
    prefixTerm (smallK L suffix) u (smallPack suffix first second third a penult last) =
      laurentEval (p12Term (lengthParity (smallN L)) suffix first second third penult last
        (wordClass ((pairWordsEquiv L a).1)) (wordClass ((pairWordsEquiv L a).2))) u := by
  simp only [prefixTerm, boundaryCopies_smallPack hL, prefixSign_smallPack, p12Term]
  rw [laurentEval_mul, ← quartet_eval _ u hu]
  ring

theorem laurentEval_p12Sum (nu : Bit) (suffix : Bool) (K : ℤ) (u : ℂ) :
    laurentEval (p12Sum nu suffix K) u =
      ∑ f : Fin 4, ∑ s : Fin 4, ∑ t : Fin 4, ∑ p : Fin 4, ∑ l : Fin 4,
        ∑ c : Fin 4, ∑ d : Fin 4,
          (catWeight K (1+nu) c : ℂ) * (catWeight K (1+nu) d : ℂ) *
            laurentEval (p12Term nu suffix f s t p l c d) u := by
  unfold p12Sum
  simp only [laurentEval_sum, laurentEval_mul, map_mul, Int.cast_mul, map_intCast]

/-- 全部n≥6的首/末两位纯度由实际任意长自由串计数归约到p12核。 -/
theorem actual_prefix_p12Sum {L : ℕ} (hL : 1 ≤ L) (suffix : Bool)
    (u : ℂ) (hu : u * star u = 1) :
    swapPurity (prefixSet (smallN L) (smallK L suffix))
      (Physical.seed (UnifiedEJM.rawPhase u)) =
      (((2 : ℂ)^(smallN L+1))⁻¹)^2 *
        laurentEval (p12Sum (lengthParity (smallN L)) suffix (2^(L-1))) u := by
  rw [actual_prefix_pair_sum (by dsimp [smallN]; omega)
    (by cases suffix <;> dsimp [smallK] <;> omega)
    (by cases suffix <;> dsimp [smallN, smallK] <;> omega)]
  congr 1
  rw [sum_smallPack_free_last L suffix, laurentEval_p12Sum]
  simp_rw [prefixTerm_smallPack hL suffix u hu]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro l _
  simpa only [smallN_parity] using sum_pairWord_cats hL
    (fun c d => laurentEval (p12Term (lengthParity (smallN L)) suffix f s t p l c d) u)

theorem seed_prefix_p12Sum {L : ℕ} (hL : 1 ≤ L) (suffix : Bool) (t : ℝ) :
    Multipartite.cutPurity (prefixSet (smallN L) (smallK L suffix))
      (UnifiedEJM.seed (smallN L) t) =
      (((2 : ℂ)^(smallN L+1))⁻¹)^2 *
        laurentEval (p12Sum (lengthParity (smallN L)) suffix (2^(L-1))) (anglePhase t) := by
  rw [cutPurity_eq_swap]
  exact actual_prefix_p12Sum hL suffix (anglePhase t) (by
    simpa only [mul_comm] using anglePhase_star_mul t)

end

end UnifiedEJM.PrefixCounts
