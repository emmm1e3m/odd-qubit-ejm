import UnifiedEJM.PrefixPairReindex
import UnifiedEJM.BoundaryKernel

open OddEJM Complex
open UnifiedEJM.PhysicsFinite UnifiedEJM.BoundaryAmplitude UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

noncomputable section

def affineEval (h : Fin 2 → G) (u : ℂ) : ℂ := (h 0 : ℂ) + u * (h 1 : ℂ)

theorem quartet_eval (h : Fin 4 → Fin 2 → G) (u : ℂ) (hu : u * star u = 1) :
    affineEval (h 0) u * affineEval (h 1) u *
      star (affineEval (h 2) u) * star (affineEval (h 3) u) =
        laurentEval (quartet h) u := by
  simpa [affineEval, quartet, pairCoeffs] using
    affine_term (fun r => h r 0) (fun r => h r 1) 0 1 2 3 u hu

theorem laurentEval_mul (a : G) (q : Fin 5 → G) (u : ℂ) :
    laurentEval (fun k => a * q k) u = (a : ℂ) * laurentEval q u := by
  simp only [laurentEval, map_mul]
  ring

theorem laurentEval_sum {ι : Type*} [Fintype ι] (q : ι → Fin 5 → G) (u : ℂ) :
    laurentEval (fun k => ∑ i, q i k) u = ∑ i, laurentEval (q i) u := by
  simp [laurentEval, map_sum, Finset.sum_add_distrib, Finset.sum_mul]

theorem boundary_sign_pair (x y z w : Bit) :
    bitSign ((x+y)*(z+w)) =
      ((gsign (x+y) ^ (if z = w then 0 else 1) : G) : ℂ) := by
  have hz (a b : Bit) : a+b = if a = b then 0 else 1 := by
    revert a b
    decide +kernel
  simp only [map_pow, gsign_complex]
  rw [hz z w]
  by_cases h : z = w <;> simp [h, bitSign]

def boundaryCopies {n : ℕ} (S : Finset (Fin n)) (u : ℂ) (z : Fin n → Fin 4) :
    Fin 4 → ℂ :=
  let y := (pairWordsEquiv n z).1
  let v := (pairWordsEquiv n z).2
  ![evaluatedBoundary u y, evaluatedBoundary u v,
    evaluatedBoundary u (splice S v y), evaluatedBoundary u (splice S y v)]

def prefixSign {n : ℕ} (k : ℕ) (z : Fin n → Fin 4) : ℂ :=
  let y := (pairWordsEquiv n z).1
  let v := (pairWordsEquiv n z).2
  bitSign ((coord y (k-1)+coord v (k-1))*(coord y k+coord v k))

def prefixTerm {n : ℕ} (k : ℕ) (u : ℂ) (z : Fin n → Fin 4) : ℂ :=
  let h := boundaryCopies (prefixSet n k) u z
  prefixSign k z * h 0 * h 1 * star (h 2) * star (h 3)

/-- 原seed四副本恒等式重索引为逐位置位对，保留完整缺陷。 -/
theorem actual_prefix_pair_sum {n k : ℕ} (hn : 5 ≤ n) (hk : 0 < k) (hkn : k < n)
    (u : ℂ) :
    swapPurity (prefixSet n k) (Physical.seed (UnifiedEJM.rawPhase u)) =
      (((2 : ℂ)^(n+1))⁻¹)^2 * ∑ z : Fin n → Fin 4, prefixTerm k u z := by
  rw [actual_swapPurity_boundary hn]
  simp_rw [crossing_sum_prefix hk hkn]
  congr 1
  rw [sum_pairWords n]
  apply Finset.sum_congr rfl
  intro z _
  simp [prefixTerm, prefixSign, boundaryCopies]
  ring

/-- 单个拼接字的H接口。此处保留H为整体，不展开其复数强制转换。 -/
def wordH (la lb : Option Bit) (f : Bits 2) (left right : Bit) (l : Bits 2)
    (ca cb : Fin 4) : Fin 2 → G :=
  H ![f 0, f 1, l 0, l 1]
    (left + right + runParity la ca + runParity lb cb)
    (decide (f 1 = f 0 ∧ left = f 0 ∧ right = f 0 ∧ l 0 = f 0 ∧ l 1 = f 0) &&
      runMatches la ca (f 0) && runMatches lb cb (f 0))
    (la.getD 0 + lb.getD 0)

theorem evaluatedBoundary_fullWord_H {LA LB : ℕ} (u : ℂ) (f : Bits 2)
    (a : Bits LA) (left right : Bit) (b : Bits LB) (l : Bits 2) :
    evaluatedBoundary u (fullWord f a left right b l) =
      affineEval (wordH (runInfo LA) (runInfo LB) f left right l
        (wordClass a) (wordClass b)) u := by
  rw [evaluatedBoundary_fullWord_run, lengthParity_longN]
  have hp : runParity (runInfo LA) (wordClass a) + left + right +
      runParity (runInfo LB) (wordClass b) =
        left + right + runParity (runInfo LA) (wordClass a) +
          runParity (runInfo LB) (wordClass b) := by ac_rfl
  rw [hp, boundaryValue_H]
  rfl

/-- 四个有限副本只做投影重排，直接定义归约，不展开H的内部算术。 -/
theorem longH_wordH (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) :
    longH la lb f s a b p l ca da cb db =
      ![wordH la lb ![(pair f).1, (pair s).1] (pair a).1 (pair b).1
          ![(pair p).1, (pair l).1] ca cb,
        wordH la lb ![(pair f).2, (pair s).2] (pair a).2 (pair b).2
          ![(pair p).2, (pair l).2] da db,
        wordH la lb ![(pair f).2, (pair s).2] (pair a).2 (pair b).1
          ![(pair p).1, (pair l).1] da cb,
        wordH la lb ![(pair f).1, (pair s).1] (pair a).1 (pair b).2
          ![(pair p).2, (pair l).2] ca db] := by
  funext r
  fin_cases r <;> rfl

/-- 每个真实四副本振幅均等于有限核所使用的同一个H。
自由组长度可以为零；末两项按交换后的前缀/后缀排列。 -/
theorem boundaryCopies_pack {LA LB : ℕ} (u : ℂ)
    (first second : Fin 4) (a : Fin LA → Fin 4) (left right : Fin 4)
    (b : Fin LB → Fin 4) (penult last : Fin 4) :
    boundaryCopies (prefixSet (longN LA LB) (longK LA)) u
      (pack first second a left right b penult last) =
      fun r => affineEval (longH (runInfo LA) (runInfo LB) first second left right penult last
        (wordClass ((pairWordsEquiv LA a).1)) (wordClass ((pairWordsEquiv LA a).2))
        (wordClass ((pairWordsEquiv LB b).1)) (wordClass ((pairWordsEquiv LB b).2)) r) u := by
  simp only [boundaryCopies, pairWords_pack, longH_wordH]
  simp_rw [splice_fullWord, evaluatedBoundary_fullWord_H]
  funext r
  fin_cases r <;> rfl

theorem prefixSign_pack {LA LB : ℕ} (first second : Fin 4) (a : Fin LA → Fin 4)
    (left right : Fin 4) (b : Fin LB → Fin 4) (penult last : Fin 4) :
    prefixSign (longK LA) (pack first second a left right b penult last) =
      ((gsign ((pair left).1+(pair left).2) ^
        (if (pair right).1 = (pair right).2 then 0 else 1) : G) : ℂ) := by
  simp only [prefixSign, pairWords_pack, fullWord_cut_left, fullWord_cut_right]
  exact boundary_sign_pair _ _ _ _

/-- 点式桥：有限核的每个系数项来自真实四副本，而非事后假定的系数表。 -/
theorem prefixTerm_pack {LA LB : ℕ} (u : ℂ) (hu : u * star u = 1)
    (first second : Fin 4) (a : Fin LA → Fin 4) (left right : Fin 4)
    (b : Fin LB → Fin 4) (penult last : Fin 4) :
    prefixTerm (longK LA) u (pack first second a left right b penult last) =
      laurentEval (longTerm (runInfo LA) (runInfo LB) first second left right penult last
        (wordClass ((pairWordsEquiv LA a).1)) (wordClass ((pairWordsEquiv LA a).2))
        (wordClass ((pairWordsEquiv LB b).1)) (wordClass ((pairWordsEquiv LB b).2))) u := by
  simp only [prefixTerm, boundaryCopies_pack, prefixSign_pack, longTerm]
  rw [laurentEval_mul, ← quartet_eval _ u hu]
  ring

theorem sum_two_pairWord_runs {R : Type*} [CommRing R] (LA LB : ℕ)
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) :
    (∑ a : Fin LA → Fin 4, ∑ b : Fin LB → Fin 4,
      f (wordClass ((pairWordsEquiv LA a).1)) (wordClass ((pairWordsEquiv LA a).2))
        (wordClass ((pairWordsEquiv LB b).1)) (wordClass ((pairWordsEquiv LB b).2))) =
      ∑ ca : Fin 4, ∑ da : Fin 4, ∑ cb : Fin 4, ∑ db : Fin 4,
        (runWeight (2^(LA-1)) (runInfo LA) ca : R) *
          (runWeight (2^(LA-1)) (runInfo LA) da : R) *
          (runWeight (2^(LB-1)) (runInfo LB) cb : R) *
          (runWeight (2^(LB-1)) (runInfo LB) db : R) * f ca da cb db := by
  have hb (ca da : Fin 4) := sum_pairWord_runs LB (fun cb db => f ca da cb db)
  simp_rw [hb]
  rw [sum_pairWord_runs LA (fun ca da =>
    ∑ cb : Fin 4, ∑ db : Fin 4,
      (runWeight (2^(LB-1)) (runInfo LB) cb : R) *
        (runWeight (2^(LB-1)) (runInfo LB) db : R) * f ca da cb db)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ca _
  apply Finset.sum_congr rfl
  intro da _
  apply Finset.sum_congr rfl
  intro cb _
  apply Finset.sum_congr rfl
  intro db _
  ring

theorem laurentEval_longSum (la lb : Option Bit) (X Y : ℤ) (u : ℂ) :
    laurentEval (longSum la lb X Y) u =
      ∑ f : Fin 4, ∑ s : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
        ∑ p : Fin 4, ∑ l : Fin 4, ∑ ca : Fin 4, ∑ da : Fin 4,
          ∑ cb : Fin 4, ∑ db : Fin 4,
            (runWeight X la ca : ℂ) * (runWeight X la da : ℂ) *
              (runWeight Y lb cb : ℂ) * (runWeight Y lb db : ℂ) *
              laurentEval (longTerm la lb f s a b p l ca da cb db) u := by
  unfold longSum
  simp only [laurentEval_sum, laurentEval_mul, map_mul, Int.cast_mul, map_intCast]

/-- 任意两侧长度至少3的实际纯度，完整归约为经类别计数生成的有限核。
该结论没有以系数表或纯度公式作为前提，空自由组也已纳入。 -/
theorem actual_prefix_longSum (LA LB : ℕ) (u : ℂ) (hu : u * star u = 1) :
    swapPurity (prefixSet (longN LA LB) (longK LA))
      (Physical.seed (UnifiedEJM.rawPhase u)) =
      (((2 : ℂ)^(longN LA LB+1))⁻¹)^2 *
        laurentEval (longSum (runInfo LA) (runInfo LB) (2^(LA-1)) (2^(LB-1))) u := by
  rw [actual_prefix_pair_sum (by dsimp [longN, longK]; omega)
    (by dsimp [longK]; omega) (by dsimp [longN, longK]; omega)]
  congr 1
  rw [sum_pack_free_last, laurentEval_longSum]
  simp_rw [prefixTerm_pack u hu]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro l _
  exact sum_two_pairWord_runs LA LB
    (fun ca da cb db => laurentEval
      (longTerm (runInfo LA) (runInfo LB) f s a b p l ca da cb db) u)

theorem cutPurity_eq_swap {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    Multipartite.cutPurity S ψ = swapPurity S ψ := by
  rw [Multipartite.cutPurity_eq_swap_sum]
  rfl

/-- 上式直接用于正式统一族seed，参数遍历全体实数。 -/
theorem seed_prefix_longSum (LA LB : ℕ) (t : ℝ) :
    Multipartite.cutPurity (prefixSet (longN LA LB) (longK LA))
      (UnifiedEJM.seed (longN LA LB) t) =
      (((2 : ℂ)^(longN LA LB+1))⁻¹)^2 *
        laurentEval (longSum (runInfo LA) (runInfo LB) (2^(LA-1)) (2^(LB-1))) (anglePhase t) := by
  rw [cutPurity_eq_swap]
  exact actual_prefix_longSum LA LB (anglePhase t) (by
    simpa only [mul_comm] using anglePhase_star_mul t)

end

end UnifiedEJM.PrefixCounts
