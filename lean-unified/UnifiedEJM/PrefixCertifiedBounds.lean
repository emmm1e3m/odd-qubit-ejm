import UnifiedEJM.PrefixRealBridge
import UnifiedEJM.P12Certificates
import UnifiedEJM.LongCase00
import UnifiedEJM.LongCase01
import UnifiedEJM.LongCase02
import UnifiedEJM.LongCase10
import UnifiedEJM.LongCase11
import UnifiedEJM.LongCase12
import UnifiedEJM.LongCase20
import UnifiedEJM.LongCase21
import UnifiedEJM.LongCase22

open OddEJM Complex
open UnifiedEJM.PhysicsFinite UnifiedEJM.BoundaryAmplitude UnifiedEJM.PrefixKernel

namespace UnifiedEJM.PrefixCounts

noncomputable section

/-- 本文件调用实际有限核证书，未把系数公式列作额外前提。 -/
theorem realFourier_long (la lb : Bit) (X Y : ℤ) :
    realFourier (longSum (some la) (some lb) X Y) =
      PrefixAnalytic.longCoeffs (X : ℝ) (Y : ℝ) := by
  rcases bit_cases la with rfl | rfl <;> rcases bit_cases lb with rfl | rfl <;>
    funext r <;> fin_cases r <;>
      norm_num [realFourier, LongCase11.polynomial, LongCase12.polynomial,
        LongCase21.polynomial, LongCase22.polynomial, biEval,
        LongCase11.expected, LongCase12.expected, LongCase21.expected, LongCase22.expected,
        PrefixAnalytic.longCoeffs, pow_two] <;> push_cast <;> ring

theorem realFourier_none_left (lb : Bit) (X Y : ℤ) :
    realFourier (longSum none (some lb) X Y) =
      PrefixAnalytic.shortEvenCoeffs (Y : ℝ) := by
  rcases bit_cases lb with rfl | rfl <;> funext r <;> fin_cases r <;>
    norm_num [realFourier, LongCase01.polynomial, LongCase02.polynomial,
      biEval, LongCase01.expected, LongCase02.expected,
      PrefixAnalytic.shortEvenCoeffs, pow_two] <;> push_cast <;> ring

theorem realFourier_none_right_even (X Y : ℤ) :
    realFourier (longSum (some 0) none X Y) =
      PrefixAnalytic.shortOddCoeffs (X : ℝ) := by
  funext r
  fin_cases r <;> norm_num [realFourier, LongCase10.polynomial,
    biEval, LongCase10.expected, PrefixAnalytic.shortOddCoeffs, pow_two] <;>
      push_cast <;> ring

theorem realFourier_none_right_odd (X Y : ℤ) :
    realFourier (longSum (some 1) none X Y) =
      PrefixAnalytic.shortEvenCoeffs (X : ℝ) := by
  funext r
  fin_cases r <;> norm_num [realFourier, LongCase20.polynomial,
    biEval, LongCase20.expected, PrefixAnalytic.shortEvenCoeffs, pow_two] <;>
      push_cast <;> ring

theorem realFourier_none_none (X Y : ℤ) :
    realFourier (longSum none none X Y) = PrefixAnalytic.sixCoeffs := by
  funext r
  fin_cases r <;> norm_num [realFourier, LongCase00.polynomial,
    biEval, LongCase00.expected, PrefixAnalytic.sixCoeffs, pow_two]

theorem realFourier_p12 (nu : Bit) (suffix : Bool) (K : ℤ) :
    realFourier (p12Sum nu suffix K) = PrefixAnalytic.pairCoeffs (K : ℝ) := by
  funext r
  fin_cases r <;> norm_num [realFourier, p12Sum_checked, p12Expected,
    PrefixAnalytic.pairCoeffs, pow_two] <;> push_cast <;> ring

@[simp] theorem runInfo_zero : runInfo 0 = none := rfl

theorem runInfo_pos {L : ℕ} (hL : 1 ≤ L) : runInfo L = some (L : Bit) := by
  simp [runInfo, show L ≠ 0 by omega]

lemma long_denominator {LA LB : ℕ} (hA : 1 ≤ LA) (hB : 1 ≤ LB) :
    (2 : ℝ)^(2*longN LA LB+2) =
      262144*((2 : ℝ)^(LA-1))^2*((2 : ℝ)^(LB-1))^2 := by
  calc
    _ = (2 : ℝ)^18 * (2 : ℝ)^((LA-1)*2) * (2 : ℝ)^((LB-1)*2) := by
      rw [← pow_add, ← pow_add]
      congr 1 <;> dsimp [longN, longK] <;> omega
    _ = _ := by norm_num [pow_mul]

lemma long_gap_denominator {LA LB : ℕ} (hA : 1 ≤ LA) (hB : 1 ≤ LB) :
    (2 : ℝ)^(longN LA LB+2) = 1024*(2 : ℝ)^(LA-1)*(2 : ℝ)^(LB-1) := by
  calc
    _ = (2 : ℝ)^10 * (2 : ℝ)^(LA-1) * (2 : ℝ)^(LB-1) := by
      rw [← pow_add, ← pow_add]
      congr 1 <;> dsimp [longN, longK] <;> omega
    _ = _ := by norm_num

lemma single_denominator {L : ℕ} (hL : 1 ≤ L) (c : ℕ) :
    (2 : ℝ)^(2*(L+c)+2) = (2 : ℝ)^(2*c+4)*((2 : ℝ)^(L-1))^2 := by
  rw [← pow_mul, ← pow_add]
  congr 1 <;> omega

lemma single_gap_denominator {L : ℕ} (hL : 1 ≤ L) (c : ℕ) :
    (2 : ℝ)^(L+c+2) = (2 : ℝ)^(c+3)*(2 : ℝ)^(L-1) := by
  rw [← pow_add]
  congr 1 <;> omega

/-- 两个自由组均非空时的真实种子纯度统一间隙。 -/
theorem seed_prefix_long_positive_bound {LA LB : ℕ} (hA : 1 ≤ LA) (hB : 1 ≤ LB)
    (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (longN LA LB) (longK LA))
      (UnifiedEJM.seed (longN LA LB) t)).re ≤ 1/2-1/(2 : ℝ)^(longN LA LB+2) := by
  rw [seed_prefix_longSum_re, runInfo_pos hA, runInfo_pos hB, realFourier_long]
  simp only [Int.cast_pow, Int.cast_ofNat]
  rw [long_denominator hA hB, long_gap_denominator hA hB]
  exact PrefixAnalytic.long_common_bound _ _ t
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))

/-- 首侧三位，另一侧任意至少四位。 -/
theorem seed_prefix_short_left_bound {L : ℕ} (hL : 1 ≤ L) (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (longN 0 L) (longK 0))
      (UnifiedEJM.seed (longN 0 L) t)).re ≤ 1/2-1/(2 : ℝ)^(longN 0 L+2) := by
  rw [seed_prefix_longSum_re, runInfo_zero, runInfo_pos hL, realFourier_none_left]
  simp only [Int.cast_pow, Int.cast_ofNat]
  have hn : longN 0 L = L+6 := by dsimp [longN, longK]; omega
  rw [hn, single_denominator (L := L) hL 6, single_gap_denominator (L := L) hL 6]
  norm_num
  simpa only [one_div, mul_inv_rev] using
    (PrefixAnalytic.shortEven_common_bound ((2 : ℝ)^(L-1)) t
      (one_le_pow₀ (by norm_num)))

/-- 末侧三位，首侧任意至少四位；两种奇偶均含在已核验表中。 -/
theorem seed_prefix_short_right_bound {L : ℕ} (hL : 1 ≤ L) (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (longN L 0) (longK L))
      (UnifiedEJM.seed (longN L 0) t)).re ≤ 1/2-1/(2 : ℝ)^(longN L 0+2) := by
  rw [seed_prefix_longSum_re, runInfo_pos hL, runInfo_zero]
  have hn : longN L 0 = L+6 := by dsimp [longN, longK]; omega
  rw [hn, single_denominator (L := L) hL 6, single_gap_denominator (L := L) hL 6]
  rcases bit_cases (L : Bit) with h | h
  · rw [h, realFourier_none_right_even]
    simp only [Int.cast_pow, Int.cast_ofNat]
    norm_num
    simpa only [one_div, mul_inv_rev] using
      (PrefixAnalytic.shortOdd_common_bound ((2 : ℝ)^(L-1)) t
        (one_le_pow₀ (by norm_num)))
  · rw [h, realFourier_none_right_odd]
    simp only [Int.cast_pow, Int.cast_ofNat]
    norm_num
    simpa only [one_div, mul_inv_rev] using
      (PrefixAnalytic.shortEven_common_bound ((2 : ℝ)^(L-1)) t
        (one_le_pow₀ (by norm_num)))

theorem seed_prefix_six_bound (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (longN 0 0) (longK 0))
      (UnifiedEJM.seed (longN 0 0) t)).re ≤ 1/2-1/(2 : ℝ)^(longN 0 0+2) := by
  rw [seed_prefix_longSum_re, runInfo_zero, realFourier_none_none]
  convert PrefixAnalytic.six_common_bound t using 1 <;> norm_num [longN, longK]

/-- 全部两侧至少三位的真实纯度共同间隙，包括空自由组。 -/
theorem seed_prefix_long_bound (LA LB : ℕ) (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (longN LA LB) (longK LA))
      (UnifiedEJM.seed (longN LA LB) t)).re ≤ 1/2-1/(2 : ℝ)^(longN LA LB+2) := by
  by_cases hA : LA = 0
  · subst LA
    by_cases hB : LB = 0
    · subst LB
      exact seed_prefix_six_bound t
    · exact seed_prefix_short_left_bound (by omega) t
  · by_cases hB : LB = 0
    · subst LB
      exact seed_prefix_short_right_bound (by omega) t
    · exact seed_prefix_long_positive_bound (by omega) (by omega) t

/-- n≥6的首或末两位侧真实纯度共同间隙。 -/
theorem seed_prefix_pair_bound {L : ℕ} (hL : 1 ≤ L) (suffix : Bool) (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (smallN L) (smallK L suffix))
      (UnifiedEJM.seed (smallN L) t)).re ≤ 1/2-1/(2 : ℝ)^(smallN L+2) := by
  rw [seed_prefix_p12Sum_re hL, realFourier_p12]
  simp only [Int.cast_pow, Int.cast_ofNat]
  have hn : smallN L = L+5 := by dsimp [smallN]; omega
  rw [hn, single_denominator (L := L) hL 5, single_gap_denominator (L := L) hL 5]
  norm_num
  simpa only [one_div, mul_inv_rev] using
    (PrefixAnalytic.pair_common_bound ((2 : ℝ)^(L-1)) t
      (one_le_pow₀ (by norm_num)))

/-- 同时替换态空间维度与割位置，避免simp跳过依赖类型中的维度。 -/
private theorem seed_prefix_bound_of_eq {m n a b : ℕ}
    (hN : m = n) (hK : a = b) (t : ℝ)
    (h : (Multipartite.cutPurity (prefixSet m a) (UnifiedEJM.seed m t)).re ≤
      1/2-1/(2 : ℝ)^(m+2)) :
    (Multipartite.cutPurity (prefixSet n b) (UnifiedEJM.seed n t)).re ≤
      1/2-1/(2 : ℝ)^(n+2) := by
  subst n
  subst b
  exact h

/-- 用两侧实际长度表述全部n≥6非单体前缀。 -/
theorem seed_prefix_lengths_bound (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hn : 6 ≤ k+l) (t : ℝ) :
    (Multipartite.cutPurity (prefixSet (k+l) k) (UnifiedEJM.seed (k+l) t)).re ≤
      1/2-1/(2 : ℝ)^(k+l+2) := by
  by_cases hk2 : k = 2
  · have hL : 1 ≤ k+l-5 := by omega
    have hN : smallN (k+l-5) = k+l := by dsimp [smallN]; omega
    have hK : smallK (k+l-5) false = k := by simpa [smallK] using hk2.symm
    exact seed_prefix_bound_of_eq hN hK t
      (seed_prefix_pair_bound (L := k+l-5) hL false t)
  · by_cases hl2 : l = 2
    · have hL : 1 ≤ k+l-5 := by omega
      have hN : smallN (k+l-5) = k+l := by dsimp [smallN]; omega
      have hK : smallK (k+l-5) true = k := by dsimp [smallK]; omega
      exact seed_prefix_bound_of_eq hN hK t
        (seed_prefix_pair_bound (L := k+l-5) hL true t)
    · have hN : longN (k-3) (l-3) = k+l := by dsimp [longN, longK]; omega
      have hK : longK (k-3) = k := by dsimp [longK]; omega
      exact seed_prefix_bound_of_eq hN hK t (seed_prefix_long_bound (k-3) (l-3) t)

/-- 原seed、任意实参数、任意n≥6非单体前缀的统一paper gap。 -/
theorem seed_prefix_bound {n k : ℕ} (hn : 6 ≤ n) (hk : 2 ≤ k) (hl : 2 ≤ n-k)
    (t : ℝ) :
    (Multipartite.cutPurity (prefixSet n k) (UnifiedEJM.seed n t)).re ≤
      1/2-1/(2 : ℝ)^(n+2) := by
  have hN : k+(n-k) = n := by omega
  exact seed_prefix_bound_of_eq hN rfl t
    (seed_prefix_lengths_bound k (n-k) hk hl (by omega) t)

theorem seed_prefix_strict {n k : ℕ} (hn : 6 ≤ n) (hk : 2 ≤ k) (hl : 2 ≤ n-k)
    (t : ℝ) :
    (Multipartite.cutPurity (prefixSet n k) (UnifiedEJM.seed n t)).re < 1/2 :=
  PrefixAnalytic.strict_of_common _ n (seed_prefix_bound hn hk hl t)

/-- 后缀是前缀互补，使用实际纯态互补纯度恒等式。 -/
theorem seed_suffix_bound {n k : ℕ} (hn : 6 ≤ n) (hk : 2 ≤ k) (hl : 2 ≤ n-k)
    (t : ℝ) :
    (Multipartite.cutPurity (prefixSet n k)ᶜ (UnifiedEJM.seed n t)).re ≤
      1/2-1/(2 : ℝ)^(n+2) := by
  rw [Multipartite.cutPurity_compl]
  exact seed_prefix_bound hn hk hl t

end

end UnifiedEJM.PrefixCounts
