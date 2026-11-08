import UnifiedEJM.PhysicsLaurent

noncomputable section

namespace UnifiedEJM.PrefixAnalytic

/-- 这里只需三角函数的初等界，不依赖大规模有限系数表模块。 -/
theorem mul_trig_le_abs (a x : ℝ) (hx : |x| ≤ 1) : a*x ≤ |a| := by
  apply (le_abs_self _).trans
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left hx (abs_nonneg a)

theorem linear_trig_sq_le (a b t : ℝ) :
    (a * Real.cos t + b * Real.sin t)^2 ≤ a^2+b^2 := by
  calc
    _ = (a^2+b^2) * (Real.sin t^2+Real.cos t^2) -
        (a*Real.sin t-b*Real.cos t)^2 := by ring
    _ ≤ a^2+b^2 := by
      rw [Real.sin_sq_add_cos_sq]
      nlinarith [sq_nonneg (a*Real.sin t-b*Real.cos t)]

theorem special_trig_two (t : ℝ) : 3*Real.cos t - 4*Real.sin t ≤ 5 := by
  have h := linear_trig_sq_le 3 (-4) t
  nlinarith [sq_nonneg (3*Real.cos t - 4*Real.sin t - 5)]

/-- 实系数 Fourier 多项式，顺序与精确长度证书一致。 -/
def eval (q : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  q 0 + q 1 * Real.cos t + q 2 * Real.sin t +
    q 3 * Real.cos (2*t) + q 4 * Real.sin (2*t)

theorem eval_int (q : Fin 5 → ℤ) (t : ℝ) :
    eval (fun j => (q j : ℝ)) t =
      (q 0 : ℝ) + q 1 * Real.cos t + q 2 * Real.sin t +
        q 3 * Real.cos (2*t) + q 4 * Real.sin (2*t) := rfl

theorem eval_le_abs (q : Fin 5 → ℝ) (t : ℝ) :
    eval q t ≤ q 0 + |q 1| + |q 2| + |q 3| + |q 4| := by
  have h1 := mul_trig_le_abs (q 1) (Real.cos t) (Real.abs_cos_le_one t)
  have h2 := mul_trig_le_abs (q 2) (Real.sin t) (Real.abs_sin_le_one t)
  have h3 := mul_trig_le_abs (q 3) (Real.cos (2*t)) (Real.abs_cos_le_one _)
  have h4 := mul_trig_le_abs (q 4) (Real.sin (2*t)) (Real.abs_sin_le_one _)
  unfold eval
  linarith

def longCoeffs (X Y : ℝ) : Fin 5 → ℝ :=
  ![65024*X^2*Y^2-1088*X*Y+256*(X+Y)-4,
    47104*X^2*Y^2-704*X*Y, 832*X*Y-256*(X+Y),
    18944*X^2*Y^2-256*X*Y-4, 224*X*Y]

/-- k=3 或 l=3 且 k 偶数的相同长度多项式。 -/
def shortEvenCoeffs (Y : ℝ) : Fin 5 → ℝ :=
  ![17920*Y^2-224*Y+124, 10240*Y^2-384*Y, 64*Y-128,
    4608*Y^2-160*Y-4, 96*Y]

/-- l=3 且 k 奇数时的长度多项式。 -/
def shortOddCoeffs (X : ℝ) : Fin 5 → ℝ :=
  ![19968*X^2-448*X+124, 10240*X^2-256*X, 384*X-128,
    2560*X^2-64*X-4, 64*X]

def pairCoeffs (K : ℝ) : Fin 5 → ℝ :=
  ![5632*K^2-64*K+60, 2048*K^2-128*K, -64, 512*K^2-64*K-4, 0]

def sixCoeffs : Fin 5 → ℝ := ![5404,2144,-32,380,16]
def fiveCoeffs : Fin 5 → ℝ := ![379,112,-24,3,-4]

lemma square_ge_self (x : ℝ) (hx : 1 ≤ x) : x ≤ x^2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ x)]

lemma long_domain (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    1 ≤ X*Y ∧ X+Y ≤ 2*X*Y ∧ X*Y ≤ X^2*Y^2 := by
  have hXYX : X ≤ X*Y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ X) (sub_nonneg.mpr hY)]
  have hXYY : Y ≤ X*Y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (by linarith : 0 ≤ Y)]
  have hXY : 1 ≤ X*Y := hX.trans hXYX
  refine ⟨hXY, by linarith, ?_⟩
  nlinarith [square_ge_self (X*Y) hXY]

theorem long_numerator_bound (X Y t : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    eval (longCoeffs X Y) t ≤ 131072*X^2*Y^2-992*X*Y-8 := by
  obtain ⟨hXY, hsum, hquad⟩ := long_domain X Y hX hY
  have hb : 0 ≤ 47104*X^2*Y^2-704*X*Y := by nlinarith only [hquad,hXY]
  have hc : 0 ≤ 832*X*Y-256*(X+Y) := by nlinarith only [hsum,hXY]
  have hd : 0 ≤ 18944*X^2*Y^2-256*X*Y-4 := by nlinarith only [hquad,hXY]
  have he : 0 ≤ 224*X*Y := by nlinarith only [hXY]
  have h := eval_le_abs (longCoeffs X Y) t
  change eval (longCoeffs X Y) t ≤
    (65024*X^2*Y^2-1088*X*Y+256*(X+Y)-4) +
      |47104*X^2*Y^2-704*X*Y| + |832*X*Y-256*(X+Y)| +
      |18944*X^2*Y^2-256*X*Y-4| + |224*X*Y| at h
  rw [abs_of_nonneg hb, abs_of_nonneg hc, abs_of_nonneg hd, abs_of_nonneg he] at h
  linarith only [h]

theorem shortEven_numerator_bound (Y t : ℝ) (hY : 1 ≤ Y) :
    eval (shortEvenCoeffs Y) t ≤ 32768*Y^2-608*Y+248 := by
  have hquad := square_ge_self Y hY
  have hb : 0 ≤ 10240*Y^2-384*Y := by nlinarith only [hquad,hY]
  have hc : |64*Y-128| ≤ 64*Y+128 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hd : 0 ≤ 4608*Y^2-160*Y-4 := by nlinarith only [hquad,hY]
  have he : 0 ≤ 96*Y := by linarith
  have h := eval_le_abs (shortEvenCoeffs Y) t
  change eval (shortEvenCoeffs Y) t ≤
    (17920*Y^2-224*Y+124) + |10240*Y^2-384*Y| + |64*Y-128| +
      |4608*Y^2-160*Y-4| + |96*Y| at h
  rw [abs_of_nonneg hb, abs_of_nonneg hd, abs_of_nonneg he] at h
  linarith only [h,hc]

theorem shortOdd_numerator_bound (X t : ℝ) (hX : 1 ≤ X) :
    eval (shortOddCoeffs X) t ≤ 32768*X^2-320*X-8 := by
  have hquad := square_ge_self X hX
  have hb : 0 ≤ 10240*X^2-256*X := by nlinarith only [hquad,hX]
  have hc : 0 ≤ 384*X-128 := by linarith
  have hd : 0 ≤ 2560*X^2-64*X-4 := by nlinarith only [hquad,hX]
  have he : 0 ≤ 64*X := by linarith
  have h := eval_le_abs (shortOddCoeffs X) t
  change eval (shortOddCoeffs X) t ≤
    (19968*X^2-448*X+124) + |10240*X^2-256*X| + |384*X-128| +
      |2560*X^2-64*X-4| + |64*X| at h
  rw [abs_of_nonneg hb, abs_of_nonneg hc, abs_of_nonneg hd, abs_of_nonneg he] at h
  linarith only [h]

theorem pair_numerator_bound (K t : ℝ) (hK : 1 ≤ K) :
    eval (pairCoeffs K) t ≤ 8192*K^2-256*K+120 := by
  have hquad := square_ge_self K hK
  have hb : 0 ≤ 2048*K^2-128*K := by nlinarith only [hquad,hK]
  have hd : 0 ≤ 512*K^2-64*K-4 := by nlinarith only [hquad,hK]
  have h := eval_le_abs (pairCoeffs K) t
  change eval (pairCoeffs K) t ≤
    (5632*K^2-64*K+60) + |2048*K^2-128*K| + |(-64:ℝ)| +
      |512*K^2-64*K-4| + |(0:ℝ)| at h
  rw [abs_of_nonneg hb, abs_of_nonneg hd] at h
  norm_num at h
  linarith only [h]

theorem six_numerator_bound (t : ℝ) : eval sixCoeffs t ≤ 7976 := by
  have h := eval_le_abs sixCoeffs t
  norm_num [sixCoeffs] at h
  simpa only [sixCoeffs] using h

theorem five_numerator_bound (t : ℝ) : eval fiveCoeffs t ≤ 499 := by
  have h1 : 112*Real.cos t-24*Real.sin t ≤ 115 := by
    have h := linear_trig_sq_le 112 (-24) t
    nlinarith [sq_nonneg (112*Real.cos t-24*Real.sin t-115)]
  have h2 := special_trig_two (2*t)
  norm_num [eval,fiveCoeffs]
  linarith

/-- 分子界除以正归一化因子，保留显式纯度间隙。 -/
lemma divide_gap (N D g : ℝ) (hD : 0 < D) (hN : N ≤ D/2-g) :
    N/D ≤ 1/2-g/D := by
  apply (div_le_iff₀ hD).2
  calc
    N ≤ D/2-g := hN
    _ = (1/2-g/D)*D := by field_simp [ne_of_gt hD] <;> ring

theorem long_gap (X Y t : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    eval (longCoeffs X Y) t / (262144*X^2*Y^2) ≤
      1/2-(992*X*Y+8)/(262144*X^2*Y^2) := by
  apply divide_gap _ _ _ (by positivity)
  have h := long_numerator_bound X Y t hX hY
  linarith only [h]

theorem shortEven_gap (Y t : ℝ) (hY : 1 ≤ Y) :
    eval (shortEvenCoeffs Y) t / (65536*Y^2) ≤
      1/2-(608*Y-248)/(65536*Y^2) := by
  apply divide_gap _ _ _ (by positivity)
  have h := shortEven_numerator_bound Y t hY
  linarith only [h]

theorem shortOdd_gap (X t : ℝ) (hX : 1 ≤ X) :
    eval (shortOddCoeffs X) t / (65536*X^2) ≤
      1/2-(320*X+8)/(65536*X^2) := by
  apply divide_gap _ _ _ (by positivity)
  have h := shortOdd_numerator_bound X t hX
  linarith only [h]

theorem pair_gap (K t : ℝ) (hK : 1 ≤ K) :
    eval (pairCoeffs K) t / (16384*K^2) ≤
      1/2-(256*K-120)/(16384*K^2) := by
  apply divide_gap _ _ _ (by positivity)
  have h := pair_numerator_bound K t hK
  linarith only [h]

theorem six_gap (t : ℝ) : eval sixCoeffs t / 16384 ≤ 1/2-27/2048 := by
  have h := six_numerator_bound t
  linarith

theorem five_gap (t : ℝ) : eval fiveCoeffs t / 1024 ≤ 1/2-13/1024 := by
  have h := five_numerator_bound t
  linarith

/-- 各长度分支的显式间隙均大于共同要求的 2^(-n-2)。 -/
theorem long_common_bound (X Y t : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    eval (longCoeffs X Y) t / (262144*X^2*Y^2) ≤ 1/2-1/(1024*X*Y) := by
  have hg : 1/(1024*X*Y) ≤ (992*X*Y+8)/(262144*X^2*Y^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [sq_nonneg (X*Y), (long_domain X Y hX hY).1]
  linarith [long_gap X Y t hX hY]

theorem shortEven_common_bound (Y t : ℝ) (hY : 1 ≤ Y) :
    eval (shortEvenCoeffs Y) t / (65536*Y^2) ≤ 1/2-1/(512*Y) := by
  have hg : 1/(512*Y) ≤ (608*Y-248)/(65536*Y^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [square_ge_self Y hY]
  linarith [shortEven_gap Y t hY]

theorem shortOdd_common_bound (X t : ℝ) (hX : 1 ≤ X) :
    eval (shortOddCoeffs X) t / (65536*X^2) ≤ 1/2-1/(512*X) := by
  have hg : 1/(512*X) ≤ (320*X+8)/(65536*X^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [sq_nonneg X]
  linarith [shortOdd_gap X t hX]

theorem pair_common_bound (K t : ℝ) (hK : 1 ≤ K) :
    eval (pairCoeffs K) t / (16384*K^2) ≤ 1/2-1/(256*K) := by
  have hg : 1/(256*K) ≤ (256*K-120)/(16384*K^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [square_ge_self K hK]
  linarith [pair_gap K t hK]

theorem six_common_bound (t : ℝ) : eval sixCoeffs t / 16384 ≤ 1/2-1/(2:ℝ)^8 := by
  have h := six_gap t
  norm_num at *
  linarith

theorem five_common_bound (t : ℝ) : eval fiveCoeffs t / 1024 ≤ 1/2-1/(2:ℝ)^7 := by
  have h := five_gap t
  norm_num at *
  linarith

lemma length_variable_ge_one (k d : ℕ) : 1 ≤ (2:ℝ)^(k-d) := by
  exact one_le_pow₀ (by norm_num)

theorem long_length_bound (k l : ℕ) (hk : 4 ≤ k) (hl : 4 ≤ l) (t : ℝ) :
    eval (longCoeffs ((2:ℝ)^(k-4)) ((2:ℝ)^(l-4))) t /
      (262144*((2:ℝ)^(k-4))^2*((2:ℝ)^(l-4))^2) ≤ 1/2-1/(2:ℝ)^(k+l+2) := by
  have he : (2:ℝ)^(k+l+2) = 1024*(2:ℝ)^(k-4)*(2:ℝ)^(l-4) := by
    rw [show k+l+2=(k-4)+(l-4)+10 by omega, pow_add, pow_add]
    norm_num
    ring
  rw [he]
  exact long_common_bound _ _ t (length_variable_ge_one k 4) (length_variable_ge_one l 4)

theorem shortEven_length_bound (l : ℕ) (hl : 4 ≤ l) (t : ℝ) :
    eval (shortEvenCoeffs ((2:ℝ)^(l-4))) t /
      (65536*((2:ℝ)^(l-4))^2) ≤ 1/2-1/(2:ℝ)^(l+5) := by
  have he : (2:ℝ)^(l+5) = 512*(2:ℝ)^(l-4) := by
    rw [show l+5=(l-4)+9 by omega, pow_add]
    norm_num
    ring
  rw [he]
  exact shortEven_common_bound _ t (length_variable_ge_one l 4)

theorem shortOdd_length_bound (k : ℕ) (hk : 4 ≤ k) (t : ℝ) :
    eval (shortOddCoeffs ((2:ℝ)^(k-4))) t /
      (65536*((2:ℝ)^(k-4))^2) ≤ 1/2-1/(2:ℝ)^(k+5) := by
  have he : (2:ℝ)^(k+5) = 512*(2:ℝ)^(k-4) := by
    rw [show k+5=(k-4)+9 by omega, pow_add]
    norm_num
    ring
  rw [he]
  exact shortOdd_common_bound _ t (length_variable_ge_one k 4)

theorem pair_length_bound (n : ℕ) (hn : 6 ≤ n) (t : ℝ) :
    eval (pairCoeffs ((2:ℝ)^(n-6))) t /
      (16384*((2:ℝ)^(n-6))^2) ≤ 1/2-1/(2:ℝ)^(n+2) := by
  have he : (2:ℝ)^(n+2) = 256*(2:ℝ)^(n-6) := by
    rw [show n+2=(n-6)+8 by omega, pow_add]
    norm_num
    ring
  rw [he]
  exact pair_common_bound _ t (length_variable_ge_one n 6)

theorem strict_of_common (p : ℝ) (n : ℕ) (hp : p ≤ 1/2-1/(2:ℝ)^(n+2)) : p < 1/2 := by
  have hpos : 0 < 1/(2:ℝ)^(n+2) := by positivity
  linarith

end UnifiedEJM.PrefixAnalytic
