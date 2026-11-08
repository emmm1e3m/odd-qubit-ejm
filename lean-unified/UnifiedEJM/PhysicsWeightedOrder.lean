import UnifiedEJM.PhysicsWeightedTransfer

open OddEJM
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer

theorem siteWeight_nonneg (a : Site) : 0 ≤ siteWeight a := by
  cases h : a.inA <;> norm_num [siteWeight, h]

theorem stepKernel_nonneg (d : Logical) (a b : Site) (s t : Memory) :
    0 ≤ stepKernel d a b s t := by
  unfold stepKernel
  split_ifs <;> first | exact siteWeight_nonneg b | exact le_rfl

theorem advance_nonneg (d : Logical) (a b : Site) (μ : Distribution)
    (hμ : ∀ s, 0 ≤ μ s) : ∀ s, 0 ≤ advance d a b μ s := by
  intro t
  exact Finset.sum_nonneg fun s _ => mul_nonneg (hμ s) (stepKernel_nonneg d a b s t)

/-- 有限支撑/指数截断若增加输入权重，之后的精确演化仍保持上界。 -/
theorem advance_mono (d : Logical) (a b : Site) (μ ν : Distribution)
    (h : ∀ s, μ s ≤ ν s) : ∀ s, advance d a b μ s ≤ advance d a b ν s := by
  intro t
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_right (h s) (stepKernel_nonneg d a b s t)

theorem allowed_mass (b : Site) :
    (∑ r : Bit, if allowed b r then siteWeight b else 0) = 1 := by
  have huniv : (Finset.univ : Finset Bit) = {0, 1} := by decide +kernel
  cases h : b.inA <;> norm_num [huniv, allowed, siteWeight, h]

theorem stepKernel_mass_le (d : Logical) (a b : Site) (s : Memory) :
    (∑ t, stepKernel d a b s t) ≤ 1 := by
  have hp := stepKernel_pairing d a b s (fun _ => 1)
  simp only [mul_one] at hp
  rw [hp, ← allowed_mass b]
  apply Finset.sum_le_sum
  intro r hr
  by_cases ha : allowed b r
  · by_cases hc : constraint a d s.2.1 r
    · simp [ha, hc]
    · simpa [ha, hc] using siteWeight_nonneg b
  · simp [ha]

def mass (μ : Distribution) : ℚ := ∑ s, μ s

/-- 新位的平均与旧B约束都是质量不增的映射。 -/
theorem advance_mass_le (d : Logical) (a b : Site) (μ : Distribution)
    (hμ : ∀ s, 0 ≤ μ s) : mass (advance d a b μ) ≤ mass μ := by
  unfold mass advance
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [← Finset.mul_sum]
  simpa using mul_le_mul_of_nonneg_left (stepKernel_mass_le d a b s) (hμ s)

theorem evolve_nonneg (d : Logical) (bs : List Site) (a : Site) (μ : Distribution)
    (hμ : ∀ s, 0 ≤ μ s) : ∀ s, 0 ≤ evolve d a bs μ s := by
  induction bs generalizing a μ with
  | nil => exact hμ
  | cons b bs ih =>
      exact ih b (advance d a b μ) (advance_nonneg d a b μ hμ)

theorem evolve_mono (d : Logical) (bs : List Site) (a : Site) (μ ν : Distribution)
    (h : ∀ s, μ s ≤ ν s) : ∀ s, evolve d a bs μ s ≤ evolve d a bs ν s := by
  induction bs generalizing a μ ν with
  | nil => exact h
  | cons b bs ih =>
      exact ih b (advance d a b μ) (advance d a b ν) (advance_mono d a b μ ν h)

theorem evolve_mass_le (d : Logical) (bs : List Site) (a : Site) (μ : Distribution)
    (hμ : ∀ s, 0 ≤ μ s) : mass (evolve d a bs μ) ≤ mass μ := by
  induction bs generalizing a μ with
  | nil => exact le_rfl
  | cons b bs ih =>
      exact le_trans (ih b (advance d a b μ) (advance_nonneg d a b μ hμ))
        (advance_mass_le d a b μ hμ)

theorem finish_nonneg (d : Logical) (a : Site) (μ : Distribution)
    (hμ : ∀ s, 0 ≤ μ s) (k : Logical) : 0 ≤ finish d a μ k := by
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  split_ifs <;> first | exact hμ (k, p, q) | exact le_rfl

theorem finish_mono (d : Logical) (a : Site) (μ ν : Distribution)
    (h : ∀ s, μ s ≤ ν s) (k : Logical) : finish d a μ k ≤ finish d a ν k := by
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  split_ifs <;> first | exact h (k, p, q) | exact le_rfl

theorem finish_mass_le (d : Logical) (a : Site) (μ : Distribution)
    (hμ : ∀ s, 0 ≤ μ s) : (∑ k, finish d a μ k) ≤ mass μ := by
  unfold mass
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  change (if constraint a d p 0 then μ (k, p, q) else 0) ≤ μ (k, p, q)
  split_ifs <;> first | exact le_rfl | exact hμ (k, p, q)

/-- 一个可能替代大秩Schmidt估计的安全吸收阈值。 -/
theorem ten_bit_mass_bound (μ : Logical → Distribution)
    (hμ : ∀ d s, μ d s ≤ 1 / 4096) : (∑ d, mass (μ d)) ≤ 1 / 4 := by
  calc
    (∑ d, mass (μ d)) ≤ ∑ d : Logical, ∑ _ : Memory, (1 / 4096 : ℚ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.sum_le_sum fun s _ => hμ d s
    _ = 1 / 4 := by
      norm_num [Logical, Memory, OddEJM.Bits, OddEJM.Bit, Fintype.card_fun,
        Fintype.card_prod, ZMod.card]

/-- 任意后缀、任意终端函数F≤1：中途进入小质量区后始终安全。 -/
theorem suffix_score_le_mass (μ : Logical → Distribution)
    (hμ : ∀ d s, 0 ≤ μ d s) (a last : Site) (bs : List Site)
    (score : Logical → Logical → ℚ) (hscore : ∀ d k, score d k ≤ 1) :
    (∑ d, ∑ k, finish d last (evolve d a bs (μ d)) k * score d k) ≤
      ∑ d, mass (μ d) := by
  apply Finset.sum_le_sum
  intro d hd
  calc
    (∑ k, finish d last (evolve d a bs (μ d)) k * score d k) ≤
        ∑ k, finish d last (evolve d a bs (μ d)) k := by
      apply Finset.sum_le_sum
      intro k hk
      simpa using mul_le_mul_of_nonneg_left (hscore d k)
        (finish_nonneg d last _ (evolve_nonneg d bs a _ (hμ d)) k)
    _ ≤ mass (evolve d a bs (μ d)) :=
      finish_mass_le d last _ (evolve_nonneg d bs a _ (hμ d))
    _ ≤ mass (μ d) := evolve_mass_le d bs a _ (hμ d)

/-- 实值终端函数可取任意实参数t的复振幅模方，不要求其为有理数。 -/
theorem suffix_realScore_le_mass (μ : Logical → Distribution)
    (hμ : ∀ d s, 0 ≤ μ d s) (a last : Site) (bs : List Site)
    (score : Logical → Logical → ℝ) (hscore : ∀ d k, score d k ≤ 1) :
    (∑ d, ∑ k, (finish d last (evolve d a bs (μ d)) k : ℝ) * score d k) ≤
      ((∑ d, mass (μ d) : ℚ) : ℝ) := by
  push_cast
  apply Finset.sum_le_sum
  intro d hd
  calc
    (∑ k, (finish d last (evolve d a bs (μ d)) k : ℝ) * score d k) ≤
        ∑ k, (finish d last (evolve d a bs (μ d)) k : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hpos : (0 : ℝ) ≤ (finish d last (evolve d a bs (μ d)) k : ℝ) := by
        exact_mod_cast finish_nonneg d last _ (evolve_nonneg d bs a _ (hμ d)) k
      simpa using mul_le_mul_of_nonneg_left (hscore d k) hpos
    _ ≤ (mass (μ d) : ℝ) := by
      exact_mod_cast le_trans
        (finish_mass_le d last _ (evolve_nonneg d bs a _ (hμ d)))
        (evolve_mass_le d bs a _ (hμ d))

/-- 有限证书直接检查支撑的真实质量即可进入安全区，不需要任何秩公式。 -/
theorem suffix_realScore_le_quarter_of_mass (μ : Logical → Distribution)
    (hμ : ∀ d s, 0 ≤ μ d s) (hmass : (∑ d, mass (μ d)) ≤ 1 / 4)
    (a last : Site) (bs : List Site) (score : Logical → Logical → ℝ)
    (hscore : ∀ d k, score d k ≤ 1) :
    (∑ d, ∑ k, (finish d last (evolve d a bs (μ d)) k : ℝ) * score d k) ≤ 1 / 4 := by
  apply le_trans (suffix_realScore_le_mass μ hμ a last bs score hscore)
  calc
    ((∑ d, mass (μ d) : ℚ) : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) :=
      Rat.cast_mono hmass
    _ = 1 / 4 := by norm_num

/-- 一次进入E≥12安全区以后，无需继续枚举任何路径长度或割颜色。 -/
theorem suffix_realScore_le_quarter (μ : Logical → Distribution)
    (hμ : ∀ d s, 0 ≤ μ d s) (hsmall : ∀ d s, μ d s ≤ 1 / 4096)
    (a last : Site) (bs : List Site) (score : Logical → Logical → ℝ)
    (hscore : ∀ d k, score d k ≤ 1) :
    (∑ d, ∑ k, (finish d last (evolve d a bs (μ d)) k : ℝ) * score d k) ≤ 1 / 4 := by
  exact suffix_realScore_le_quarter_of_mass μ hμ (ten_bit_mass_bound μ hsmall)
    a last bs score hscore

end UnifiedEJM.WeightedTransfer
