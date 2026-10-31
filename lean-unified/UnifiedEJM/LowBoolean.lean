import OddEJM.Finite
import OddEJM.Character
import OddEJM.Walsh
import Mathlib.Tactic

/-!
# 二、三、四比特 Boolean 相位直线的精确边界障碍

以下求和直接使用计算基 Bits n。十进制编码仅作有限恒等式的书写工具；
最外层定理把它们接回物理 Pauli 拉回中的 unitBit、tailMask 和 adjacentMask。
-/

namespace UnifiedEJM.LowBoolean
open OddEJM
open scoped BigOperators

def decode2 (k : ℕ) : Bits 2 :=
  ![if k / 2 % 2 = 1 then 1 else 0, if k % 2 = 1 then 1 else 0]

def decode3 (k : ℕ) : Bits 3 :=
  ![if k / 4 % 2 = 1 then 1 else 0, if k / 2 % 2 = 1 then 1 else 0,
    if k % 2 = 1 then 1 else 0]

def decode4 (k : ℕ) : Bits 4 :=
  ![if k / 8 % 2 = 1 then 1 else 0, if k / 4 % 2 = 1 then 1 else 0,
    if k / 2 % 2 = 1 then 1 else 0, if k % 2 = 1 then 1 else 0]

noncomputable def eq2 : Fin 4 ≃ Bits 2 :=
  Equiv.ofBijective (fun k => decode2 k.val) (by decide)
noncomputable def eq3 : Fin 8 ≃ Bits 3 :=
  Equiv.ofBijective (fun k => decode3 k.val) (by decide)
noncomputable def eq4 : Fin 16 ≃ Bits 4 :=
  Equiv.ofBijective (fun k => decode4 k.val) (by decide)

/-- 以布尔函数值（不是其符号）定义的整数 Fourier 矩。 -/
def moment {n : ℕ} (q : Bits n → Bit) (h : Bits n) : ℤ :=
  ∑ z, ((q z).val : ℤ) * intSign (dot h z)

theorem bitSign_val (b : Bit) : bitSign b = 1 - 2 * (b.val : ℂ) := by
  rcases bit_cases b with rfl | rfl <;>
    norm_num [bitSign, show (1 : Bit).val = 1 by decide]

/-- 非零字符处，符号 Walsh 和与布尔值矩之间的真实有限和等式。 -/
theorem walsh_eq_neg_two_moment {n : ℕ} (q : Bits n → Bit) (h : Bits n)
    (hh : h ≠ 0) : walsh q h = -2 * (moment q h : ℂ) := by
  have hp (z : Bits n) : bitSign (q z + dot h z) =
      character h z - 2 * ((q z).val : ℂ) * (intSign (dot h z) : ℂ) := by
    rw [bitSign_add, bitSign_val (q z), intSign_cast]
    unfold character
    ring
  unfold walsh
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, character_sum, ite_eq_right hh]
  simp only [moment, Int.cast_sum, Int.cast_mul, Int.cast_natCast, zero_sub]
  rw [show (∑ z, 2 * ((q z).val : ℂ) * (intSign (dot h z) : ℂ)) =
    2 * ∑ z, ((q z).val : ℂ) * (intSign (dot h z) : ℂ) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring]
  ring

theorem walsh_re_eq_neg_two_moment {n : ℕ} (q : Bits n → Bit) (h : Bits n)
    (hh : h ≠ 0) : (walsh q h).re = -2 * (moment q h : ℝ) := by
  rw [walsh_eq_neg_two_moment q h hh]
  norm_num [Complex.mul_re]

theorem moment_eq_of_walsh {n : ℕ} (q : Bits n → Bit) (h : Bits n)
    (hh : h ≠ 0) (s k : Bit)
    (hw : (walsh q h).re = 2 * ((s.val : ℝ) + (k.val : ℝ) - 1)) :
    moment q h = 1 - (s.val : ℤ) - (k.val : ℤ) := by
  rw [walsh_re_eq_neg_two_moment q h hh] at hw
  have hr : (moment q h : ℝ) = 1 - (s.val : ℝ) - (k.val : ℝ) := by linarith
  exact_mod_cast hr

theorem moment3_one (q : Bits 3 → Bit) : moment q (decode3 1) =
    (q (decode3 0)).val - (q (decode3 1)).val + (q (decode3 2)).val -
    (q (decode3 3)).val + (q (decode3 4)).val - (q (decode3 5)).val +
    (q (decode3 6)).val - (q (decode3 7)).val := by
  unfold moment
  rw [← eq3.sum_comp]
  norm_num [eq3, decode3, dot, intSign, Fin.sum_univ_succ]
  ring

theorem moment3_four (q : Bits 3 → Bit) : moment q (decode3 4) =
    (q (decode3 0)).val + (q (decode3 1)).val + (q (decode3 2)).val +
    (q (decode3 3)).val - (q (decode3 4)).val - (q (decode3 5)).val -
    (q (decode3 6)).val - (q (decode3 7)).val := by
  unfold moment
  rw [← eq3.sum_comp]
  norm_num [eq3, decode3, dot, intSign, Fin.sum_univ_succ]
  ring

/-- 四个边界字符相加：所有未指定的六个真值严格消去。 -/
def signTable4 (h z : ℕ) : ℤ :=
  if ((h/8%2)*(z/8%2) + (h/4%2)*(z/4%2) +
      (h/2%2)*(z/2%2) + (h%2)*(z%2)) % 2 = 0 then 1 else -1

theorem signTable4_correct : ∀ h z : Fin 16,
    intSign (dot (decode4 h.val) (decode4 z.val)) = signTable4 h.val z.val := by decide

theorem moment4_fin (q : Bits 4 → Bit) (h : Fin 16) :
    moment q (decode4 h.val) =
      ∑ z : Fin 16, ((q (decode4 z.val)).val : ℤ) * signTable4 h.val z.val := by
  unfold moment
  rw [← eq4.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  change ((q (decode4 z.val)).val : ℤ) * intSign (dot (decode4 h.val) (decode4 z.val)) = _
  rw [signTable4_correct]

theorem moment4_boundary_sum (q : Bits 4 → Bit) :
    moment q (decode4 1) + moment q (decode4 3) +
      moment q (decode4 7) + moment q (decode4 15) =
    4 * (q (decode4 0)).val - 4 * (q (decode4 1)).val -
    2 * (q (decode4 2)).val + 2 * (q (decode4 3)).val +
    2 * (q (decode4 6)).val - 2 * (q (decode4 7)).val +
    2 * (q (decode4 8)).val - 2 * (q (decode4 9)).val +
    2 * (q (decode4 12)).val - 2 * (q (decode4 13)).val := by
  rw [moment4_fin q ⟨1, by omega⟩, moment4_fin q ⟨3, by omega⟩,
    moment4_fin q ⟨7, by omega⟩, moment4_fin q ⟨15, by omega⟩]
  norm_num [signTable4, Fin.sum_univ_succ]
  ring

/-- 三比特的两条真实 Walsh 方程已迫使两个四律参数都为零。 -/
theorem three_qubit_parameters_zero (q : Bits 3 → Bit) (s k : Bit)
    (hq0 : q 0 = 1)
    (hI : ∀ a ∈ ({1,2,3,4,5} : Finset ℕ), q (decode3 a) = s)
    (hII : ∀ a ∈ ({6,7} : Finset ℕ), q (decode3 a) = k)
    (hw1 : (walsh q (decode3 1)).re = 2 * ((s.val : ℝ) + (k.val : ℝ) - 1))
    (hw4 : (walsh q (decode3 4)).re = 2 * ((s.val : ℝ) + (k.val : ℝ) - 1)) :
    s = 0 ∧ k = 0 := by
  have hz : decode3 0 = 0 := by decide
  have h1 := moment_eq_of_walsh q (decode3 1) (by decide) s k hw1
  have h4 := moment_eq_of_walsh q (decode3 4) (by decide) s k hw4
  rw [moment3_one, hz, hq0, hI 1 (by decide), hI 2 (by decide),
    hI 3 (by decide), hI 4 (by decide), hI 5 (by decide),
    hII 6 (by decide), hII 7 (by decide)] at h1
  rw [moment3_four, hz, hq0, hI 1 (by decide), hI 2 (by decide),
    hI 3 (by decide), hI 4 (by decide), hI 5 (by decide),
    hII 6 (by decide), hII 7 (by decide)] at h4
  simp only [show (1 : Bit).val = 1 by decide, Nat.cast_one] at h1 h4
  have hk : (k.val : ℤ) = 0 := by linarith
  have hs : (s.val : ℤ) = 0 := by linarith
  constructor
  · exact ((ZMod.val_eq_zero s).mp (by exact_mod_cast hs))
  · exact ((ZMod.val_eq_zero k).mp (by exact_mod_cast hk))

/-- 四比特所有支持均无正弦分支；本证明不枚举支持函数。 -/
theorem four_qubit_sine_parameter_zero (q : Bits 4 → Bit) (s k : Bit)
    (hq0 : q 0 = 1)
    (hI : ∀ a ∈ ({1,2,3,8,9} : Finset ℕ), q (decode4 a) = s)
    (hII : ∀ a ∈ ({6,7,12,13} : Finset ℕ), q (decode4 a) = k)
    (hw : ∀ h ∈ ({1,3,7,15} : Finset ℕ),
      (walsh q (decode4 h)).re = 2 * ((s.val : ℝ) + (k.val : ℝ) - 1)) :
    k = 0 := by
  have h1 := moment_eq_of_walsh q (decode4 1) (by decide) s k (hw 1 (by decide))
  have h3 := moment_eq_of_walsh q (decode4 3) (by decide) s k (hw 3 (by decide))
  have h7 := moment_eq_of_walsh q (decode4 7) (by decide) s k (hw 7 (by decide))
  have h15 := moment_eq_of_walsh q (decode4 15) (by decide) s k (hw 15 (by decide))
  have hb := moment4_boundary_sum q
  have hz : decode4 0 = 0 := by decide
  rw [hz, hq0, hI 1 (by decide), hI 2 (by decide), hI 3 (by decide),
    hI 8 (by decide), hI 9 (by decide), hII 6 (by decide),
    hII 7 (by decide), hII 12 (by decide), hII 13 (by decide)] at hb
  simp only [show (1 : Bit).val = 1 by decide, Nat.cast_one] at hb
  have hk : (k.val : ℤ) = 0 := by omega
  exact (ZMod.val_eq_zero k).mp (by exact_mod_cast hk)

/-- 逐门拉回表的五种 I 类翻转及内部两种 II 类翻转。
这些条件的下标是物理位下标；后面有限十进制表只用于证明。 -/
structure PullbackValues {n : ℕ} (q : Bits n → Bit) (s k : Bit) : Prop where
  firstX : q (unitBit n 0) = s
  firstY : q (unitBit n 0 + unitBit n (n - 1)) = s
  localZ : q (unitBit n (n - 1)) = s
  lastX : q (unitBit n (n - 2)) = s
  lastY : q (unitBit n (n - 2) + unitBit n (n - 1)) = s
  internalX : ∀ j, 1 ≤ j → j < n - 1 → q (adjacentMask n j) = k
  internalY : ∀ j, 1 ≤ j → j < n - 1 → q (internalYMask n j) = k

theorem values3_I (q : Bits 3 → Bit) (s k : Bit) (hv : PullbackValues q s k) :
    ∀ a ∈ ({1,2,3,4,5} : Finset ℕ), q (decode3 a) = s := by
  intro a ha
  have hd : decode3 a = unitBit 3 0 ∨
      decode3 a = unitBit 3 0 + unitBit 3 2 ∨
      decode3 a = unitBit 3 2 ∨ decode3 a = unitBit 3 1 ∨
      decode3 a = unitBit 3 1 + unitBit 3 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hd with h | h | h | h | h
  · simpa only [h] using hv.firstX
  · simpa only [h] using hv.firstY
  · simpa only [h] using hv.localZ
  · simpa only [h] using hv.lastX
  · simpa only [h] using hv.lastY

theorem values3_II (q : Bits 3 → Bit) (s k : Bit) (hv : PullbackValues q s k) :
    ∀ a ∈ ({6,7} : Finset ℕ), q (decode3 a) = k := by
  intro a ha
  have hd : decode3 a = adjacentMask 3 1 ∨ decode3 a = internalYMask 3 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> decide
  rcases hd with h | h
  · rw [h]; exact hv.internalX 1 (by omega) (by omega)
  · rw [h]; exact hv.internalY 1 (by omega) (by omega)

theorem values4_I (q : Bits 4 → Bit) (s k : Bit) (hv : PullbackValues q s k) :
    ∀ a ∈ ({1,2,3,8,9} : Finset ℕ), q (decode4 a) = s := by
  intro a ha
  have hd : decode4 a = unitBit 4 0 ∨
      decode4 a = unitBit 4 0 + unitBit 4 3 ∨
      decode4 a = unitBit 4 3 ∨ decode4 a = unitBit 4 2 ∨
      decode4 a = unitBit 4 2 + unitBit 4 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hd with h | h | h | h | h
  · simpa only [h] using hv.firstX
  · simpa only [h] using hv.firstY
  · simpa only [h] using hv.localZ
  · simpa only [h] using hv.lastX
  · simpa only [h] using hv.lastY

theorem values4_II (q : Bits 4 → Bit) (s k : Bit) (hv : PullbackValues q s k) :
    ∀ a ∈ ({6,7,12,13} : Finset ℕ), q (decode4 a) = k := by
  intro a ha
  have hd : decode4 a = adjacentMask 4 1 ∨ decode4 a = internalYMask 4 1 ∨
      decode4 a = adjacentMask 4 2 ∨ decode4 a = internalYMask 4 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  rcases hd with h | h | h | h
  · rw [h]; exact hv.internalX 1 (by omega) (by omega)
  · rw [h]; exact hv.internalY 1 (by omega) (by omega)
  · rw [h]; exact hv.internalX 2 (by omega) (by omega)
  · rw [h]; exact hv.internalY 2 (by omega) (by omega)

/-- 接口使用真实首位 X 及各位 Z 的拉回字符，不假设抽象真值表。 -/
theorem three_qubit_physical_parameters_zero (q : Bits 3 → Bit) (s k : Bit)
    (hq0 : q 0 = 1) (hv : PullbackValues q s k)
    (hx : (walsh q (unitBit 3 0)).re = 2 * ((s.val : ℝ) + (k.val : ℝ) - 1))
    (hz : ∀ j, j < 3 → (walsh q (tailMask 3 j)).re =
      2 * ((s.val : ℝ) + (k.val : ℝ) - 1)) : s = 0 ∧ k = 0 := by
  apply three_qubit_parameters_zero q s k hq0 (values3_I q s k hv) (values3_II q s k hv)
  · simpa only [show decode3 1 = tailMask 3 2 by decide] using hz 2 (by omega)
  · simpa only [show decode3 4 = unitBit 3 0 by decide] using hx

/-- 四比特障碍仅使用四个物理 Z 字符和逐门翻转值。 -/
theorem four_qubit_physical_sine_parameter_zero (q : Bits 4 → Bit) (s k : Bit)
    (hq0 : q 0 = 1) (hv : PullbackValues q s k)
    (hz : ∀ j, j < 4 → (walsh q (tailMask 4 j)).re =
      2 * ((s.val : ℝ) + (k.val : ℝ) - 1)) : k = 0 := by
  apply four_qubit_sine_parameter_zero q s k hq0 (values4_I q s k hv) (values4_II q s k hv)
  intro h hh
  have he : decode4 h = tailMask 4 0 ∨ decode4 h = tailMask 4 1 ∨
      decode4 h = tailMask 4 2 ∨ decode4 h = tailMask 4 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl <;> decide
  rcases he with he | he | he | he
  · rw [he]; exact hz 0 (by omega)
  · rw [he]; exact hz 1 (by omega)
  · rw [he]; exact hz 2 (by omega)
  · rw [he]; exact hz 3 (by omega)

/-- 两比特 I 类翻转覆盖全部非零物理输入。 -/
theorem two_qubit_support_form (q : Bits 2 → Bit) (s k : Bit)
    (hq0 : q 0 = 1) (hv : PullbackValues q s k) :
    q = fun z => if z = 0 then 1 else s := by
  funext z
  by_cases hz : z = 0
  · simp [hz, hq0]
  · rw [ite_eq_right hz]
    have hc : z = unitBit 2 0 ∨ z = unitBit 2 1 ∨ z = unitBit 2 0 + unitBit 2 1 := by
      revert z
      decide
    rcases hc with h | h | h
    · rw [h]; exact hv.firstX
    · rw [h]; exact hv.localZ
    · rw [h]; exact hv.firstY

theorem two_qubit_support_dichotomy (q : Bits 2 → Bit) (s k : Bit)
    (hq0 : q 0 = 1) (hv : PullbackValues q s k) :
    q = (fun z => if z = 0 then 1 else 0) ∨ q = (fun _ => 1) := by
  have hf := two_qubit_support_form q s k hq0 hv
  rcases bit_cases s with hs | hs
  · left; simpa [hs] using hf
  · right; simpa [hs] using hf

theorem two_qubit_walsh_first (q : Bits 2 → Bit) (s k : Bit)
    (hq0 : q 0 = 1) (hv : PullbackValues q s k) :
    (walsh q (unitBit 2 0)).re = 2 * ((s.val : ℝ) - 1) := by
  have hm : moment q (unitBit 2 0) = 1 - (s.val : ℤ) := by
    unfold moment
    rw [← eq2.sum_comp]
    norm_num [eq2, decode2, dot, intSign, Fin.sum_univ_succ, unitBit]
    have he0 : (![0,0] : Bits 2) = 0 := by decide
    have he1 : (![0,1] : Bits 2) = unitBit 2 1 := by decide
    have he2 : (![1,0] : Bits 2) = unitBit 2 0 := by decide
    have he3 : (![1,1] : Bits 2) = unitBit 2 0 + unitBit 2 1 := by decide
    rw [he0, he1, he2, he3, hq0, hv.localZ, hv.firstX, hv.firstY]
    rw [show (ZMod.cast (1 : Bit) : ℤ) = 1 by rfl]
    ring
  rw [walsh_re_eq_neg_two_moment q (unitBit 2 0) (by decide), hm]
  push_cast
  ring

/-- 剩余的两种三角函数在全实轴上的绝对值上界。 -/
theorem no_sine_law_bound (s : Bit) (t : ℝ) :
    |(1 - (s.val : ℝ)) + (s.val : ℝ) * Real.cos t| ≤ 1 := by
  rcases bit_cases s with rfl | rfl
  · norm_num
  · simpa only [show (1 : Bit).val = 1 by decide, Nat.cast_one,
      sub_self, zero_add, one_mul] using Real.abs_cos_le_one t

theorem scaled_no_sine_law_bound (c : ℝ) (hc : 0 ≤ c) (s : Bit) (t : ℝ) :
    |c * ((1 - (s.val : ℝ)) + (s.val : ℝ) * Real.cos t)| ≤ c := by
  rw [abs_mul, abs_of_nonneg hc]
  simpa using mul_le_mul_of_nonneg_left (no_sine_law_bound s t) hc

end UnifiedEJM.LowBoolean

