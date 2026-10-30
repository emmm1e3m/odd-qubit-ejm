import OddEJM.Core
import Mathlib.Tactic

/-!
# 固定五位布尔函数的内核可核查证书

所有有限结论均由 `decide` 生成内核检查的证明；不使用 `native_decide`。
五位十进制编码以第零坐标为最高位，与论文表格一致。
-/

namespace OddEJM

open scoped BigOperators

/-- 五位最高位在前的十进制解码。 -/
def decode5 (k : ℕ) : Bits 5 :=
  ![((k / 16 : ℕ) : Bit), ((k / 8 : ℕ) : Bit), ((k / 4 : ℕ) : Bit),
    ((k / 2 : ℕ) : Bit), (k : Bit)]

/-- 字符符号的整数版本，有限求和完全在整数内完成。 -/
def intSign (b : Bit) : ℤ := if b = 0 then 1 else -1

/-- 将布尔值提升到整数0或1，差值不再模2。 -/
def qInt (v : Bits 5) : ℤ := (Q v).val

def qSupport : Finset ℕ := {0,5,6,7,11,12,13,14,18,20,21,23,24,25,26,31}

/-- 多项式定义与论文的完整32点真值表相同。 -/
theorem q_truth_table : ∀ k : Fin 32,
    Q (decode5 k) = if (k : ℕ) ∈ qSupport then 1 else 0 := by
  decide

/-- 直接在全部五位函数上计数，Q恰有16个取值1的输入。 -/
theorem q_balanced :
    ((Finset.univ : Finset (Bits 5)).filter (fun v => Q v = 1)).card = 16 := by
  decide

@[simp] theorem Q_zero : Q 0 = 1 := by decide

/-- 相位因子为-i的五种缺陷翻转输入。 -/
theorem q_defect_zero : ∀ k ∈ ({1,2,3,16,17} : Finset ℕ),
    Q (decode5 k) = 0 := by decide

/-- 相位因子为-1的六种缺陷翻转输入。 -/
theorem q_defect_one : ∀ k ∈ ({6,7,12,13,24,25} : Finset ℕ),
    Q (decode5 k) = 1 := by decide

/-- 论文中的整数Walsh分层系数N_s(A,H)。 -/
def walshCoeff (A H : Bits 5) (s : ℤ) : ℤ :=
  ∑ v, if qInt v - qInt (v + A) = s then intSign (dot H v) else 0

/-- 覆盖所有奇数n的16种五位(A,H)标签。 -/
def certificatePairs : Finset (ℕ × ℕ) :=
  {(16,16), (17,15), (1,31), (24,24), (25,23), (1,15), (12,12), (13,11),
    (1,7), (6,6), (7,5), (1,3), (2,3), (3,2), (1,1), (13,7)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- 16行乘3个整数系数的完整有限证书。 -/
theorem walshCoeff_checked : ∀ p ∈ certificatePairs,
    ∀ s ∈ ({-1,0,1} : Finset ℤ),
      walshCoeff (decode5 p.1) (decode5 p.2) s = 0 := by
  decide

lemma qInt_cases (v : Bits 5) : qInt v = 0 ∨ qInt v = 1 := by
  have hv := (Q v).val_lt
  unfold qInt
  omega

lemma qdiff_cases (A v : Bits 5) :
    qInt v - qInt (v + A) = -1 ∨
    qInt v - qInt (v + A) = 0 ∨
    qInt v - qInt (v + A) = 1 := by
  rcases qInt_cases v with h | h <;>
    rcases qInt_cases (v + A) with h' | h' <;> simp [h, h']

/-- 所有整数层系数都为零，包括不可能出现的其他差值。 -/
theorem walshCoeff_zero {a h : ℕ} (hp : (a,h) ∈ certificatePairs) (s : ℤ) :
    walshCoeff (decode5 a) (decode5 h) s = 0 := by
  by_cases hs : s ∈ ({-1,0,1} : Finset ℤ)
  · exact walshCoeff_checked (a,h) hp s hs
  · unfold walshCoeff
    apply Finset.sum_eq_zero
    intro v _
    have hd : qInt v - qInt (v + decode5 a) ≠ s := by
      intro heq
      apply hs
      rcases qdiff_cases (decode5 a) v with hd | hd | hd <;>
        simp_all
    simp [hd]

@[simp] lemma intSign_cast (b : Bit) : (intSign b : ℂ) = bitSign b := by
  simp only [intSign, bitSign]
  split_ifs <;> norm_num

lemma walshCoeff_cast (A H : Bits 5) (s : ℤ) :
    (walshCoeff A H s : ℂ) =
      ∑ v, if qInt v - qInt (v + A) = s then bitSign (dot H v) else 0 := by
  simp [walshCoeff, Int.cast_sum]

/-- 证书消去任意仅依赖整数布尔差值的复权重。 -/
theorem walsh_weighted_zero {a h : ℕ} (hp : (a,h) ∈ certificatePairs)
    (f : ℤ → ℂ) :
    ∑ v : Bits 5, bitSign (dot (decode5 h) v) *
      f (qInt v - qInt (v + decode5 a)) = 0 := by
  calc
    _ = ∑ v : Bits 5,
        ((if qInt v - qInt (v + decode5 a) = -1 then bitSign (dot (decode5 h) v) else 0) * f (-1) +
        (if qInt v - qInt (v + decode5 a) = 0 then bitSign (dot (decode5 h) v) else 0) * f 0 +
        (if qInt v - qInt (v + decode5 a) = 1 then bitSign (dot (decode5 h) v) else 0) * f 1) := by
      apply Finset.sum_congr rfl
      intro v _
      rcases qdiff_cases (decode5 a) v with hd | hd | hd <;> simp [hd]
    _ = (walshCoeff (decode5 a) (decode5 h) (-1) : ℂ) * f (-1) +
        (walshCoeff (decode5 a) (decode5 h) 0 : ℂ) * f 0 +
        (walshCoeff (decode5 a) (decode5 h) 1 : ℂ) * f 1 := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, walshCoeff_cast]
    _ = 0 := by simp [walshCoeff_zero hp]

/-- 提升证明使用的三个固定Q字符和。 -/
theorem q_walsh_int_checked : ∀ h ∈ ({31,15,7} : Finset ℕ),
    ∑ v : Bits 5, intSign (Q v + dot (decode5 h) v) = 0 := by decide

theorem q_walsh_zero {h : ℕ} (hh : h ∈ ({31,15,7} : Finset ℕ)) :
    walsh Q (decode5 h) = 0 := by
  have hc := congrArg (fun z : ℤ => (z : ℂ)) (q_walsh_int_checked h hh)
  simpa [walsh, Int.cast_sum] using hc

lemma qVal_cases (v : Bits 5) : (Q v).val = 0 ∨ (Q v).val = 1 := by
  have hv := (Q v).val_lt
  omega

/-- 单位模相位的五位背景和为零。 -/
theorem walsh_phase_zero {a h : ℕ} (hp : (a,h) ∈ certificatePairs)
    (u : ℂ) (hu : u * star u = 1) :
    ∑ v : Bits 5, bitSign (dot (decode5 h) v) *
      (u ^ (Q v).val * star (u ^ (Q (v + decode5 a)).val)) = 0 := by
  change u * (starRingEnd ℂ) u = 1 at hu
  let f : ℤ → ℂ := fun s => if s = -1 then star u else if s = 0 then 1 else u
  calc
    _ = ∑ v : Bits 5, bitSign (dot (decode5 h) v) *
        f (qInt v - qInt (v + decode5 a)) := by
      apply Finset.sum_congr rfl
      intro v _
      rcases qVal_cases v with hv | hv <;>
        rcases qVal_cases (v + decode5 a) with ha | ha <;>
          simp [qInt, f, hv, ha, hu]
    _ = 0 := walsh_weighted_zero hp f


end OddEJM



