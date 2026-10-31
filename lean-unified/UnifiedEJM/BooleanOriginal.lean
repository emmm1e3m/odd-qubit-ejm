import UnifiedEJM.BooleanLines
import OddEJM.OriginalPhase
import UnifiedEJM.Physical

/-! 从原基本对称相位与任意Boolean生成元到形式化四律。 -/
noncomputable section
namespace UnifiedEJM.BooleanLines
open OddEJM Complex
open scoped BigOperators

/-- 物理生成元d在零串为0；背景q只在这个串上补1。 -/
def qOfSupport {n : ℕ} (d : Bits n → Bit) (z : Bits n) : Bit :=
  if z=0 then 1 else d z

@[simp] theorem qOfSupport_zero {n : ℕ} (d : Bits n → Bit) : qOfSupport d 0=1 := by
  simp [qOfSupport]

def originalLine {n : ℕ} (d : Bits n → Bit) (t : ℝ) (z : Bits n) : ℂ :=
  originalDiagonal z * anglePhase t ^ (d z).val

/-- 原始基本对称多项式与有限和计算的逐振幅连接。 -/
theorem raw_eq_originalLine {n : ℕ} (hn : 1≤n) (d : Bits n → Bit) (hd : d 0=0)
    (t : ℝ) : raw (qOfSupport d) (anglePhase t)=originalLine d t := by
  funext z
  rw [originalLine, originalDiagonal_eq_rawPhase_zero hn]
  by_cases hz : z=0
  · subst z
    simp [raw,OddEJM.rawPhase,hd]
  · simp [raw,OddEJM.rawPhase,qOfSupport,hz]

theorem raw_unit {n : ℕ} (q : Bits n → Bit) (t : ℝ) (z : Bits n) :
    star (raw q (anglePhase t) z)*raw q (anglePhase t) z=1 := by
  have hn : ‖raw q (anglePhase t) z‖=1 := by
    by_cases hz : z=0 <;> simp [raw,hz,norm_pow]
  simpa [Complex.star_def,hn] using Complex.conj_mul' (raw q (anglePhase t) z)

theorem originalLine_unit {n : ℕ} (hn : 1≤n) (d : Bits n → Bit) (hd : d 0=0)
    (t : ℝ) (z : Bits n) : star (originalLine d t z)*originalLine d t z=1 := by
  rw [←raw_eq_originalLine hn d hd]
  exact raw_unit _ _ _

/-- 全部实际测量列始终正交，不依赖局部几何条件。 -/
theorem original_measurement_orthonormal {n : ℕ} (hn : 1≤n) (d : Bits n → Bit)
    (hd : d 0=0) (t : ℝ) (k l : Bits n) :
    inner (Physical.measurement (originalLine d t) k)
      (Physical.measurement (originalLine d t) l)=if k=l then 1 else 0 := by
  exact Physical.measurement_orthonormal (by omega) _ (originalLine_unit hn d hd t) k l

theorem original_seed_eq {n : ℕ} (hn : 1≤n) (d : Bits n → Bit) (hd : d 0=0) (t : ℝ) :
    Physical.seed (originalLine d t)=seed (qOfSupport d) t := by
  rw [←raw_eq_originalLine hn d hd]
  rfl

/-- 四律以四个显式公式陈述，而不是把它们作为模型假设。 -/
theorem law_explicit (s k : Bit) (t : ℝ) :
    (law s k).eval t=2 ∨ (law s k).eval t=2*Real.cos t ∨
    (law s k).eval t=2*(1-Real.sin t) ∨
    (law s k).eval t=2*(Real.cos t-Real.sin t) := by
  rcases bit_cases s with rfl|rfl <;> rcases bit_cases k with rfl|rfl <;>
    simp [law,Trig.eval,ZMod.val_one_eq_one_mod] <;> ring_nf <;> simp

/-- 直接针对原始相位测量：局部规则性必要的X1²=X2²已蕴含四律。 -/
theorem original_four_laws {n : ℕ} (hn : 3≤n) (d : Bits n → Bit) (hd : d 0=0)
    (hreg : ∀ᶠ t in nhds (0:ℝ),
      (pauliExpectation (Physical.seed (originalLine d t)) (unitBit n 0) 0 1).re^2 =
      (pauliExpectation (Physical.seed (originalLine d t)) (unitBit n 1) 0 1).re^2) :
    ∃ s k : Bit, ∀ t,
      (pauliExpectation (Physical.seed (originalLine d t)) (unitBit n 0) 0 1).re =
        (2/(2:ℝ)^n)*((1-s.val)+s.val*Real.cos t-k.val*Real.sin t) := by
  have hr : ∀ᶠ t in nhds (0:ℝ),
      seedX (qOfSupport d) t 0^2=seedX (qOfSupport d) t 1^2 := by
    filter_upwards [hreg] with t ht
    simpa [seedX,original_seed_eq (by omega) d hd] using ht
  refine ⟨qOfSupport d (unitBit n 0),qOfSupport d (adjacentMask n 1),?_⟩
  intro t
  rw [original_seed_eq (by omega) d hd]
  change seedX (qOfSupport d) t 0=_
  rw [actual_seed_four_law hn _ (qOfSupport_zero d) hr]
  simp only [law,Trig.eval]
  ring

/-- 共同四面体半径为sqrt(3)|m|，于是得到完整二值模型上界。 -/
theorem original_radius_bound {n : ℕ} (hn : 3≤n) (d : Bits n → Bit) (hd : d 0=0)
    (hreg : ∀ᶠ t in nhds (0:ℝ),
      (pauliExpectation (Physical.seed (originalLine d t)) (unitBit n 0) 0 1).re^2 =
      (pauliExpectation (Physical.seed (originalLine d t)) (unitBit n 1) 0 1).re^2) (t : ℝ) :
    Real.sqrt 3*|(pauliExpectation (Physical.seed (originalLine d t)) (unitBit n 0) 0 1).re|
      ≤ 2*(Real.sqrt 3/(2:ℝ)^(n-1)) := by
  have hr : ∀ᶠ t in nhds (0:ℝ),
      seedX (qOfSupport d) t 0^2=seedX (qOfSupport d) t 1^2 := by
    filter_upwards [hreg] with t ht
    simpa [seedX,original_seed_eq (by omega) d hd] using ht
  rw [original_seed_eq (by omega) d hd]
  change Real.sqrt 3*|seedX (qOfSupport d) t 0|≤_
  have hb := mul_le_mul_of_nonneg_left
    (actual_seed_bound hn _ (qOfSupport_zero d) hr t) (Real.sqrt_nonneg 3)
  have hp : (2:ℝ)^n=(2:ℝ)^(n-1)*2 := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤n)]
  convert hb using 1
  rw [hp]
  ring

end UnifiedEJM.BooleanLines
