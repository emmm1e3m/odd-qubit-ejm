import UnifiedEJM.BooleanMaximum
import UnifiedEJM.Regularity

/-! Boolean模型的形式结论与实际测量四面体、全参数共同半径之间的连接。 -/
noncomputable section
namespace UnifiedEJM.BooleanLines
open OddEJM Complex
open UnifiedEJM.LowBooleanPhysical
open scoped BigOperators

/-- 局部等平方在Boolean线上延拓为全参数共同signed分量，故每列均有实际规则四面体。 -/
theorem regular_global_measurement {n : ℕ} (hn : 2≤n)
    (q : Bits n → Bit) (hq : q 0=1) (hr : LocallyRegular q) (t : ℝ) :
    Regularity.Regular (raw q (anglePhase t)) (modelRadius q t) := by
  apply (Regularity.regular_iff_seed_squares hn _ _).mpr
  refine ⟨by unfold modelRadius; positivity,?_⟩
  intro j
  obtain ⟨hx,hy,hz⟩ := regular_global_components hn q hq hr t j.val j.isLt
  change seedX q t j.val^2=(modelRadius q t)^2/3 ∧
    seedY q t j.val^2=(modelRadius q t)^2/3 ∧
    seedZ q t j.val^2=(modelRadius q t)^2/3
  have hrad : (modelRadius q t)^2/3=seedX q t 0^2 := by
    simp only [modelRadius,mul_pow,Real.sq_sqrt (show (0:ℝ)≤3 by norm_num),sq_abs]
    ring
  rw [hrad,hx,hy,hz]
  split_ifs <;> simp

/-- 任意列、任意物理位的真实偏迹Bloch半径，与优化量严格一致。 -/
theorem actual_all_column_radius {n : ℕ} (hn : 2≤n)
    (q : Bits n → Bit) (hq : q 0=1) (hr : LocallyRegular q)
    (t : ℝ) (label : Bits n) (j : Fin n) :
    Regularity.radius (Physical.measurement (raw q (anglePhase t)) label) j=modelRadius q t :=
  Regularity.regular_column_radius (regular_global_measurement hn q hq hr t) j label

def LocallyGeometric {n : ℕ} (q : Bits n → Bit) : Prop :=
  ∀ᶠ t in nhds (0:ℝ), ∃ r : ℝ, Regularity.Regular (raw q (anglePhase t)) r

/-- 完整实际测量几何与计算中使用的局部等平方条件双向等价。 -/
theorem locally_regular_iff_geometric {n : ℕ} (hn : 2≤n)
    (q : Bits n → Bit) (hq : q 0=1) : LocallyRegular q ↔ LocallyGeometric q := by
  constructor
  · intro hr
    exact Filter.Eventually.of_forall (fun t=>⟨modelRadius q t,regular_global_measurement hn q hq hr t⟩)
  · intro hr
    filter_upwards [hr] with t ht
    obtain ⟨r,hr⟩ := ht
    intro j hj
    have hj' := Regularity.seed_squares hn hr (⟨j,hj⟩:Fin n)
    have h0 := (Regularity.seed_squares hn hr (⟨0,by omega⟩:Fin n)).1
    change seedX q t j^2=r^2/3 ∧ seedY q t j^2=r^2/3 ∧ seedZ q t j^2=r^2/3 at hj'
    change seedX q t 0^2=r^2/3 at h0
    exact ⟨hj'.1.trans h0.symm,hj'.2.1.trans h0.symm,hj'.2.2.trans h0.symm⟩

theorem regular_radius_identification {n : ℕ} (hn : 2≤n)
    (q : Bits n → Bit) (t r : ℝ) (hr : Regularity.Regular (raw q (anglePhase t)) r) :
    r=modelRadius q t := by
  have h := Regularity.r_eq_sqrt_three_abs_seed_X hn hr (⟨0,by omega⟩:Fin n)
  exact h

/-- 按原始f0和d(0)=0定义的实际几何模型：先在基点邻域规则，再取任意规则参数值的共同半径。 -/
def geometricRadiusValues (n : ℕ) : Set ℝ :=
  {r | ∃ d : Bits n → Bit, d 0=0 ∧
    (∀ᶠ t in nhds (0:ℝ), ∃ s : ℝ, Regularity.GeometricRegular (originalLine d t) s) ∧
    ∃ t : ℝ, Regularity.GeometricRegular (originalLine d t) r}

/-- 并未优化代用公式：可达半径集就是完整原始测量几何的可达半径集。 -/
theorem geometric_values_eq {n : ℕ} (hn : 2≤n) : geometricRadiusValues n=radiusValues n := by
  unfold geometricRadiusValues
  simp_rw [Regularity.geometric_iff_regular hn]
  ext r
  constructor
  · rintro ⟨d,hd,hlocal,t,ht⟩
    have hl : LocallyGeometric (qOfSupport d) := by
      filter_upwards [hlocal] with u hu
      simpa only [raw_eq_originalLine (by omega) d hd] using hu
    have hr : LocallyRegular (qOfSupport d) :=
      (locally_regular_iff_geometric hn _ (qOfSupport_zero d)).mpr hl
    refine ⟨qOfSupport d,qOfSupport_zero d,hr,t,?_⟩
    apply regular_radius_identification hn
    simpa only [raw_eq_originalLine (by omega) d hd] using ht
  · rintro ⟨q,hq,hr,t,rfl⟩
    let d := supportOfQ q
    have hd : d 0=0 := supportOfQ_zero q
    have he (u : ℝ) : originalLine d u=raw q (anglePhase u) := by
      rw [←raw_eq_originalLine (by omega) d hd,qOfSupport_supportOfQ q hq]
    refine ⟨d,hd,?_,t,?_⟩
    · apply Filter.Eventually.of_forall
      intro u
      exact ⟨modelRadius q u,by rw [he]; exact regular_global_measurement hn q hq hr u⟩
    · rw [he]
      exact regular_global_measurement hn q hq hr t

/-- 论文主定理2的实际测量版本：低维rE，高维2rE，均为达到的最大值。 -/
theorem actual_boolean_model_exact_maximum {n : ℕ} (hn : 2≤n) :
    IsGreatest (geometricRadiusValues n) (modelMaximum n) := by
  rw [geometric_values_eq hn]
  exact boolean_model_exact_maximum hn

end UnifiedEJM.BooleanLines
