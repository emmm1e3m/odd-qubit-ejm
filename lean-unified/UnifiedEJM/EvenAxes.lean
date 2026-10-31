import UnifiedEJM.EvenSeed
import UnifiedEJM.Phase
import UnifiedEJM.Projective

namespace UnifiedEJM.EvenFamily
open OddEJM Complex
open UnifiedEJM.EvenWalsh
open scoped BigOperators

/-- 与论文原始基点相位及两个删除物理零点的支持完全一致。 -/
theorem diagonal_original {n : ℕ} (hn : 1 ≤ n) (α β : ℝ) (z : Bits n) :
    diagonal n α β z = originalDiagonal z *
      anglePhase α ^ (dA z).val * anglePhase β ^ (UnifiedEJM.phaseSupport z).val := by
  by_cases hz : z = 0
  · subst z
    simp [diagonal, EvenRaw.raw, dA, UnifiedEJM.phaseSupport,
      originalDiagonal, originalExponent_zero hn]
  · rw [originalDiagonal_eq_rawPhase_zero hn]
    simp [diagonal, EvenRaw.raw, EvenRaw.background, dA, UnifiedEJM.phaseSupport,
      OddEJM.rawPhase, hz, mul_assoc]

/-- β轴逐列恢复新版全n增强族。 -/
theorem second_axis_measurement (n : ℕ) (β : ℝ) (label : Bits n) :
    measurement n 0 β label = UnifiedEJM.measurement n β label := by
  unfold measurement Physical.measurement UnifiedEJM.measurement
  congr 1
  funext z
  simp [diagonal, EvenRaw.raw, EvenRaw.background, UnifiedEJM.rawPhase, mul_assoc]

/-- α轴逐列恢复前作明确的AND支持，而非仅恢复半径。 -/
theorem first_axis_measurement {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (label : Bits n) :
    measurement n α 0 label =
      circuit (fun z => normFactor n *
        (originalDiagonal z * anglePhase α ^ (dA z).val) * character label z) := by
  unfold measurement Physical.measurement
  congr 1
  funext z
  rw [diagonal_original hn]
  simp

lemma angle_injective {x y : ℝ}
    (hx : x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (hy : y ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (he : anglePhase x = anglePhase y) : x=y := by
  apply Real.injOn_sin hx hy
  have hh := congrArg Complex.im he
  simpa [anglePhase, Complex.exp_ofReal_mul_I_im] using hh

/-- 两个见证输入分别读取两个参数；固定零点规范下无参数冗余。 -/
theorem diagonal_parameter_injective {n : ℕ} (hn : 5 ≤ n) (he : Even n)
    {α α' β β' : ℝ}
    (hα : α ∈ Geometry.parameterInterval) (hα' : α' ∈ Geometry.parameterInterval)
    (hβ : β ∈ Geometry.parameterInterval) (hβ' : β' ∈ Geometry.parameterInterval)
    (h : diagonal n α β = diagonal n α' β') : α=α' ∧ β=β' := by
  have hf := UnifiedEJM.MaskFacts.firstX hn
  have hi := UnifiedEJM.MaskFacts.internalX hn 1 (by omega) (by omega)
  have hzA := congrFun h (unitBit n 0)
  have hzB := congrFun h (adjacentMask n 1)
  have haA : qA (unitBit n 0) = 1 := qA_of_ezero ezero_first
  have hbA : UnifiedEJM.q (unitBit n 0) = 0 := hf.hq
  have haB := qA_adjacent hn he 1 (by omega) (by omega)
  have hbB : UnifiedEJM.q (adjacentMask n 1) = 1 := hi.hq
  simp only [diagonal, EvenRaw.raw, if_neg hf.ha, EvenRaw.background, haA, hbA,
    ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.one_mod, pow_one, pow_zero, mul_one] at hzA
  simp only [diagonal, EvenRaw.raw, if_neg hi.ha, EvenRaw.background, haB, hbB,
    ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.one_mod, pow_one, pow_zero, mul_one] at hzB
  have hu : anglePhase α = anglePhase α' :=
    (mul_left_cancel₀ (pow_ne_zero _ I_ne_zero)) ((mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero)) hzA)
  have hv : anglePhase β = anglePhase β' :=
    (mul_left_cancel₀ (pow_ne_zero _ I_ne_zero)) ((mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero)) hzB)
  exact ⟨angle_injective hα hα' hu, angle_injective hβ hβ' hv⟩

/-- 有序实际测量投影在参数矩形内单射，尤其母族是真正二维。 -/
theorem ordered_measurement_parameter_injective {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    {α α' β β' : ℝ}
    (hα : α ∈ Geometry.parameterInterval) (hα' : α' ∈ Geometry.parameterInterval)
    (hβ : β ∈ Geometry.parameterInterval) (hβ' : β' ∈ Geometry.parameterInterval)
    (h : ∀ label, Physical.projector (measurement n α β label) =
      Physical.projector (measurement n α' β' label)) : α=α' ∧ β=β' := by
  apply diagonal_parameter_injective (by omega) he hα hα' hβ hβ'
  apply (Physical.ordered_projectors_injective_fixed_origin (by omega)
    (diagonal n α β) (diagonal n α' β') (diagonal_unit n α β)
    (diagonal_unit n α' β') (diagonal_origin n α β) (diagonal_origin n α' β')).mp
  exact h

end UnifiedEJM.EvenFamily
