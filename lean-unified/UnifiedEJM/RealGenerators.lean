import UnifiedEJM.BooleanMeasurement
import UnifiedEJM.Projective

noncomputable section
namespace UnifiedEJM.BooleanLines
open OddEJM Complex
open scoped BigOperators

/-- 允许两个值相等，因此包含常值生成元。 -/
def AtMostTwoRealValues {n : ℕ} (g : Bits n → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ z, g z = a ∨ g z = b

/-- 从真实实生成元定义的原始对角相位。 -/
def realGeneratorLine {n : ℕ} (g : Bits n → ℝ) (t : ℝ) (z : Bits n) : ℂ :=
  originalDiagonal z * anglePhase (t * g z)

/-- 常值情形取比例一及零Boolean函数；非恒定情形取相对零串的非零差值。 -/
theorem atMostTwoRealValues_normalize {n : ℕ} (g : Bits n → ℝ)
    (hg : AtMostTwoRealValues g) :
    ∃ (c : ℝ) (d : Bits n → Bit), c ≠ 0 ∧ d 0 = 0 ∧
      ∀ z, g z = g 0 + c * (d z).val := by
  classical
  by_cases hconstant : ∀ z, g z = g 0
  · refine ⟨1, fun _ => 0, one_ne_zero, rfl, ?_⟩
    intro z
    simpa using hconstant z
  · obtain ⟨w, hw⟩ := not_forall.mp hconstant
    obtain ⟨a, b, hab⟩ := hg
    have hvalues : ∀ z, g z = g 0 ∨ g z = g w := by
      intro z
      rcases hab 0 with h0 | h0 <;> rcases hab w with h1 | h1
      · exact (hw (h1.trans h0.symm)).elim
      · rcases hab z with hz | hz
        · exact Or.inl (hz.trans h0.symm)
        · exact Or.inr (hz.trans h1.symm)
      · rcases hab z with hz | hz
        · exact Or.inr (hz.trans h1.symm)
        · exact Or.inl (hz.trans h0.symm)
      · exact (hw (h1.trans h0.symm)).elim
    let d : Bits n → Bit := fun z => if g z = g 0 then 0 else 1
    refine ⟨g w - g 0, d, sub_ne_zero.mpr hw, by simp [d], ?_⟩
    intro z
    by_cases hz : g z = g 0
    · simp [d, hz]
    · have hzw := (hvalues z).resolve_left hz
      simp only [d, ite_eq_right hz, ZMod.val_one_eq_one_mod, Nat.one_mod,
        Nat.cast_one, mul_one]
      linarith

/-- 任意实际测量列随输入公共复因子线性变化。 -/
theorem measurement_global_scale {n : ℕ} (c : ℂ) (u : Bits n → ℂ)
    (label : Bits n) :
    Physical.measurement (fun z => c * u z) label =
      fun z => c * Physical.measurement u label z := by
  unfold Physical.measurement
  rw [← Physical.circuit_scale]
  congr 1
  funext z
  ring

/-- 单位公共相位保持每个完整秩一测量投影；不需要另加态归一化假设。 -/
theorem projector_global_phase {n : ℕ} (c : ℂ) (hc : star c * c = 1) (v : Vec n) :
    Physical.projector (fun z => c * v z) = Physical.projector v := by
  ext z w
  simp only [Physical.projector, Matrix.of_apply, star_mul]
  calc
    c * v z * (star (v w) * star c) = (star c * c) * (v z * star (v w)) := by ring
    _ = v z * star (v w) := by rw [hc, one_mul]

theorem bloch_global_phase {n : ℕ} (c : ℂ) (hc : star c * c = 1)
    (v : Vec n) (j : Fin n) :
    Regularity.bloch (fun z => c * v z) j = Regularity.bloch v j := by
  simp only [Regularity.bloch, localX, localY, localZ, pauliExpectation_scale, hc, one_mul]

/-- 定义中的全部测量列Bloch向量不变，故任意方向和重标号的几何正则性不变。 -/
theorem geometric_regular_global_phase {n : ℕ} (c : ℂ) (hc : star c * c = 1)
    (u : Bits n → ℂ) (r : ℝ) :
    Regularity.GeometricRegular (fun z => c * u z) r ↔
      Regularity.GeometricRegular u r := by
  simp only [Regularity.GeometricRegular, measurement_global_scale, bloch_global_phase c hc]

/-- 逐振幅规范化：减去零串的生成元值只贡献公共相位。 -/
theorem realGeneratorLine_normalize {n : ℕ} (g : Bits n → ℝ) (c : ℝ)
    (d : Bits n → Bit) (h : ∀ z, g z = g 0 + c * (d z).val) (t : ℝ) :
    realGeneratorLine g t =
      fun z => anglePhase (g 0 * t) * originalLine d (c * t) z := by
  funext z
  have hp := two_rate_phase (g 0) (g 0 + c) t (d z)
  rw [show g 0 + c - g 0 = c by ring] at hp
  unfold realGeneratorLine originalLine
  rw [h z]
  change originalDiagonal z * Complex.exp _ = _
  rw [hp]
  ring

/-- 规范化对完整有序测量成立，保留每一个输出列。 -/
theorem realGenerator_measurement_normalize {n : ℕ} (g : Bits n → ℝ) (c : ℝ)
    (d : Bits n → Bit) (h : ∀ z, g z = g 0 + c * (d z).val)
    (t : ℝ) (label : Bits n) :
    Physical.measurement (realGeneratorLine g t) label =
      fun z => anglePhase (g 0 * t) * Physical.measurement (originalLine d (c * t)) label z := by
  rw [realGeneratorLine_normalize g c d h, measurement_global_scale]

theorem realGenerator_projectors_normalize {n : ℕ} (g : Bits n → ℝ) (c : ℝ)
    (d : Bits n → Bit) (h : ∀ z, g z = g 0 + c * (d z).val)
    (t : ℝ) (label : Bits n) :
    Physical.projector (Physical.measurement (realGeneratorLine g t) label) =
      Physical.projector (Physical.measurement (originalLine d (c * t)) label) := by
  rw [realGenerator_measurement_normalize g c d h]
  exact projector_global_phase _ (anglePhase_star_mul _) _

theorem realGenerator_geometric_normalize {n : ℕ} (g : Bits n → ℝ) (c : ℝ)
    (d : Bits n → Bit) (h : ∀ z, g z = g 0 + c * (d z).val) (t r : ℝ) :
    Regularity.GeometricRegular (realGeneratorLine g t) r ↔
      Regularity.GeometricRegular (originalLine d (c * t)) r := by
  rw [realGeneratorLine_normalize g c d h]
  exact geometric_regular_global_phase _ (anglePhase_star_mul _) _ _

/-- 实生成元的admissibility直接使用完整测量在零点邻域的几何条件。 -/
def RealGeneratorAdmissible {n : ℕ} (g : Bits n → ℝ) : Prop :=
  ∀ᶠ t in nhds (0 : ℝ), ∃ r : ℝ, Regularity.GeometricRegular (realGeneratorLine g t) r

/-- 非零实缩放，包括反向参数，双向保持零点邻域中的命题。 -/
theorem eventually_mul_zero_iff (c : ℝ) (hc : c ≠ 0) (P : ℝ → Prop) :
    (∀ᶠ t in nhds (0 : ℝ), P (c * t)) ↔ ∀ᶠ u in nhds (0 : ℝ), P u := by
  have hm : Filter.map (fun t : ℝ => c * t) (nhds 0) = nhds 0 := by
    simpa only [mul_zero] using map_mul_left_nhds₀ hc (0 : ℝ)
  calc
    (∀ᶠ t in nhds (0 : ℝ), P (c * t)) ↔
        ∀ᶠ u in Filter.map (fun t : ℝ => c * t) (nhds 0), P u := Iff.rfl
    _ ↔ ∀ᶠ u in nhds (0 : ℝ), P u := by rw [hm]

/-- 规范化同时给出admissibility的充分性和必要性。 -/
theorem realGenerator_admissible_iff {n : ℕ} (g : Bits n → ℝ) (c : ℝ)
    (hc : c ≠ 0) (d : Bits n → Bit)
    (h : ∀ z, g z = g 0 + c * (d z).val) :
    RealGeneratorAdmissible g ↔
      ∀ᶠ t in nhds (0 : ℝ), ∃ r : ℝ, Regularity.GeometricRegular (originalLine d t) r := by
  unfold RealGeneratorAdmissible
  simp_rw [realGenerator_geometric_normalize g c d h]
  exact eventually_mul_zero_iff c hc
    (fun t => ∃ r : ℝ, Regularity.GeometricRegular (originalLine d t) r)

/-- 非零缩放覆盖全部实参数，故完整测量的可达几何半径逐值相同。 -/
theorem realGenerator_attainable_iff {n : ℕ} (g : Bits n → ℝ) (c : ℝ)
    (hc : c ≠ 0) (d : Bits n → Bit)
    (h : ∀ z, g z = g 0 + c * (d z).val) (r : ℝ) :
    (∃ t : ℝ, Regularity.GeometricRegular (realGeneratorLine g t) r) ↔
      ∃ u : ℝ, Regularity.GeometricRegular (originalLine d u) r := by
  simp_rw [realGenerator_geometric_normalize g c d h]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨c * t, ht⟩
  · rintro ⟨u, hu⟩
    refine ⟨u / c, ?_⟩
    simpa only [mul_div_cancel₀ _ hc] using hu

/-- 任意至多两值实生成元的完整实际几何优化集合。 -/
def realGeneratorRadiusValues (n : ℕ) : Set ℝ :=
  {r | ∃ g : Bits n → ℝ, AtMostTwoRealValues g ∧ RealGeneratorAdmissible g ∧
    ∃ t : ℝ, Regularity.GeometricRegular (realGeneratorLine g t) r}

/-- Boolean函数按零、一实值嵌入，属于至多两值生成元。 -/
theorem boolean_as_real_two_valued {n : ℕ} (d : Bits n → Bit) :
    AtMostTwoRealValues (fun z => ((d z).val : ℝ)) := by
  refine ⟨0, 1, ?_⟩
  intro z
  rcases bit_cases (d z) with hz | hz <;>
    simp [hz, ZMod.val_one_eq_one_mod]

/-- 规范化和Boolean实值嵌入双向证明优化集合相等，包括常值生成元。 -/
theorem realGenerator_radius_values_eq (n : ℕ) :
    realGeneratorRadiusValues n = geometricRadiusValues n := by
  ext r
  constructor
  · rintro ⟨g, hg, ha, ht⟩
    obtain ⟨c, d, hc, hd, he⟩ := atMostTwoRealValues_normalize g hg
    exact ⟨d, hd, (realGenerator_admissible_iff g c hc d he).mp ha,
      (realGenerator_attainable_iff g c hc d he r).mp ht⟩
  · rintro ⟨d, hd, ha, ht⟩
    let g : Bits n → ℝ := fun z => (d z).val
    have he : ∀ z, g z = g 0 + 1 * (d z).val := by
      intro z
      simp [g, hd]
    exact ⟨g, boolean_as_real_two_valued d,
      (realGenerator_admissible_iff g 1 one_ne_zero d he).mpr ha,
      (realGenerator_attainable_iff g 1 one_ne_zero d he r).mpr ht⟩

/-- 主定理的任意至多两值实生成元版本：实际完整测量半径的最大值达到。 -/
theorem actual_two_valued_real_model_exact_maximum {n : ℕ} (hn : 2 ≤ n) :
    IsGreatest (realGeneratorRadiusValues n) (modelMaximum n) := by
  rw [realGenerator_radius_values_eq]
  exact actual_boolean_model_exact_maximum hn

end UnifiedEJM.BooleanLines
