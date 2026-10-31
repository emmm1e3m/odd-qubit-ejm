import UnifiedEJM.SixAnalytic
import UnifiedEJM.SixPhysical
import UnifiedEJM.Physical
import UnifiedEJM.SixLocal

namespace UnifiedEJM.SixFamily
open OddEJM Complex
open UnifiedEJM.SixCertificate
open scoped BigOperators

def isII (p : Fin 18) : Prop :=
  p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=7 ∨ p=8 ∨ p=9 ∨ p=10
instance (p : Fin 18) : Decidable (isII p) := inferInstanceAs (Decidable (_∨_∨_∨_∨_∨_∨_∨_))

noncomputable def background (α β γ : ℝ) (z : Bits 6) : ℂ :=
  I ^ weight z * colourPhases α β γ (colour z)
noncomputable def diagonal (α β γ φ : ℝ) (z : Bits 6) : ℂ :=
  -I * (background α β γ z + (anglePhase φ - anglePhase γ) * deltaZero z)
noncomputable def seed (α β γ φ : ℝ) : Vec 6 := Physical.seed (diagonal α β γ φ)
noncomputable def defect (p : Fin 18) (α β γ φ : ℝ) : ℝ :=
  if isII p then SixLocal.defectII β γ φ else SixLocal.defectI α γ φ
noncomputable def total (p : Fin 18) (α β γ φ : ℝ) : ℝ :=
  backgroundTable p α β γ + 2 * defect p α β γ φ

theorem flip_colour : ∀ p : Fin 18, colour (A p) = if isII p then 1 else 2 := by decide

lemma crossI (α γ φ : ℝ) :
    (-I * star (anglePhase α) * (anglePhase φ - anglePhase γ)).re =
      SixLocal.defectI α γ φ := by
  simp [anglePhase, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, SixLocal.defectI, Real.sin_sub]
  ring

lemma crossII (β γ φ : ℝ) :
    (-star (anglePhase β) * (anglePhase φ - anglePhase γ)).re =
      SixLocal.defectII β γ φ := by
  simp [anglePhase, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, SixLocal.defectII, Real.cos_sub]
  ring

lemma cross_term (p : Fin 18) (α β γ φ : ℝ) :
    (star (background α β γ (A p)) * C p * (anglePhase φ-anglePhase γ)).re =
      defect p α β γ φ := by
  have he : star (background α β γ (A p)) * C p * (anglePhase φ-anglePhase γ) =
      gamma p * star (colourPhases α β γ (colour (A p))) *
        (anglePhase φ-anglePhase γ) := by
    unfold background
    rw [star_mul]
    calc
      _ = (C p * star (I ^ weight (A p))) *
        star (colourPhases α β γ (colour (A p))) * (anglePhase φ-anglePhase γ) := by ring
      _ = _ := by rw [gamma_checked]
  rw [he, flip_colour]
  by_cases hp : isII p
  · have hp' : p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=7 ∨ p=8 ∨ p=9 ∨ p=10 := hp
    simp only [hp, ite_true, gamma, hp', colourPhases, Matrix.cons_val_one,
      Matrix.cons_val_zero, neg_one_mul, defect]
    exact crossII β γ φ
  · have hp' : ¬(p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=7 ∨ p=8 ∨ p=9 ∨ p=10) := hp
    simp only [hp, ite_false, gamma, hp', colourPhases, Matrix.cons_val_succ,
      Matrix.cons_val_zero, defect]
    exact crossI α γ φ

/-- 四独立相位的实际输入振幅期望，包含物理零点修正。 -/
theorem raw_expectation (p : Fin 18) (α β γ φ : ℝ) :
    pauliExpectation (diagonal α β γ φ) (A p) (B p) (C p) =
      (total p α β γ φ : ℂ) := by
  unfold diagonal
  rw [pauliExpectation_scale]
  have hi : star (-I) * (-I) = 1 := by norm_num [Complex.star_def]
  rw [hi, one_mul, pauliExpectation_add_delta_hermitian _ _ _ _ _
    (nonzero_flip p) (hermitian_checked p), cross_term]
  change pauliExpectation (fun z => I ^ weight z * colourPhases α β γ (colour z)) _ _ _ + _ = _
  rw [actual_background, background_table]
  simp [total]

lemma normalized_expectation (p : Fin 18) (α β γ φ : ℝ) :
    pauliExpectation (fun z => normFactor 6 * diagonal α β γ φ z) (A p) (B p) (C p) =
      ((total p α β γ φ / 64 : ℝ) : ℂ) := by
  rw [pauliExpectation_scale, raw_expectation]
  have hn : star (normFactor 6) * normFactor 6 = (1/64 : ℂ) := by
    norm_num [normFactor, Complex.star_def]
  rw [hn]
  push_cast
  ring

theorem actual_X (j : Fin 6) (α β γ φ : ℝ) :
    localX (seed α β γ φ) j = ((total (rowX j) α β γ φ / 64 : ℝ) : ℂ) := by
  change pauliExpectation (circuit _) (unitBit 6 j.val) 0 1 = _
  rw [pull_X, normalized_expectation]

theorem actual_Y (j : Fin 6) (α β γ φ : ℝ) :
    (if j.val=5 then -localY (seed α β γ φ) j else localY (seed α β γ φ) j) =
      ((total (rowY j) α β γ φ / 64 : ℝ) : ℂ) := by
  change (if j.val=5 then -pauliExpectation (circuit _) (unitBit 6 j.val) (unitBit 6 j.val) I
    else pauliExpectation (circuit _) (unitBit 6 j.val) (unitBit 6 j.val) I) = _
  rw [pull_Y, normalized_expectation]

theorem actual_Z (j : Fin 6) (α β γ φ : ℝ) :
    localZ (seed α β γ φ) j = ((total (rowZ j) α β γ φ / 64 : ℝ) : ℂ) := by
  change pauliExpectation (circuit _) 0 (unitBit 6 j.val) 1 = _
  rw [pull_Z, normalized_expectation]

/-- 全部实际signed局部分量相同，以第一位X分量固定公共值。 -/
def ActualRegular (ψ : Vec 6) : Prop := ∀ j : Fin 6,
  localX ψ j = localX ψ 0 ∧
  (if j.val=5 then -localY ψ j else localY ψ j) = localX ψ 0 ∧
  localZ ψ j = localX ψ 0

theorem rows_cover : ∀ p : Fin 18,
    (∃ j : Fin 6, rowX j = p) ∨ (∃ j : Fin 6, rowY j = p) ∨ (∃ j : Fin 6, rowZ j = p) := by decide

lemma cast_div_injective {x y : ℝ} : ((x/64 : ℝ) : ℂ) = ((y/64 : ℝ) : ℂ) ↔ x=y := by
  rw [Complex.ofReal_inj]
  constructor
  · intro h; linarith
  · rintro rfl; rfl

theorem actual_regular_iff_table (α β γ φ : ℝ) :
    ActualRegular (seed α β γ φ) ↔
      ∀ p : Fin 18, total p α β γ φ = total 0 α β γ φ := by
  unfold ActualRegular
  simp only [actual_X, actual_Y, actual_Z, cast_div_injective]
  change (∀ j : Fin 6, total (rowX j) α β γ φ = total 0 α β γ φ ∧
    total (rowY j) α β γ φ = total 0 α β γ φ ∧
    total (rowZ j) α β γ φ = total 0 α β γ φ) ↔ _
  constructor
  · intro h p
    rcases rows_cover p with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact (h j).1
    · exact (h j).2.1
    · exact (h j).2.2
  · intro h j
    exact ⟨h _, h _, h _⟩

lemma total_at_zero (α β γ φ : ℝ) : total 0 α β γ φ = 2 * SixLocal.defectI α γ φ := by
  norm_num [total, defect, isII, backgroundTable]
lemma total_at_one (α β γ φ : ℝ) : total 1 α β γ φ = 2 * SixLocal.defectII β γ φ := by
  norm_num [total, defect, isII, backgroundTable]

theorem table_regular_iff_equations (α β γ φ : ℝ) :
    (∀ p : Fin 18, total p α β γ φ = total 0 α β γ φ) ↔
      SixLocal.BackgroundEquations α β γ ∧ SixLocal.defectI α γ φ = SixLocal.defectII β γ φ := by
  constructor
  · intro h
    have ho := h 1
    rw [total_at_one, total_at_zero] at ho
    have hd : SixLocal.defectI α γ φ = SixLocal.defectII β γ φ := by linarith
    refine ⟨(background_zero_iff α β γ).mp ?_, hd⟩
    intro p
    have hp := h p
    rw [total_at_zero] at hp
    unfold total defect at hp
    split_ifs at hp <;> rw [hd] at hp <;> linarith
  · rintro ⟨hbg, hd⟩ p
    have hb := (background_zero_iff α β γ).mpr hbg p
    rw [total_at_zero]
    unfold total defect
    rw [hb]
    split_ifs <;> simp [hd]

/-- 真实18个局部分量而非抽象方程的完整六比特局部交叉定理。 -/
theorem actual_local_crossing {α β γ φ : ℝ}
    (hα : |α| ≤ Real.pi/12) (hβ : |β| ≤ Real.pi/12)
    (hγ : |γ| ≤ Real.pi/12) (hφ : |φ-Real.pi/2| ≤ Real.pi/12) :
    ActualRegular (seed α β γ φ) ↔
      ((β=0 ∧ γ=α) ∨ (α=0 ∧ γ=β)) ∧ φ=Real.pi/2 := by
  rw [actual_regular_iff_table, table_regular_iff_equations]
  exact SixLocal.local_crossing_iff hα hβ hγ hφ

end UnifiedEJM.SixFamily
