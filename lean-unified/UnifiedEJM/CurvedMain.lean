import UnifiedEJM.CurvedFamily
import UnifiedEJM.CurvedPhysical
import UnifiedEJM.Continuity

/-!
# 指定四比特基点的闭式弯曲测量族

把闭式根的实分析、实际门电路有限和及通用偏迹桥连接成无待证物理前提的定理。
-/
namespace UnifiedEJM.Curved

open OddEJM
open scoped BigOperators

noncomputable def curvePhase (b : ℝ) : Bits 4 → ℂ :=
  CurvedPhysical.phase b (paperDelta b)

noncomputable def measurement (b : ℝ) (label : Bits 4) : Vec 4 :=
  Physical.measurement (curvePhase b) label

lemma curvePhase_unit (b : ℝ) (z : Bits 4) : star (curvePhase b z)*curvePhase b z=1 :=
  CurvedPhysical.phase_unit b (paperDelta b) z

/-- 正文两个固定掩码所给出的实际对角相位。 -/
lemma curvePhase_original (b : ℝ) (z : Bits 4) :
    curvePhase b z=originalDiagonal z * anglePhase
      (CurvedPhysical.bMask (CurvedPhysical.index z)*b+
        CurvedPhysical.dMask (CurvedPhysical.index z)*paperDelta b) :=
  CurvedPhysical.phase_original b (paperDelta b) z

lemma curvePhase_basepoint (z : Bits 4) : curvePhase 0 z=originalDiagonal z := by
  unfold curvePhase
  rw [paperDelta_zero]
  exact CurvedPhysical.phase_basepoint z

lemma closed_HT {b : ℝ} (hb : b ∈ Set.Icc 0 (Real.pi/4)) :
    CurvedPhysical.H b (paperDelta b)=CurvedPhysical.T b (paperDelta b) := by
  simpa only [CurvedPhysical.H,CurvedPhysical.T,paperGain] using paper_H_eq_T hb

lemma closed_seed_components {b : ℝ} (hb : b ∈ Set.Icc 0 (Real.pi/4)) (j : Fin 4) :
    localX (Physical.seed (curvePhase b)) j=(paperGain b/8 : ℝ) ∧
    localY (Physical.seed (curvePhase b)) j=
      (if j.val=3 then -((paperGain b/8 : ℝ):ℂ) else (paperGain b/8 : ℝ)) ∧
    localZ (Physical.seed (curvePhase b)) j=(paperGain b/8 : ℝ) := by
  exact CurvedPhysical.seed_components b (paperDelta b) (closed_HT hb) j

lemma measurement_orthonormal (b : ℝ) (label label' : Bits 4) :
    inner (measurement b label) (measurement b label')=if label=label' then 1 else 0 :=
  Physical.measurement_orthonormal (by norm_num) (curvePhase b) (curvePhase_unit b) label label'

lemma measurement_complete (b : ℝ) (z w : Bits 4) :
    (∑ label,measurement b label z*star (measurement b label w))=if z=w then 1 else 0 :=
  Physical.measurement_complete (by norm_num) (curvePhase b) (curvePhase_unit b) z w

lemma radius_component (b : ℝ) : Real.sqrt 3*(paperGain b/8)=radius b := by
  unfold radius
  ring

/-- 每个输出列和每个物理比特的真实有限和偏迹。 -/
lemma measurement_reduced {b : ℝ} (hb : b ∈ Set.Icc 0 (Real.pi/4))
    (label : Bits 4) (j : Fin 4) :
    let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
    reduced (measurement b label) j=(1/2:ℂ) • ((1:Matrix Bit Bit ℂ)+
      (radius b:ℂ) • ((v 0:ℂ) • sigmaX+(v 1:ℂ) • sigmaY+(v 2:ℂ) • sigmaZ)) := by
  obtain ⟨hx,hy,hz⟩ := closed_seed_components hb j
  have h := Physical.measurement_reduced_from_seed (by norm_num) (curvePhase b)
    (curvePhase_unit b) (paperGain b/8) label j hx hy hz
  simpa [radius_component,measurement] using h

lemma measurement_purity {b : ℝ} (hb : b ∈ Set.Icc 0 (Real.pi/4))
    (label : Bits 4) (j : Fin 4) :
    Matrix.trace (reduced (measurement b label) j*reduced (measurement b label) j)=
      (((1+radius b^2)/2:ℝ):ℂ) := by
  obtain ⟨hx,hy,hz⟩ := closed_seed_components hb j
  have h := Physical.measurement_purity (by norm_num) (curvePhase b)
    (curvePhase_unit b) (paperGain b/8) label j hx hy hz
  simpa [radius_component,measurement] using h

lemma measurement_basepoint (label : Bits 4) :
    measurement 0 label=circuit (fun z => normFactor 4*originalDiagonal z*character label z) := by
  unfold measurement Physical.measurement
  congr 1
  funext z
  rw [curvePhase_basepoint]

lemma measurement_eq_gate_column (b : ℝ) (label : Bits 4) :
    measurement b label=circuit (phaseGate (curvePhase b) (tensorHadamard (ket label))) :=
  Physical.measurement_eq_gate_column (curvePhase b) label

lemma curvePhase_continuous (z : Bits 4) :
    ContinuousOn (fun b => curvePhase b z) (Set.Icc 0 (Real.pi/4)) := by
  simp only [curvePhase_original,anglePhase]
  have hd := paperDelta_continuous
  fun_prop

lemma measurement_continuous (label : Bits 4) :
    ContinuousOn (fun b => measurement b label) (Set.Icc 0 (Real.pi/4)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Physical.measurement_continuous
    (fun b : Set.Icc (0:ℝ) (Real.pi/4) => curvePhase b.val)
    (fun z => continuousOn_iff_continuous_domRestrict.mp (curvePhase_continuous z)) label

lemma measurement_projector_continuous (label : Bits 4) :
    ContinuousOn (fun b => Physical.projector (measurement b label)) (Set.Icc 0 (Real.pi/4)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Physical.projector_continuous
    (fun b : Set.Icc (0:ℝ) (Real.pi/4) => measurement b.val label)
    (continuousOn_iff_continuous_domRestrict.mp (measurement_continuous label))

lemma measurement_reduced_continuous (label : Bits 4) (j : Fin 4) :
    ContinuousOn (fun b => reduced (measurement b label) j) (Set.Icc 0 (Real.pi/4)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Physical.reduced_continuous
    (fun b : Set.Icc (0:ℝ) (Real.pi/4) => measurement b.val label)
    (continuousOn_iff_continuous_domRestrict.mp (measurement_continuous label)) j

lemma measurement_multiplicity {b : ℝ} (hb : b ∈ Set.Icc 0 (Real.pi/4))
    (j : Fin 4) (a : Bit × Bit) :
    Nat.card {label : Bits 4 // reduced (measurement b label) j=blochMatrix 1
      ((radius b:ℂ)*(Geometry.vertex (localOrientation j) a.1 a.2 0:ℂ))
      ((radius b:ℂ)*(Geometry.vertex (localOrientation j) a.1 a.2 1:ℂ))
      ((radius b:ℂ)*(Geometry.vertex (localOrientation j) a.1 a.2 2:ℂ))}=4 := by
  obtain ⟨hx,hy,hz⟩ := closed_seed_components hb j
  have hm : paperGain b/8 ≠ 0 := by
    intro hzero
    have hr := radius_positive hb
    rw [← radius_component,hzero,mul_zero] at hr
    exact lt_irrefl 0 hr
  have h := Physical.measurement_reduced_multiplicity (by norm_num) (curvePhase b)
    (curvePhase_unit b) (paperGain b/8) hm j a hx hy hz
  simpa [radius_component,measurement] using h

/-- 四比特闭式曲线的完整测量定理；参数域外不承诺规则四面体。 -/
theorem curved_ejm_family :
    (∀ b label label',inner (measurement b label) (measurement b label')=
      if label=label' then 1 else 0) ∧
    (∀ b z w,(∑ label,measurement b label z*star (measurement b label w))=
      if z=w then 1 else 0) ∧
    (∀ b ∈ Set.Icc (0:ℝ) (Real.pi/4),∀ label j,
      let v := Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2
      reduced (measurement b label) j=(1/2:ℂ) • ((1:Matrix Bit Bit ℂ)+
        (radius b:ℂ) • ((v 0:ℂ) • sigmaX+(v 1:ℂ) • sigmaY+(v 2:ℂ) • sigmaZ))) ∧
    (∀ label,measurement 0 label=
      circuit (fun z => normFactor 4*originalDiagonal z*character label z)) ∧
    (∀ label,ContinuousOn (fun b => measurement b label) (Set.Icc 0 (Real.pi/4))) ∧
    (∀ label,ContinuousOn (fun b => Physical.projector (measurement b label))
      (Set.Icc 0 (Real.pi/4))) ∧
    ContinuousOn radius (Set.Icc 0 (Real.pi/4)) ∧
    StrictMonoOn radius (Set.Icc 0 (Real.pi/4)) ∧
    radius '' Set.Icc 0 (Real.pi/4)=
      Set.Icc (Real.sqrt 3/8) ((1+1/Real.sqrt 2)*(Real.sqrt 3/8)) := by
  exact ⟨measurement_orthonormal,measurement_complete,
    fun _ hb => measurement_reduced hb,measurement_basepoint,
    measurement_continuous,measurement_projector_continuous,
    radius_continuous,radius_strictMono,radius_image⟩

end UnifiedEJM.Curved

