import UnifiedEJM.Physical
import Mathlib.Tactic

/-! 实际测量的四面体几何与种子平方条件之间的双向桥。
几何定义使用真实测量列的Bloch内积，不预设四面体方向。
-/
noncomputable section
namespace UnifiedEJM.Regularity

open OddEJM OddEJM.CircuitPauli

abbrev V3 := Fin 3 → ℝ
abbrev LocalLabel := Bit × Bit

/-- 真实振幅态的三个局部Pauli迹期望之实部。 -/
def bloch {n : ℕ} (v : Vec n) (j : Fin n) : V3 :=
  ![(localX v j).re, (localY v j).re, (localZ v j).re]

def dot3 (v w : V3) : ℝ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def radius {n : ℕ} (v : Vec n) (j : Fin n) : ℝ :=
  Real.sqrt (dot3 (bloch v j) (bloch v j))

/-- Bloch向量直接对应真实偏迹，未另行定义代用密度矩阵。 -/
theorem bloch_eq_reduced_traces {n : ℕ} (v : Vec n) (j : Fin n) :
    bloch v j = ![(Matrix.trace (reduced v j * sigmaX)).re,
      (Matrix.trace (reduced v j * sigmaY)).re,
      (Matrix.trace (reduced v j * sigmaZ)).re] := by
  simp [bloch, reduced_trace_sigmaX, reduced_trace_sigmaY, reduced_trace_sigmaZ]

def orbitVector (v : V3) (p : LocalLabel) : V3 :=
  ![Geometry.signR p.1 * v 0, Geometry.signR (p.1 + p.2) * v 1,
    Geometry.signR p.2 * v 2]

theorem measurement_bloch {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (label : Bits n) (j : Fin n) :
    bloch (Physical.measurement u label) j =
      orbitVector (bloch (Physical.seed u) j) (localOutcome j label) := by
  funext k
  fin_cases k
  · change (pauliExpectation (Physical.measurement u label) (unitBit n j.val) 0 1).re =
      Geometry.signR (localParity label j.val) *
        (pauliExpectation (Physical.seed u) (unitBit n j.val) 0 1).re
    rw [Physical.measurement_localX_sign hn u label j.val j.isLt, bitSign_eq_real]
    simp [Complex.mul_re]
  · change (pauliExpectation (Physical.measurement u label) (unitBit n j.val)
        (unitBit n j.val) Complex.I).re =
      Geometry.signR (localParity label j.val + coord label (n-1)) *
        (pauliExpectation (Physical.seed u) (unitBit n j.val) (unitBit n j.val) Complex.I).re
    rw [Physical.measurement_localY_sign hn u label j.val j.isLt, bitSign_eq_real]
    simp [Complex.mul_re, add_comm]
  · change (pauliExpectation (Physical.measurement u label) 0 (unitBit n j.val) 1).re =
      Geometry.signR (coord label (n-1)) *
        (pauliExpectation (Physical.seed u) 0 (unitBit n j.val) 1).re
    rw [Physical.measurement_localZ_sign hn u label j.val j.isLt, bitSign_eq_real]
    simp [Complex.mul_re]

/-- 四个局部符号标签都由实际列实现。 -/
theorem localOutcome_surjective {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    Function.Surjective (localOutcome j) := by
  cases n with
  | zero => omega
  | succ m =>
    have h := Geometry.fullLabelHom_surjective m (by omega) j
    intro a
    obtain ⟨label, hh⟩ := h a
    exact ⟨label, (fullLabel_eq_localOutcome m j label).symm.trans hh⟩

private theorem bit_cases (q : Bit) : q = 0 ∨ q = 1 := by
  fin_cases q
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem orbitVector_norm (v : V3) (p : LocalLabel) :
    dot3 (orbitVector v p) (orbitVector v p) = dot3 v v := by
  rcases p with ⟨q,s⟩
  rcases bit_cases q with rfl | rfl <;> rcases bit_cases s with rfl | rfl <;>
    simp only [orbitVector, Geometry.signR_add] at * <;> norm_num [dot3, Geometry.signR]

/-- 任意相位和任意测量列的局部Bloch模长均等于种子；无需先假设规则性。 -/
theorem measurement_norm_sq {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (label : Bits n) (j : Fin n) :
    dot3 (bloch (Physical.measurement u label) j)
      (bloch (Physical.measurement u label) j) =
    dot3 (bloch (Physical.seed u) j) (bloch (Physical.seed u) j) := by
  rw [measurement_bloch hn]
  exact orbitVector_norm _ _

theorem measurement_radius {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (label : Bits n) (j : Fin n) :
    radius (Physical.measurement u label) j = radius (Physical.seed u) j := by
  unfold radius
  rw [measurement_norm_sq hn]

/-- 实际测量列按四个已满射的轨道标签组成同半径正四面体；方向自由。 -/
def Regular {n : ℕ} (u : Bits n → ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ (j : Fin n) (k l : Bits n),
    dot3 (bloch (Physical.measurement u k) j) (bloch (Physical.measurement u l) j) =
      if localOutcome j k = localOutcome j l then r^2 else -(r^2)/3

theorem orbit_gram_of_squares (v : V3) (r : ℝ)
    (hx : v 0 ^ 2 = r^2/3) (hy : v 1 ^ 2 = r^2/3) (hz : v 2 ^ 2 = r^2/3)
    (p q : LocalLabel) :
    dot3 (orbitVector v p) (orbitVector v q) = if p=q then r^2 else -(r^2)/3 := by
  rcases p with ⟨p₁,p₂⟩
  rcases q with ⟨q₁,q₂⟩
  rcases bit_cases p₁ with rfl | rfl <;> rcases bit_cases p₂ with rfl | rfl <;>
    rcases bit_cases q₁ with rfl | rfl <;> rcases bit_cases q₂ with rfl | rfl <;>
    simp only [orbitVector, Geometry.signR_add] at * <;> norm_num [dot3, Geometry.signR] <;> nlinarith

theorem squares_of_orbit_gram (v : V3) (r : ℝ)
    (h : ∀ p q : LocalLabel, dot3 (orbitVector v p) (orbitVector v q) =
      if p=q then r^2 else -(r^2)/3) :
    v 0 ^ 2 = r^2/3 ∧ v 1 ^ 2 = r^2/3 ∧ v 2 ^ 2 = r^2/3 := by
  have h0 := h (0,0) (0,0)
  have h1 := h (0,0) (1,0)
  have h2 := h (0,0) (0,1)
  simp only [orbitVector, Geometry.signR_add] at * <;> norm_num [dot3, Geometry.signR] at h0 h1 h2
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- 共同半径真实几何的充要条件；右侧是三条逐站点实际Pauli平方等式。 -/
theorem regular_iff_seed_squares {n : ℕ} (hn : 2 ≤ n) (u : Bits n → ℂ) (r : ℝ) :
    Regular u r ↔ 0 ≤ r ∧ ∀ j : Fin n,
      (localX (Physical.seed u) j).re^2 = r^2/3 ∧
      (localY (Physical.seed u) j).re^2 = r^2/3 ∧
      (localZ (Physical.seed u) j).re^2 = r^2/3 := by
  constructor
  · intro h
    refine ⟨h.1, fun j => ?_⟩
    apply squares_of_orbit_gram (bloch (Physical.seed u) j) r
    intro p q
    obtain ⟨k,hk⟩ := localOutcome_surjective hn j p
    obtain ⟨l,hl⟩ := localOutcome_surjective hn j q
    have hh := h.2 j k l
    rw [measurement_bloch (show 0 < n by omega) u k j,
      measurement_bloch (show 0 < n by omega) u l j, hk, hl] at hh
    exact hh
  · rintro ⟨hr,h⟩
    refine ⟨hr, fun j k l => ?_⟩
    rw [measurement_bloch (show 0 < n by omega), measurement_bloch (show 0 < n by omega)]
    exact orbit_gram_of_squares (bloch (Physical.seed u) j) r
      (h j).1 (h j).2.1 (h j).2.2 _ _

theorem seed_squares {n : ℕ} (hn : 2 ≤ n) {u : Bits n → ℂ} {r : ℝ}
    (h : Regular u r) (j : Fin n) :
    (localX (Physical.seed u) j).re^2 = r^2/3 ∧
    (localY (Physical.seed u) j).re^2 = r^2/3 ∧
    (localZ (Physical.seed u) j).re^2 = r^2/3 :=
  ((regular_iff_seed_squares hn u r).mp h).2 j

theorem r_eq_sqrt_three_abs_seed_X {n : ℕ} (hn : 2 ≤ n) {u : Bits n → ℂ} {r : ℝ}
    (h : Regular u r) (j : Fin n) :
    r = Real.sqrt 3 * |(localX (Physical.seed u) j).re| := by
  have hx := (seed_squares hn h j).1
  have hr := h.1
  have hs := Geometry.sqrt_three_sq
  have hp : 0 ≤ Real.sqrt 3 * |(localX (Physical.seed u) j).re| := by positivity
  have he : (Real.sqrt 3 * |(localX (Physical.seed u) j).re|)^2 = r^2 := by
    rw [mul_pow, hs, sq_abs]
    nlinarith
  nlinarith

theorem regular_column_radius {n : ℕ} {u : Bits n → ℂ} {r : ℝ}
    (h : Regular u r) (j : Fin n) (label : Bits n) :
    radius (Physical.measurement u label) j = r := by
  unfold radius
  have hh := h.2 j label label
  simp only [ite_true] at hh
  rw [hh, Real.sqrt_sq h.1]


/-- 不固定顶点方向或输出标号的几何定义；四个顶点标签均被实际列覆盖。
半径零时允许四点重合，其范数条件仍由Gram矩阵保留。 -/
def GeometricRegular {n : ℕ} (u : Bits n → ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ j : Fin n, ∃ (v : LocalLabel → V3) (a : Bits n → LocalLabel),
    Function.Surjective a ∧
    (∀ label, bloch (Physical.measurement u label) j = v (a label)) ∧
    ∀ p q, dot3 (v p) (v q) = if p=q then r^2 else -(r^2)/3

private theorem eq_zero_of_dot_self_zero (v : V3) (h : dot3 v v = 0) : v = 0 := by
  have hh : v 0^2 + v 1^2 + v 2^2 = 0 := by simpa [dot3, pow_two] using h
  have h0 : v 0 ^ 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  have h2 : v 2 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  funext i
  fin_cases i
  · exact sq_eq_zero_iff.mp h0
  · exact sq_eq_zero_iff.mp h1
  · exact sq_eq_zero_iff.mp h2

/-- 任意四面体方向和任意实际输出重标号，均诱导同一个轨道Gram条件。 -/
theorem geometric_iff_regular {n : ℕ} (hn : 2 ≤ n) (u : Bits n → ℂ) (r : ℝ) :
    GeometricRegular u r ↔ Regular u r := by
  classical
  constructor
  · rintro ⟨hr, hg⟩
    refine ⟨hr, fun j k l => ?_⟩
    obtain ⟨v,a,ha,hb,hgram⟩ := hg j
    by_cases hz : r = 0
    · have hv : ∀ p, v p = 0 := by
        intro p
        apply eq_zero_of_dot_self_zero
        simpa [hz] using hgram p p
      simp [hb, hv, hz, dot3]
    · have hvi : Function.Injective v := by
        intro p q he
        by_contra hpq
        have h0 := hgram q q
        have h1 := hgram p q
        rw [he] at h1
        simp only [ite_true] at h0
        simp only [ite_eq_right hpq] at h1
        have hp : 0 < r^2 := sq_pos_of_ne_zero hz
        nlinarith
      let rep : LocalLabel → Bits n := fun p =>
        Classical.choose (localOutcome_surjective hn j p)
      have hrep : ∀ p, localOutcome j (rep p) = p := fun p =>
        Classical.choose_spec (localOutcome_surjective hn j p)
      let f : LocalLabel → LocalLabel := fun p => a (rep p)
      have hf : ∀ p, v (f p) = orbitVector (bloch (Physical.seed u) j) p := by
        intro p
        calc
          v (f p) = bloch (Physical.measurement u (rep p)) j := (hb (rep p)).symm
          _ = orbitVector (bloch (Physical.seed u) j) (localOutcome j (rep p)) :=
            measurement_bloch (by omega) u (rep p) j
          _ = orbitVector (bloch (Physical.seed u) j) p := by rw [hrep]
      have hfs : Function.Surjective f := by
        intro p
        obtain ⟨label,hl⟩ := ha p
        refine ⟨localOutcome j label, hvi ?_⟩
        calc
          v (f (localOutcome j label)) =
              orbitVector (bloch (Physical.seed u) j) (localOutcome j label) := hf _
          _ = bloch (Physical.measurement u label) j :=
            (measurement_bloch (by omega) u label j).symm
          _ = v p := by rw [hb, hl]
      have hfi : Function.Injective f := Finite.injective_iff_surjective.mpr hfs
      have hk : a k = f (localOutcome j k) := hvi (by
        rw [hf, ← measurement_bloch (show 0 < n by omega) u k j, hb])
      have hl : a l = f (localOutcome j l) := hvi (by
        rw [hf, ← measurement_bloch (show 0 < n by omega) u l j, hb])
      rw [hb, hb, hgram, hk, hl]
      simp only [hfi.eq_iff]
  · intro h
    refine ⟨h.1, fun j => ?_⟩
    refine ⟨orbitVector (bloch (Physical.seed u) j), localOutcome j,
      localOutcome_surjective hn j, ?_, ?_⟩
    · intro label
      exact measurement_bloch (by omega) u label j
    · intro p q
      obtain ⟨k,hk⟩ := localOutcome_surjective hn j p
      obtain ⟨l,hl⟩ := localOutcome_surjective hn j q
      have hh := h.2 j k l
      rw [measurement_bloch (show 0 < n by omega) u k j,
        measurement_bloch (show 0 < n by omega) u l j, hk, hl] at hh
      exact hh

theorem geometric_iff_seed_squares {n : ℕ} (hn : 2 ≤ n) (u : Bits n → ℂ) (r : ℝ) :
    GeometricRegular u r ↔ 0 ≤ r ∧ ∀ j : Fin n,
      (localX (Physical.seed u) j).re^2 = r^2/3 ∧
      (localY (Physical.seed u) j).re^2 = r^2/3 ∧
      (localZ (Physical.seed u) j).re^2 = r^2/3 :=
  (geometric_iff_regular hn u r).trans (regular_iff_seed_squares hn u r)

theorem geometric_seed_squares {n : ℕ} (hn : 2 ≤ n) {u : Bits n → ℂ} {r : ℝ}
    (h : GeometricRegular u r) (j : Fin n) :
    (localX (Physical.seed u) j).re^2 = r^2/3 ∧
    (localY (Physical.seed u) j).re^2 = r^2/3 ∧
    (localZ (Physical.seed u) j).re^2 = r^2/3 :=
  ((geometric_iff_seed_squares hn u r).mp h).2 j

theorem geometric_column_radius {n : ℕ} (hn : 2 ≤ n) {u : Bits n → ℂ} {r : ℝ}
    (h : GeometricRegular u r) (j : Fin n) (label : Bits n) :
    radius (Physical.measurement u label) j = r :=
  regular_column_radius ((geometric_iff_regular hn u r).mp h) j label

theorem geometric_r_eq_sqrt_three_abs_seed_X {n : ℕ} (hn : 2 ≤ n)
    {u : Bits n → ℂ} {r : ℝ} (h : GeometricRegular u r) (j : Fin n) :
    r = Real.sqrt 3 * |(localX (Physical.seed u) j).re| :=
  r_eq_sqrt_three_abs_seed_X hn ((geometric_iff_regular hn u r).mp h) j

end UnifiedEJM.Regularity

