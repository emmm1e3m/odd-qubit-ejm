import UnifiedEJM.Physical
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! 单比特真实偏迹的谱熵；定义使用矩阵的实际特征值。 -/

namespace UnifiedEJM.Entropy

open OddEJM
open scoped BigOperators

/-- 以2为底的von Neumann谱熵；零特征值使用连续延拓0 log 0=0。 -/
noncomputable def vonNeumann {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ :=
  (∑ i, Real.negMulLog (hA.eigenvalues i)) / Real.log 2

/-- 与论文一致的以2为底二元熵。 -/
noncomputable def binary (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

theorem binary_explicit (p : ℝ) :
    binary p = (-p * Real.log p - (1-p) * Real.log (1-p)) / Real.log 2 := by
  rw [binary, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog]
  ring

theorem reduced_isHermitian {n : ℕ} (ψ : Vec n) (j : Fin n) :
    (reduced ψ j).IsHermitian := by
  ext a b
  exact reduced_hermitian ψ j b a

/-- 两个实际特征值由迹和行列式确定，允许半径为0的重根。 -/
theorem eigenvalues_of_trace_det (A : Matrix Bit Bit ℂ) (hA : A.IsHermitian)
    (r : ℝ) (ht : Matrix.trace A = 1)
    (hd : Matrix.det A = (((1-r^2)/4 : ℝ) : ℂ)) :
    (hA.eigenvalues 0 = (1+r)/2 ∧ hA.eigenvalues 1 = (1-r)/2) ∨
    (hA.eigenvalues 0 = (1-r)/2 ∧ hA.eigenvalues 1 = (1+r)/2) := by
  have hsum := hA.trace_eq_sum_eigenvalues
  rw [ht, sum_bit] at hsum
  have hs : hA.eigenvalues 0 + hA.eigenvalues 1 = 1 := by
    have hh := congrArg Complex.re hsum
    simpa using hh.symm
  have hprod := hA.det_eq_prod_eigenvalues
  rw [hd] at hprod
  have hp : hA.eigenvalues 0 * hA.eigenvalues 1 = (1-r^2)/4 := by
    have huniv : (Finset.univ : Finset Bit) = {0,1} := by decide
    simp only [huniv, Finset.prod_insert, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.prod_singleton] at hprod
    have hh := congrArg Complex.re hprod
    simpa [pow_two, Complex.mul_re] using hh.symm
  have hf : (hA.eigenvalues 0 - (1+r)/2) *
      (hA.eigenvalues 0 - (1-r)/2) = 0 := by
    have hs' : hA.eigenvalues 1 = 1 - hA.eigenvalues 0 := by linarith
    rw [hs'] at hp
    nlinarith
  rcases mul_eq_zero.mp hf with hh | hh
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

/-- 此等式从谱定义推导，不把二元熵当作矩阵熵的定义。 -/
theorem vonNeumann_of_trace_det (A : Matrix Bit Bit ℂ) (hA : A.IsHermitian)
    (r : ℝ) (ht : Matrix.trace A = 1)
    (hd : Matrix.det A = (((1-r^2)/4 : ℝ) : ℂ)) :
    vonNeumann A hA = binary ((1+r)/2) := by
  have hsub : 1 - (1+r)/2 = (1-r)/2 := by ring
  unfold vonNeumann binary
  have huniv : (Finset.univ : Finset Bit) = {0,1} := by decide
  simp only [huniv, Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hsub]
  rcases eigenvalues_of_trace_det A hA r ht hd with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · rw [h0,h1]
  · rw [h0,h1,add_comm]

/-- 原振幅定义下的真实偏迹具有相应行列式。 -/
theorem reduced_det_radial {n : ℕ} (ψ : Vec n) (j : Fin n)
    (r : ℝ) (v : Fin 3 → ℝ)
    (hnorm : inner ψ ψ = 1)
    (hx : localX ψ j = (r : ℂ) * (v 0 : ℂ))
    (hy : localY ψ j = (r : ℂ) * (v 1 : ℂ))
    (hz : localZ ψ j = (r : ℂ) * (v 2 : ℂ))
    (hv : (v 0)^2+(v 1)^2+(v 2)^2=1) :
    Matrix.det (reduced ψ j) = (((1-r^2)/4 : ℝ) : ℂ) := by
  have hx' : localX ψ j = ((r * v 0 : ℝ) : ℂ) := by simpa using hx
  have hy' : localY ψ j = ((r * v 1 : ℝ) : ℂ) := by simpa using hy
  have hz' : localZ ψ j = ((r * v 2 : ℝ) : ℂ) := by simpa using hz
  have hh := reduced_det_of_components ψ j (r*v 0) (r*v 1) (r*v 2) 0
    hnorm hx' hy' hz'
  have hv' : (r*v 0)^2+(r*v 1)^2+(r*v 2)^2=r^2 := by
    calc
      _ = r^2*((v 0)^2+(v 1)^2+(v 2)^2) := by ring
      _ = r^2 := by rw [hv]; ring
  simpa [hv'] using hh

theorem reduced_entropy_radial {n : ℕ} (ψ : Vec n) (j : Fin n)
    (r : ℝ) (v : Fin 3 → ℝ)
    (hnorm : inner ψ ψ = 1)
    (hx : localX ψ j = (r : ℂ) * (v 0 : ℂ))
    (hy : localY ψ j = (r : ℂ) * (v 1 : ℂ))
    (hz : localZ ψ j = (r : ℂ) * (v 2 : ℂ))
    (hv : (v 0)^2+(v 1)^2+(v 2)^2=1) :
    vonNeumann (reduced ψ j) (reduced_isHermitian ψ j) = binary ((1+r)/2) := by
  apply vonNeumann_of_trace_det
  · rw [reduced_trace, hnorm]
  · exact reduced_det_radial ψ j r v hnorm hx hy hz hv

/-- 真实偏迹的完整二元素谱，二元析取只表示特征值排序的自由度。 -/
theorem reduced_eigenvalues_radial {n : ℕ} (ψ : Vec n) (j : Fin n)
    (r : ℝ) (v : Fin 3 → ℝ)
    (hnorm : inner ψ ψ = 1)
    (hx : localX ψ j = (r : ℂ) * (v 0 : ℂ))
    (hy : localY ψ j = (r : ℂ) * (v 1 : ℂ))
    (hz : localZ ψ j = (r : ℂ) * (v 2 : ℂ))
    (hv : (v 0)^2+(v 1)^2+(v 2)^2=1) :
    let hA := reduced_isHermitian ψ j
    (hA.eigenvalues 0 = (1+r)/2 ∧ hA.eigenvalues 1 = (1-r)/2) ∨
    (hA.eigenvalues 0 = (1-r)/2 ∧ hA.eigenvalues 1 = (1+r)/2) := by
  apply eigenvalues_of_trace_det
  · rw [reduced_trace, hnorm]
  · exact reduced_det_radial ψ j r v hnorm hx hy hz hv

/-- 所有实际测量列的熵由种子分量计算后统一传递。 -/
theorem measurement_entropy {n : ℕ} (hn : 0 < n) (u : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (m : ℝ) (label : Bits n) (j : Fin n)
    (hX : localX (Physical.seed u) j = (m : ℂ))
    (hY : localY (Physical.seed u) j = if j.val = n - 1 then -(m : ℂ) else (m : ℂ))
    (hZ : localZ (Physical.seed u) j = (m : ℂ)) :
    vonNeumann (reduced (Physical.measurement u label) j)
      (reduced_isHermitian _ j) = binary ((1+Real.sqrt 3*m)/2) := by
  obtain ⟨hx,hy,hz⟩ := Physical.measurement_radial_components_from_seed hn u m label j hX hY hZ
  have hv := local_vertices_unit j (localOutcome j label).1 (localOutcome j label).2
  simp only [Geometry.dot3, Fin.sum_univ_three, ← pow_two] at hv
  exact reduced_entropy_radial (Physical.measurement u label) j (Real.sqrt 3*m)
    (Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2)
    (Physical.measurement_normalized hn u hu label) hx hy hz hv

theorem entropy_strictAntiOn_radius :
    StrictAntiOn (fun r : ℝ => binary ((1+r)/2)) (Set.Icc 0 1) := by
  intro r hr s hs hlt
  apply (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  apply Real.binEntropy_strictAntiOn
  · constructor <;> norm_num at * <;> linarith [hr.1,hr.2]
  · constructor <;> norm_num at * <;> linarith [hs.1,hs.2]
  · linarith

theorem entropy_zero_radius : binary ((1+(0:ℝ))/2) = 1 := by
  simp only [add_zero, one_div, binary, Real.binEntropy_two_inv]
  exact div_self (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))

theorem entropy_unit_radius : binary ((1+(1:ℝ))/2) = 0 := by
  norm_num [binary]

theorem entropy_radius_bounds (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) :
    binary ((1+r)/2) ∈ Set.Icc (0:ℝ) 1 := by
  have hh := entropy_strictAntiOn_radius.antitoneOn
  constructor
  · have := hh hr (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1) hr.2
    dsimp only at this
    simpa only [entropy_unit_radius] using this
  · have := hh (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) hr hr.1
    dsimp only at this
    simpa only [entropy_zero_radius] using this

end UnifiedEJM.Entropy
