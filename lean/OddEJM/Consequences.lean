import OddEJM.Main
import OddEJM.DensityMultiplicity
import OddEJM.Spectrum

namespace OddEJM

/-- 正半径下，等于指定局部矩阵当且仅当实际四面体标签相同。 -/
theorem measurement_reduced_eq_iff {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (hr : radius n t ≠ 0) (label : Bits n) (j : Fin n) (a : Bit × Bit) :
    reduced (measurement n t label) j = blochMatrix 1
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 0 : ℂ))
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 1 : ℂ))
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 2 : ℂ)) ↔
    localOutcome j label = a := by
  rw [measurement_reduced_bloch hn ho]
  constructor
  · intro h
    exact radial_vertex_matrix_injective j (radius n t) hr h
  · intro h
    rw [h]

/-- 正半径下，每个实际局部密度矩阵严格出现2^(n−2)次。 -/
theorem measurement_reduced_multiplicity {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (hr : radius n t ≠ 0) (j : Fin n) (a : Bit × Bit) :
    Nat.card {label : Bits n // reduced (measurement n t label) j = blochMatrix 1
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 0 : ℂ))
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 1 : ℂ))
      ((radius n t : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 2 : ℂ))} =
      2 ^ (n - 2) := by
  have he := Equiv.subtypeEquivRight (fun label : Bits n =>
    measurement_reduced_eq_iff hn ho t hr label j a)
  exact (Nat.card_congr he).trans (localOutcome_fiber_card (by omega) j a)

/-- 真实约化矩阵的两条特征值分支，由特征行列式精确检验。 -/
theorem measurement_det_eigenvalue {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (label : Bits n) (j : Fin n) (ε : ℝ) (hε : ε ^ 2 = 1) :
    Matrix.det (reduced (measurement n t label) j -
      ((((1 + ε * radius n t) / 2 : ℝ) : ℂ)) • (1 : Matrix Bit Bit ℂ)) = 0 := by
  obtain ⟨hx, hy, hz⟩ := measurement_radial_components hn ho t label j
  have hv := local_vertices_unit j (localOutcome j label).1 (localOutcome j label).2
  simp only [Geometry.dot3, Fin.sum_univ_three, ← pow_two] at hv
  exact reduced_radial_det_eigenvalue (measurement n t label) j (radius n t)
    (Geometry.vertex (localOrientation j) (localOutcome j label).1 (localOutcome j label).2)
    ε (measurement_normalized (by omega) t label) hx hy hz hv hε

theorem measurement_eigenvalues {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    Matrix.det (reduced (measurement n t label) j -
      ((((1 + radius n t) / 2 : ℝ) : ℂ)) • (1 : Matrix Bit Bit ℂ)) = 0 ∧
    Matrix.det (reduced (measurement n t label) j -
      ((((1 - radius n t) / 2 : ℝ) : ℂ)) • (1 : Matrix Bit Bit ℂ)) = 0 := by
  constructor
  · simpa using measurement_det_eigenvalue hn ho t label j 1 (by norm_num)
  · simpa [sub_eq_add_neg] using measurement_det_eigenvalue hn ho t label j (-1) (by norm_num)


end OddEJM
