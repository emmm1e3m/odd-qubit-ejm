import OddEJM.FamilyGeometry

namespace OddEJM

/-- 真实2×2 Bloch矩阵的三个系数由矩阵元唯一确定。 -/
theorem blochMatrix_components_injective {x y z x' y' z' : ℂ}
    (h : blochMatrix 1 x y z = blochMatrix 1 x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  have hd := congrArg (fun M : Matrix Bit Bit ℂ => M 0 0) h
  have hu := congrArg (fun M : Matrix Bit Bit ℂ => M 0 1) h
  have hl := congrArg (fun M : Matrix Bit Bit ℂ => M 1 0) h
  simp [blochMatrix, Matrix.of_apply] at hd hu hl
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℂ) * hu + (1 / 2 : ℂ) * hl
  · have hi : Complex.I * y = Complex.I * y' := by linear_combination (1 / 2 : ℂ) * hl - (1 / 2 : ℂ) * hu
    exact mul_left_cancel₀ Complex.I_ne_zero hi
  · exact hd

/-- 半径非零时，四个固定方向对应四个不同的实际2×2局部矩阵。 -/
theorem radial_vertex_matrix_injective {n : ℕ} (j : Fin n) (r : ℝ) (hr : r ≠ 0) :
    Function.Injective (fun a : Bit × Bit => blochMatrix 1
      ((r : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 0 : ℂ))
      ((r : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 1 : ℂ))
      ((r : ℂ) * (Geometry.vertex (localOrientation j) a.1 a.2 2 : ℂ))) := by
  intro a b hab
  obtain ⟨h0, h1, h2⟩ := blochMatrix_components_injective hab
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hv : Geometry.vertex (localOrientation j) a.1 a.2 =
      Geometry.vertex (localOrientation j) b.1 b.2 := by
    funext k
    fin_cases k
    · exact_mod_cast mul_left_cancel₀ hc h0
    · exact_mod_cast mul_left_cancel₀ hc h1
    · exact_mod_cast mul_left_cancel₀ hc h2
  exact local_vertices_injective j hv

end OddEJM
