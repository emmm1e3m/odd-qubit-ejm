import OddEJM.Density
import OddEJM.Bloch

namespace OddEJM
open Complex

/-- Bit=ZMod 2 的底层类型就是 Fin 2；两个显式矩阵逐元素相等。 -/
theorem blochMatrix_eq_geometry (x y z : ℝ) :
    blochMatrix 1 (x : ℂ) (y : ℂ) (z : ℂ) = Geometry.blochMatrix x y z := by
  ext a b
  have cases₂ (b : Bit) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
    simp [blochMatrix, Geometry.blochMatrix, Matrix.of_apply] <;> rfl

/-- 同一个真实偏迹矩阵的特征行列式，无另设代用量子态。 -/
theorem reduced_det_of_components {n : ℕ} (ψ : Vec n) (j : Fin n)
    (x y z ev : ℝ) (hnorm : inner ψ ψ = 1)
    (hx : localX ψ j = (x : ℂ)) (hy : localY ψ j = (y : ℂ))
    (hz : localZ ψ j = (z : ℂ)) :
    Matrix.det (reduced ψ j - (ev : ℂ) • (1 : Matrix Bit Bit ℂ)) =
      (((ev ^ 2 - ev + (1 - (x ^ 2 + y ^ 2 + z ^ 2)) / 4) : ℝ) : ℂ) := by
  rw [reduced_of_components ψ j _ _ _ hnorm hx hy hz, blochMatrix_eq_geometry]
  exact Geometry.bloch_det_shift x y z ev

/-- 真实归一化态的单位径向分量给出实际约化矩阵的两个特征根。 -/
theorem reduced_radial_det_eigenvalue {n : ℕ} (ψ : Vec n) (j : Fin n)
    (r : ℝ) (v : Fin 3 → ℝ) (ε : ℝ)
    (hnorm : inner ψ ψ = 1)
    (hx : localX ψ j = (r : ℂ) * (v 0 : ℂ))
    (hy : localY ψ j = (r : ℂ) * (v 1 : ℂ))
    (hz : localZ ψ j = (r : ℂ) * (v 2 : ℂ))
    (hv : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1)
    (hε : ε ^ 2 = 1) :
    Matrix.det (reduced ψ j - (((1 + ε * r) / 2 : ℝ) : ℂ) •
      (1 : Matrix Bit Bit ℂ)) = 0 := by
  have hx' : localX ψ j = ((r * v 0 : ℝ) : ℂ) := by simpa using hx
  have hy' : localY ψ j = ((r * v 1 : ℝ) : ℂ) := by simpa using hy
  have hz' : localZ ψ j = ((r * v 2 : ℝ) : ℂ) := by simpa using hz
  rw [reduced_of_components ψ j _ _ _ hnorm hx' hy' hz', blochMatrix_eq_geometry]
  apply Geometry.bloch_det_eigenvalue (r * v 0) (r * v 1) (r * v 2) r ε _ hε
  calc
    _ = r ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2) := by ring
    _ = r ^ 2 := by rw [hv]; ring

end OddEJM

#print axioms OddEJM.blochMatrix_eq_geometry
#print axioms OddEJM.reduced_det_of_components
#print axioms OddEJM.reduced_radial_det_eigenvalue

