import UnifiedEJM.PurityInvariant

namespace UnifiedEJM.PurityInvariant
open scoped Matrix BigOperators

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- 行与列分别重新编号，不改变真实二分纯度。 -/
theorem purity_submatrix (A : Matrix m n ℂ) (e : m ≃ m) (f : n ≃ n) :
    purity (A.submatrix e f) = purity A := by
  unfold purity
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  exact Equiv.sum_comp e (fun i => ((A * Aᴴ) * (A * Aᴴ)) i i)

/-- 行与列各自乘单位复相位，是局域对角酉作用。 -/
theorem purity_phase (A : Matrix m n ℂ) (p : m → ℂ) (q : n → ℂ)
    (hp : ∀ i, star (p i) * p i = 1) (hq : ∀ j, star (q j) * q j = 1) :
    purity (Matrix.of (fun i j => p i * q j * A i j)) = purity A := by
  let U : Matrix m m ℂ := Matrix.diagonal p
  let V : Matrix n n ℂ := Matrix.diagonal (fun j => star (q j))
  have hU : Uᴴ * U = 1 := by
    simp only [U, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have h : (fun i => star p i * p i) = (fun _ => (1 : ℂ)) := by funext i; exact hp i
    rw [h]
    rfl
  have hV : Vᴴ * V = 1 := by
    simp only [V, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have h : (fun j => star (fun j => star (q j)) j * star (q j)) =
        (fun _ => (1 : ℂ)) := by
      funext j
      simpa only [Pi.star_apply, star_star, mul_comm] using hq j
    rw [h]
    rfl
  have hM : U * A * Vᴴ = Matrix.of (fun i j => p i * q j * A i j) := by
    ext i j
    simp only [U, V, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Pi.star_apply, star_star, Matrix.of_apply]
    ring
  rw [← hM]
  exact purity_local_unitary A U V hU hV

/-- 局部Pauli作用中的行列平移与符号因子共同保持二体纯度。 -/
theorem purity_phase_submatrix (A : Matrix m n ℂ) (e : m ≃ m) (f : n ≃ n)
    (p : m → ℂ) (q : n → ℂ)
    (hp : ∀ i, star (p i) * p i = 1) (hq : ∀ j, star (q j) * q j = 1) :
    purity (Matrix.of (fun i j => p i * q j * A (e i) (f j))) = purity A := by
  calc
    _ = purity (A.submatrix e f) := purity_phase (A.submatrix e f) p q hp hq
    _ = _ := purity_submatrix A e f

end UnifiedEJM.PurityInvariant
