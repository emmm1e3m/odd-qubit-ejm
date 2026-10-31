import UnifiedEJM.FourQubit
import UnifiedEJM.PurityInvariant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.GroupTheory.Perm.Sign

noncomputable section
open scoped BigOperators Matrix Kronecker
open OddEJM

namespace UnifiedEJM.BipartiteInvariant

open FiniteInvariants

/-- 四维指标按最高位优先拆成两个物理比特。 -/
def pairBits : Fin 4 ≃ Bit × Bit where
  toFun k := ![(0,0),(0,1),(1,0),(1,1)] k
  invFun p := ⟨2*p.1.val+p.2.val, by
    have h₁ := p.1.val_lt
    have h₂ := p.2.val_lt
    omega⟩
  left_inv := by decide
  right_inv := by decide

/-- 两个单比特算符的真实张量积，以四维计算基索引。 -/
def tensor2 (U V : Matrix Bit Bit ℂ) : Mat :=
  (U ⊗ₖ V).submatrix pairBits pairBits

theorem tensor2_unitary (U V : Matrix Bit Bit ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (tensor2 U V)ᴴ * tensor2 U V = 1 := by
  unfold tensor2
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hU, hV, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- 右侧物理张量因子作用为转置，结论仍是实际偏迹纯度不变。 -/
theorem purity_left_right_transpose (A L R : Mat)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) :
    FiniteInvariants.purity (L * A * Rᵀ) = FiniteInvariants.purity A := by
  change PurityInvariant.purity (L * A * Rᵀ) = PurityInvariant.purity A
  have hRT : Rᵀ * (Rᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose] using congrArg Matrix.transpose hR
  simpa only [Matrix.conjTranspose_conjTranspose] using
    PurityInvariant.purity_local_unitary A L (Rᵀ)ᴴ hL (by simpa using hRT)


/-- 四个单比特矩阵在实际十六个计算基振幅上的张量积作用。 -/
def localAction (U : Fin 4 → Matrix Bit Bit ℂ) (v : State) : State :=
  fun k => ∑ l : Fin 16, (∏ j : Fin 4, U j (decode4 k j) (decode4 l j)) * v l

/-- 最高位优先的解码表，用内核有限判定统一ZMod数字规范形。 -/
theorem decode4_table : decode4 = ![![0,0,0,0],![0,0,0,1],![0,0,1,0],![0,0,1,1],![0,1,0,0],![0,1,0,1],![0,1,1,0],![0,1,1,1],![1,0,0,0],![1,0,0,1],![1,0,1,0],![1,0,1,1],![1,1,0,0],![1,1,0,1],![1,1,1,0],![1,1,1,1]] := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reshape12_localAction (U : Fin 4 → Matrix Bit Bit ℂ) (v : State) :
    reshape12 (localAction U v) =
      tensor2 (U 0) (U 1) * reshape12 v * (tensor2 (U 2) (U 3))ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [reshape12, localAction, tensor2, pairBits, decode4_table,
      Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply,
      Matrix.kronecker_apply, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reshape13_localAction (U : Fin 4 → Matrix Bit Bit ℂ) (v : State) :
    reshape13 (localAction U v) =
      tensor2 (U 0) (U 2) * reshape13 v * (tensor2 (U 1) (U 3))ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [reshape13, localAction, tensor2, pairBits, decode4_table,
      Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply,
      Matrix.kronecker_apply, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reshape14_localAction (U : Fin 4 → Matrix Bit Bit ℂ) (v : State) :
    reshape14 (localAction U v) =
      tensor2 (U 0) (U 3) * reshape14 v * (tensor2 (U 1) (U 2))ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [reshape14, localAction, tensor2, pairBits, decode4_table,
      Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply,
      Matrix.kronecker_apply, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-- 三个真实二体偏迹的纯度和在任意四个单比特酉下不变。 -/
theorem sumPurity_localAction (U : Fin 4 → Matrix Bit Bit ℂ)
    (hU : ∀ j, (U j)ᴴ * U j = 1) (v : State) :
    sumPurity (localAction U v) = sumPurity v := by
  unfold sumPurity
  rw [reshape12_localAction, reshape13_localAction, reshape14_localAction]
  rw [purity_left_right_transpose _ _ _
      (tensor2_unitary _ _ (hU 0) (hU 1)) (tensor2_unitary _ _ (hU 2) (hU 3)),
    purity_left_right_transpose _ _ _
      (tensor2_unitary _ _ (hU 0) (hU 2)) (tensor2_unitary _ _ (hU 1) (hU 3)),
    purity_left_right_transpose _ _ _
      (tensor2_unitary _ _ (hU 0) (hU 3)) (tensor2_unitary _ _ (hU 1) (hU 2))]

end UnifiedEJM.BipartiteInvariant

