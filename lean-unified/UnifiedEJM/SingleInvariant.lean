import UnifiedEJM.PermutationInvariant
import UnifiedEJM.FourQubitMarginal
import UnifiedEJM.SinglePermutation

noncomputable section
open scoped BigOperators Matrix Kronecker
open OddEJM

namespace UnifiedEJM.BipartiteInvariant
open FiniteInvariants

private def bitIndex : Fin 2 ≃ Bit where
  toFun k := (k.val : Bit)
  invFun b := ⟨b.val,b.val_lt⟩
  left_inv := by decide
  right_inv := by decide

private def tripleIndex : Fin 8 ≃ Bit × Fin 4 where
  toFun k := (((k.val/4 : ℕ) : Bit),⟨k.val%4, Nat.mod_lt _ (by omega)⟩)
  invFun p := ⟨4*p.1.val+p.2.val,by
    have h₁ := p.1.val_lt
    have h₂ := p.2.isLt
    omega⟩
  left_inv := by decide
  right_inv := by decide

private def tensor1 (U : Matrix Bit Bit ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  U.submatrix bitIndex bitIndex

private def tensor3 (U V W : Matrix Bit Bit ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  (U ⊗ₖ tensor2 V W).submatrix tripleIndex tripleIndex

private theorem tensor1_unitary (U : Matrix Bit Bit ℂ) (hU : Uᴴ*U=1) :
    (tensor1 U)ᴴ*tensor1 U=1 := by
  unfold tensor1
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    hU,Matrix.submatrix_one_equiv]

private theorem tensor3_unitary (U V W : Matrix Bit Bit ℂ)
    (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) (hW : Wᴴ*W=1) :
    (tensor3 U V W)ᴴ*tensor3 U V W=1 := by
  unfold tensor3
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    hU,tensor2_unitary V W hV hW,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

private def otherPositions (j : Fin 4) : Fin 3 → Fin 4 :=
  ![![1,2,3],![0,2,3],![0,1,3],![0,1,2]] j

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem reshape1_localAction (U : Fin 4 → Matrix Bit Bit ℂ) (v : State) (j : Fin 4) :
    reshape1 j (localAction U v) = tensor1 (U j) * reshape1 j v *
      (tensor3 (U (otherPositions j 0)) (U (otherPositions j 1))
        (U (otherPositions j 2)))ᵀ := by
  ext i k
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    norm_num [reshape1,localAction,tensor1,tensor2,tensor3,bitIndex,pairBits,tripleIndex,
      otherPositions,decode4_table,Matrix.mul_apply,Matrix.submatrix,Matrix.transpose_apply,
      Matrix.kronecker_apply,Fin.sum_univ_succ,Fin.prod_univ_succ] <;> ring

private theorem purity_rect_left_right_transpose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (L : Matrix m m ℂ) (R : Matrix n n ℂ)
    (hL : Lᴴ*L=1) (hR : Rᴴ*R=1) :
    PurityInvariant.purity (L*A*Rᵀ)=PurityInvariant.purity A := by
  have hRT : Rᵀ * (Rᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_one,
      Matrix.transpose_conjTranspose,Matrix.conjTranspose_transpose] using
      congrArg Matrix.transpose hR
  simpa only [Matrix.conjTranspose_conjTranspose] using
    PurityInvariant.purity_local_unitary A L (Rᵀ)ᴴ hL (by simpa using hRT)

/-- 四个真实单体偏迹的纯度和在任意局域酉下不变。 -/
theorem singlePuritySum_localAction (U : Fin 4 → Matrix Bit Bit ℂ)
    (hU : ∀ j,(U j)ᴴ*U j=1) (v : State) :
    singlePuritySum (localAction U v)=singlePuritySum v := by
  unfold singlePuritySum
  apply Finset.sum_congr rfl
  intro j hj
  rw [reshape1_localAction]
  exact purity_rect_left_right_transpose _ _ _ (tensor1_unitary _ (hU j))
    (tensor3_unitary _ _ _ (hU _) (hU _) (hU _))

theorem singlePuritySum_of_equivalence (U : Fin 4 → Matrix Bit Bit ℂ)
    (hU : ∀ j,(U j)ᴴ*U j=1) (p : Equiv.Perm (Fin 4))
    (c : ℂ) (hc : star c*c=1) (v w : State)
    (heq : w=c • localAction U (permute p v)) :
    singlePuritySum w=singlePuritySum v := by
  rw [heq,singlePuritySum_phase c hc,singlePuritySum_localAction U hU,
    singlePuritySum_permute]

end UnifiedEJM.BipartiteInvariant
