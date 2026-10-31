import UnifiedEJM.PermutationCore
import UnifiedEJM.FourQubitMarginal

noncomputable section
open scoped BigOperators Matrix
open OddEJM
namespace UnifiedEJM.BipartiteInvariant
open FiniteInvariants

private def tripleSwap01 : Equiv.Perm (Fin 8) where
  toFun := ![0,1,4,5,2,3,6,7]
  invFun := ![0,1,4,5,2,3,6,7]
  left_inv := by decide
  right_inv := by decide

private def tripleSwap12 : Equiv.Perm (Fin 8) where
  toFun := ![0,2,1,3,4,6,5,7]
  invFun := ![0,2,1,3,4,6,5,7]
  left_inv := by decide
  right_inv := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reshape1_swap01 (v : State) :
    reshape1 0 (permute (Equiv.swap 0 1) v)=reshape1 1 v ∧
    reshape1 1 (permute (Equiv.swap 0 1) v)=reshape1 0 v ∧
    reshape1 2 (permute (Equiv.swap 0 1) v)=
      (reshape1 2 v).submatrix (Equiv.refl _) tripleSwap01 ∧
    reshape1 3 (permute (Equiv.swap 0 1) v)=
      (reshape1 3 v).submatrix (Equiv.refl _) tripleSwap01 := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [reshape1,permute,decode4,encode4,tripleSwap01,
      Matrix.submatrix,Equiv.swap_apply_def] <;> congr 1 <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reshape1_swap12 (v : State) :
    reshape1 0 (permute (Equiv.swap 1 2) v)=
      (reshape1 0 v).submatrix (Equiv.refl _) tripleSwap01 ∧
    reshape1 1 (permute (Equiv.swap 1 2) v)=reshape1 2 v ∧
    reshape1 2 (permute (Equiv.swap 1 2) v)=reshape1 1 v ∧
    reshape1 3 (permute (Equiv.swap 1 2) v)=
      (reshape1 3 v).submatrix (Equiv.refl _) tripleSwap12 := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [reshape1,permute,decode4,encode4,tripleSwap01,tripleSwap12,
      Matrix.submatrix,Equiv.swap_apply_def] <;> congr 1 <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem reshape1_swap23 (v : State) :
    reshape1 0 (permute (Equiv.swap 2 3) v)=
      (reshape1 0 v).submatrix (Equiv.refl _) tripleSwap12 ∧
    reshape1 1 (permute (Equiv.swap 2 3) v)=
      (reshape1 1 v).submatrix (Equiv.refl _) tripleSwap12 ∧
    reshape1 2 (permute (Equiv.swap 2 3) v)=reshape1 3 v ∧
    reshape1 3 (permute (Equiv.swap 2 3) v)=reshape1 2 v := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [reshape1,permute,decode4,encode4,tripleSwap12,
      Matrix.submatrix,Equiv.swap_apply_def] <;> congr 1 <;> decide

private theorem singlePuritySum_swap01 (v : State) :
    singlePuritySum (permute (Equiv.swap 0 1) v)=singlePuritySum v := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := reshape1_swap01 v
  simp only [singlePuritySum,Fin.sum_univ_four,h₁,h₂,h₃,h₄,
    PurityInvariant.purity_submatrix]
  ring

private theorem singlePuritySum_swap12 (v : State) :
    singlePuritySum (permute (Equiv.swap 1 2) v)=singlePuritySum v := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := reshape1_swap12 v
  simp only [singlePuritySum,Fin.sum_univ_four,h₁,h₂,h₃,h₄,
    PurityInvariant.purity_submatrix]
  ring

private theorem singlePuritySum_swap23 (v : State) :
    singlePuritySum (permute (Equiv.swap 2 3) v)=singlePuritySum v := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := reshape1_swap23 v
  simp only [singlePuritySum,Fin.sum_univ_four,h₁,h₂,h₃,h₄,
    PurityInvariant.purity_submatrix]
  ring

private def singleInvariantPermutations : Submonoid (Equiv.Perm (Fin 4)) where
  carrier := {p | ∀ v,singlePuritySum (permute p v)=singlePuritySum v}
  one_mem' := by intro v; rw [permute_one]
  mul_mem' := by intro p q hp hq v; rw [permute_mul,hp,hq]

theorem singlePuritySum_permute (p : Equiv.Perm (Fin 4)) (v : State) :
    singlePuritySum (permute p v)=singlePuritySum v := by
  have hgen : (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) ⊆
      (singleInvariantPermutations : Set (Equiv.Perm (Fin 4))) := by
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact singlePuritySum_swap01
    · exact singlePuritySum_swap12
    · exact singlePuritySum_swap23
  have hc := Submonoid.closure_le.mpr hgen
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hc
  exact hc (by trivial : p ∈ (⊤ : Submonoid (Equiv.Perm (Fin 4)))) v

theorem singlePuritySum_phase (c : ℂ) (hc : star c*c=1) (v : State) :
    singlePuritySum (c • v)=singlePuritySum v := by
  unfold singlePuritySum
  apply Finset.sum_congr rfl
  intro j hj
  have h : reshape1 j (c • v) = c • reshape1 j v := by
    ext i k
    fin_cases j <;> fin_cases i <;> fin_cases k <;> simp [reshape1]
  rw [h]
  have hM : Matrix.of (fun i k => c * (1 : ℂ) * reshape1 j v i k) = c • reshape1 j v := by
    ext i k
    simp [smul_eq_mul]
  rw [← hM]
  exact PurityInvariant.purity_phase (reshape1 j v) (fun _ => c) (fun _ => 1)
    (fun _ => hc) (fun _ => by simp)

end UnifiedEJM.BipartiteInvariant
