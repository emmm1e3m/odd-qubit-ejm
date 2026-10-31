import UnifiedEJM.FourQubit
import Mathlib.GroupTheory.Perm.Sign
import UnifiedEJM.MonomialInvariant

noncomputable section
open scoped BigOperators Matrix Kronecker
open OddEJM

namespace UnifiedEJM.BipartiteInvariant

open FiniteInvariants

/-- 直接重新排列四个物理比特，未将不变量性质放入定义。 -/
def permute (p : Equiv.Perm (Fin 4)) (v : State) : State :=
  fun k => v (encode4 (fun j => decode4 k (p j)))

theorem permute_one (v : State) : permute 1 v = v := by
  funext k
  simp [permute, encode_decode4]

theorem permute_mul (p q : Equiv.Perm (Fin 4)) (v : State) :
    permute (p*q) v = permute p (permute q v) := by
  funext k
  simp [permute, Equiv.Perm.mul_apply, decode_encode4]

private def pairSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2

private theorem purity_reindex (A : Mat) (e f : Equiv.Perm (Fin 4)) :
    FiniteInvariants.purity (A.submatrix e f) = FiniteInvariants.purity A :=
  PurityInvariant.purity_submatrix A e f

private theorem purity_transpose (A : Mat) :
    FiniteInvariants.purity Aᵀ = FiniteInvariants.purity A :=
  PurityInvariant.purity_transpose A

set_option maxRecDepth 10000 in
theorem reshapes_swap01 (v : State) :
    reshape12 (permute (Equiv.swap 0 1) v) =
      (reshape12 v).submatrix pairSwap (Equiv.refl _) ∧
    reshape13 (permute (Equiv.swap 0 1) v) = (reshape14 v)ᵀ ∧
    reshape14 (permute (Equiv.swap 0 1) v) = (reshape13 v)ᵀ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [reshape12, reshape13, reshape14, permute, decode4, encode4,
      pairSwap, Matrix.submatrix, Matrix.transpose_apply, Equiv.swap_apply_def] <;> congr 1 <;> decide

set_option maxRecDepth 10000 in
theorem reshapes_swap12 (v : State) :
    reshape12 (permute (Equiv.swap 1 2) v) = reshape13 v ∧
    reshape13 (permute (Equiv.swap 1 2) v) = reshape12 v ∧
    reshape14 (permute (Equiv.swap 1 2) v) =
      (reshape14 v).submatrix (Equiv.refl _) pairSwap := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [reshape12, reshape13, reshape14, permute, decode4, encode4,
      pairSwap, Matrix.submatrix, Matrix.transpose_apply, Equiv.swap_apply_def] <;> congr 1 <;> decide

set_option maxRecDepth 10000 in
theorem reshapes_swap23 (v : State) :
    reshape12 (permute (Equiv.swap 2 3) v) =
      (reshape12 v).submatrix (Equiv.refl _) pairSwap ∧
    reshape13 (permute (Equiv.swap 2 3) v) = reshape14 v ∧
    reshape14 (permute (Equiv.swap 2 3) v) = reshape13 v := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [reshape12, reshape13, reshape14, permute, decode4, encode4,
      pairSwap, Matrix.submatrix, Matrix.transpose_apply, Equiv.swap_apply_def] <;> congr 1 <;> decide

theorem sumPurity_swap01 (v : State) :
    sumPurity (permute (Equiv.swap 0 1) v) = sumPurity v := by
  obtain ⟨h₁,h₂,h₃⟩ := reshapes_swap01 v
  simp only [sumPurity, h₁,h₂,h₃,purity_reindex,purity_transpose]
  ring

theorem sumPurity_swap12 (v : State) :
    sumPurity (permute (Equiv.swap 1 2) v) = sumPurity v := by
  obtain ⟨h₁,h₂,h₃⟩ := reshapes_swap12 v
  simp only [sumPurity, h₁,h₂,h₃,purity_reindex]
  ring

theorem sumPurity_swap23 (v : State) :
    sumPurity (permute (Equiv.swap 2 3) v) = sumPurity v := by
  obtain ⟨h₁,h₂,h₃⟩ := reshapes_swap23 v
  simp only [sumPurity, h₁,h₂,h₃,purity_reindex]
  ring

private def invariantPermutations : Submonoid (Equiv.Perm (Fin 4)) where
  carrier := {p | ∀ v, sumPurity (permute p v) = sumPurity v}
  one_mem' := by intro v; rw [permute_one]
  mul_mem' := by
    intro p q hp hq v
    rw [permute_mul, hp, hq]

/-- 任意物理比特置换仅置换三种无序二二切割，因此保持其真实纯度和。 -/
theorem sumPurity_permute (p : Equiv.Perm (Fin 4)) (v : State) :
    sumPurity (permute p v) = sumPurity v := by
  have hgen : (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) ⊆
      (invariantPermutations : Set (Equiv.Perm (Fin 4))) := by
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact sumPurity_swap01
    · exact sumPurity_swap12
    · exact sumPurity_swap23
  have hc := Submonoid.closure_le.mpr hgen
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hc
  exact hc (by trivial : p ∈ (⊤ : Submonoid (Equiv.Perm (Fin 4)))) v

private theorem purity_phase_scalar (c : ℂ) (hc : star c * c = 1) (A : Mat) :
    FiniteInvariants.purity (c • A) = FiniteInvariants.purity A := by
  change PurityInvariant.purity (c • A) = PurityInvariant.purity A
  have hM : Matrix.of (fun i j => c * (1 : ℂ) * A i j) = c • A := by
    ext i j
    simp [smul_eq_mul]
  rw [← hM]
  exact PurityInvariant.purity_phase A (fun _ => c) (fun _ => 1) (fun _ => hc)
    (fun _ => by simp)

/-- 单列整体相位同样保持该不变量。 -/
theorem sumPurity_phase (c : ℂ) (hc : star c * c = 1) (v : State) :
    sumPurity (c • v) = sumPurity v := by
  have h₁ : reshape12 (c • v) = c • reshape12 v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [reshape12]
  have h₂ : reshape13 (c • v) = c • reshape13 v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [reshape13]
  have h₃ : reshape14 (c • v) = c • reshape14 v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [reshape14]
  simp only [sumPurity, h₁,h₂,h₃,purity_phase_scalar c hc]

end UnifiedEJM.BipartiteInvariant
