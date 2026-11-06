import UnifiedEJM.PhysicsCoefficientTables
open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pairCanonical6 : Finset (Fin 31) :=
  Finset.univ.filter (fun k => (canonicalCut6 k).card = 2 ∨ (canonicalCut6 k).card = 4)
def pairRepresentative6 (k : Fin 31) : Finset (Fin 6) :=
  if (canonicalCut6 k).card = 2 then canonicalCut6 k else (canonicalCut6 k)ᶜ

theorem pair6_mem : ∀ k ∈ pairCanonical6, (pairRepresentative6 k).card = 2 := by
  decide +kernel

theorem pair6_inj : ∀ k ∈ pairCanonical6, ∀ l ∈ pairCanonical6,
    pairRepresentative6 k = pairRepresentative6 l → k = l := by decide +kernel

theorem pair6_surj : ∀ S : Finset (Fin 6), S.card = 2 →
    ∃ k ∈ pairCanonical6, pairRepresentative6 k = S := by decide +kernel

theorem twoBodyPurity_canonical6 (ψ : Vec 6) :
    Multipartite.twoBodyPurity ψ =
      ∑ k ∈ pairCanonical6, Multipartite.cutPurity (canonicalCut6 k) ψ := by
  unfold Multipartite.twoBodyPurity
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ => pairRepresentative6 k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact pair6_mem k hk
  · intro k hk l hl hkl
    exact pair6_inj k hk l hl hkl
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨k,hk,heq⟩ := pair6_surj S hS
    exact ⟨k,hk,heq⟩
  · intro k hk
    unfold pairRepresentative6
    split_ifs
    · rfl
    · exact (Multipartite.cutPurity_compl (canonicalCut6 k) ψ).symm

theorem laurentEval_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → Fin 5 → G) (u : ℂ) :
    laurentEval (∑ k ∈ s, c k) u = ∑ k ∈ s, laurentEval (c k) u := by
  simp [laurentEval, Finset.sum_apply, map_sum, Finset.sum_mul, Finset.sum_add_distrib]

def new6PairCoeff : Fin 5 → G := ![⟨-78,-64⟩,⟨1472,-640⟩,⟨67172,0⟩,⟨1472,640⟩,⟨-78,64⟩]
def pg6PairCoeff : Fin 5 → G := ![⟨-2014,0⟩,⟨-960,480⟩,⟨75908,0⟩,⟨-960,-480⟩,⟨-2014,0⟩]

theorem new6_pair_coefficients : (∑ k ∈ pairCanonical6, new6Coeff k) = new6PairCoeff := by
  funext j
  fin_cases j <;> decide +kernel

theorem pg6_pair_coefficients : (∑ k ∈ pairCanonical6, pg6Coeff k) = pg6PairCoeff := by
  funext j
  fin_cases j <;> decide +kernel

def pairCanonical5 : Finset (Fin 15) :=
  Finset.univ.filter (fun k => (canonicalCut5 k).card = 2 ∨ (canonicalCut5 k).card = 3)
def pairRepresentative5 (k : Fin 15) : Finset (Fin 5) :=
  if (canonicalCut5 k).card = 2 then canonicalCut5 k else (canonicalCut5 k)ᶜ

theorem pair5_mem : ∀ k ∈ pairCanonical5, (pairRepresentative5 k).card = 2 := by
  decide +kernel

theorem pair5_inj : ∀ k ∈ pairCanonical5, ∀ l ∈ pairCanonical5,
    pairRepresentative5 k = pairRepresentative5 l → k = l := by decide +kernel

theorem pair5_surj : ∀ S : Finset (Fin 5), S.card = 2 →
    ∃ k ∈ pairCanonical5, pairRepresentative5 k = S := by decide +kernel

theorem twoBodyPurity_canonical5 (ψ : Vec 5) :
    Multipartite.twoBodyPurity ψ =
      ∑ k ∈ pairCanonical5, Multipartite.cutPurity (canonicalCut5 k) ψ := by
  unfold Multipartite.twoBodyPurity
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ => pairRepresentative5 k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact pair5_mem k hk
  · intro k hk l hl hkl
    exact pair5_inj k hk l hl hkl
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨k,hk,heq⟩ := pair5_surj S hS
    exact ⟨k,hk,heq⟩
  · intro k hk
    unfold pairRepresentative5
    split_ifs
    · rfl
    · exact (Multipartite.cutPurity_compl (canonicalCut5 k) ψ).symm

def new5PairCoeff : Fin 5 → G := ![⟨-160,-32⟩,⟨448,-408⟩,⟨12016,0⟩,⟨448,408⟩,⟨-160,32⟩]

theorem new5_pair_coefficients : (∑ k ∈ pairCanonical5, new5Coeff k) = new5PairCoeff := by
  funext j
  fin_cases j <;> decide +kernel

end UnifiedEJM.PhysicsFinite
