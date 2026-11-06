import UnifiedEJM.PhysicsIndexed
import UnifiedEJM.Multipartite

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem n6plus_pair12_indexed :
    indexedPurity (n := 6) 48 (fun i => new6A i + gi * new6B i) = 5120 := by
  decide +kernel

theorem n6plus_pair12 :
    gpurity ({0,1} : Finset (Fin 6)) (gnumerator (gphase UnifiedEJM.q gi)) = 5120 := by
  have hcut : cutSet 6 48 = ({0,1} : Finset (Fin 6)) := by decide +kernel
  rw [← hcut, gpurity6_index]
  exact n6plus_pair12_indexed

theorem endpoint_seed {n : ℕ} :
    UnifiedEJM.seed n (Real.pi/2) = Physical.seed (UnifiedEJM.rawPhase (gi : ℂ)) := by
  have ht : anglePhase (Real.pi/2) = I := by simp [anglePhase, Complex.exp_ofReal_mul_I]
  simp only [UnifiedEJM.seed, ht, gi_complex, Physical.seed]

theorem cutPurity_eq_swapPurity {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    Multipartite.cutPurity S ψ = swapPurity S ψ := by
  exact Multipartite.cutPurity_eq_swap_sum S ψ

theorem new5_endpoint_pair_purity :
    Multipartite.cutPurity ({0,1} : Finset (Fin 5)) (UnifiedEJM.seed 5 (Real.pi/2)) =
      (11/32 : ℂ) := by
  rw [endpoint_seed, cutPurity_eq_swapPurity, physical_purity_certificate,
    n5plus_pair12, scale_norm]
  norm_num [GaussianInt.toComplex_def]

theorem new6_endpoint_pair_purity :
    Multipartite.cutPurity ({0,1} : Finset (Fin 6)) (UnifiedEJM.seed 6 (Real.pi/2)) =
      (5/16 : ℂ) := by
  rw [endpoint_seed, cutPurity_eq_swapPurity, physical_purity_certificate,
    n6plus_pair12, scale_norm]
  norm_num [GaussianInt.toComplex_def]

end UnifiedEJM.PhysicsFinite

