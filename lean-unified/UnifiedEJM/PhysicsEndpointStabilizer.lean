import UnifiedEJM.StabilizerMarginal
import UnifiedEJM.PhysicsEndpointPairs

noncomputable section
open scoped Matrix
open Complex OddEJM
open UnifiedEJM.Multipartite UnifiedEJM.PhysicsEndpoint
open UnifiedEJM.StabilizerMarginal UnifiedEJM.PhysicsFinite

namespace UnifiedEJM.PhysicsEndpointStabilizer

/-- 五比特零半径端点的每个测量列具有相同真实两体纯度。 -/
theorem new5_measurement_pair_purity (label : Bits 5) :
    cutPurity ({0,1} : Finset (Fin 5)) (UnifiedEJM.measurement 5 (Real.pi/2) label) =
      (11/32 : ℂ) := by
  change cutPurity _ (Physical.measurement (UnifiedEJM.rawPhase (anglePhase (Real.pi/2))) label) = _
  rw [cutPurity_measurement (by decide)]
  exact new5_endpoint_pair_purity

/-- 六比特零半径端点的每个测量列具有相同真实两体纯度。 -/
theorem new6_measurement_pair_purity (label : Bits 6) :
    cutPurity ({0,1} : Finset (Fin 6)) (UnifiedEJM.measurement 6 (Real.pi/2) label) =
      (5/16 : ℂ) := by
  change cutPurity _ (Physical.measurement (UnifiedEJM.rawPhase (anglePhase (Real.pi/2))) label) = _
  rw [cutPurity_measurement (by decide)]
  exact new6_endpoint_pair_purity

/-- 五比特正端点不在任何稳定子纯态的局域酉轨道中，允许相位和置换。 -/
theorem new5_endpoint_not_LU_stabilizer (φ : Vec 5) (hφ : IsStabilizer φ)
    (U : Fin 5 → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin 5)) (c : ℂ) (hc : star c*c=1) :
    UnifiedEJM.seed 5 (Real.pi/2) ≠ c • localAction U (permute p φ) := by
  exact not_stabilizer_LU_of_pairPurity {0,1} (by decide) _
    (Or.inl new5_endpoint_pair_purity) φ hφ U hU p c hc

/-- 六比特正端点不在任何稳定子纯态的局域酉轨道中，允许相位和置换。 -/
theorem new6_endpoint_not_LU_stabilizer (φ : Vec 6) (hφ : IsStabilizer φ)
    (U : Fin 6 → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin 6)) (c : ℂ) (hc : star c*c=1) :
    UnifiedEJM.seed 6 (Real.pi/2) ≠ c • localAction U (permute p φ) := by
  exact not_stabilizer_LU_of_pairPurity {0,1} (by decide) _
    (Or.inr new6_endpoint_pair_purity) φ hφ U hU p c hc

theorem new5_measurement_not_LU_stabilizer (label : Bits 5)
    (φ : Vec 5) (hφ : IsStabilizer φ)
    (U : Fin 5 → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin 5)) (c : ℂ) (hc : star c*c=1) :
    UnifiedEJM.measurement 5 (Real.pi/2) label ≠ c • localAction U (permute p φ) := by
  exact not_stabilizer_LU_of_pairPurity {0,1} (by decide) _
    (Or.inl (new5_measurement_pair_purity label)) φ hφ U hU p c hc

theorem new6_measurement_not_LU_stabilizer (label : Bits 6)
    (φ : Vec 6) (hφ : IsStabilizer φ)
    (U : Fin 6 → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin 6)) (c : ℂ) (hc : star c*c=1) :
    UnifiedEJM.measurement 6 (Real.pi/2) label ≠ c • localAction U (permute p φ) := by
  exact not_stabilizer_LU_of_pairPurity {0,1} (by decide) _
    (Or.inr (new6_measurement_pair_purity label)) φ hφ U hU p c hc

end UnifiedEJM.PhysicsEndpointStabilizer
