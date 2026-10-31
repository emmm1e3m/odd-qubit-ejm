import UnifiedEJM.NormalizedInvariants
import UnifiedEJM.FourQubitMarginal
import UnifiedEJM.SingleInvariants

noncomputable section
open scoped BigOperators Matrix
open Complex
namespace UnifiedEJM.FiniteInvariants
private theorem base_purity_eq_sum (A : Mat) : purity A =
    ∑ i, ∑ j, (∑ k, A i k * star (A j k)) * (∑ l, A j l * star (A i l)) := by
  rfl


def exponentBase : Fin 16 → ℤ :=
  ![0,0,0,1,0,1,1,2,0,1,1,2,1,2,2,3]

theorem exponentBase_checked : ∀ k : Fin 16,
    OddEJM.originalExponent (decode4 k) = exponentBase k := by decide

theorem phaseBase_original (k : Fin 16) :
    phaseBase k = OddEJM.originalDiagonal (decode4 k) := by
  unfold OddEJM.originalDiagonal
  rw [exponentBase_checked]
  fin_cases k <;> norm_num [phaseBase,exponentBase,Complex.I_sq,Complex.I_pow_three]

theorem stateBase_actual_seed (k : Fin 16) :
    stateBase k = OddEJM.circuit
      (fun z => OddEJM.normFactor 4 * OddEJM.originalDiagonal z) (decode4 k) := by
  have hfun : (fun z : OddEJM.Bits 4 => OddEJM.originalDiagonal z) =
      (fun z => phaseBase (encode4 z)) := by
    funext z
    rw [phaseBase_original,decode_encode4]
  simp_rw [hfun]
  rw [circuit_const_mul]
  simp only [gateNumerator_circuit]
  have hn : OddEJM.normFactor 4 = (4:ℂ)⁻¹ := by norm_num [OddEJM.normFactor]
  rw [hn]
  unfold stateBase numeratorBase normalization
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_base_pair_purity : sumPurity numeratorBase = 1128 := by
  simp only [sumPurity,base_purity_eq_sum]
  norm_num [numeratorBase,gateNumerator,phaseBase,reshape12,reshape13,reshape14,
    Fin.sum_univ_succ]
  ring_nf
  norm_num [map_ofNat,Complex.I_sq,Complex.I_pow_three,Complex.I_pow_four] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_base_single_purity (j : Fin 4) :
    UnifiedEJM.PurityInvariant.purity (reshape1 j numeratorBase) = 536 := by
  fin_cases j <;> simp only [single_purity_eq_sum] <;>
    norm_num [reshape1,numeratorBase,gateNumerator,phaseBase,Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [map_ofNat,Complex.I_sq,Complex.I_pow_three,Complex.I_pow_four] <;> ring

theorem base_pair_purity : sumPurity stateBase = 141/128 := by
  unfold stateBase
  rw [sumPurity_smul,normalization_norm,raw_base_pair_purity]
  norm_num

theorem base_single_purity : singlePuritySum stateBase = 67/32 := by
  unfold stateBase
  rw [singlePuritySum_smul,normalization_norm]
  simp [singlePuritySum,raw_base_single_purity]
  norm_num

end UnifiedEJM.FiniteInvariants
