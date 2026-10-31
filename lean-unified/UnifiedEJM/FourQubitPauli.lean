import UnifiedEJM.PauliTensor
import UnifiedEJM.FourQubit

namespace UnifiedEJM.Physical
open OddEJM OddEJM.CircuitPauli
open scoped Matrix BigOperators

/-- 四比特十进制重排仅改变索引，实际Pauli作用仍为四个局域酉的张量积。 -/
theorem pauliAction_tensor_fin16 (a b : Bits 4) (v : FiniteInvariants.State) (k : Fin 16) :
    pauliAction a b 1 (fun z => v (FiniteInvariants.encode4 z)) (FiniteInvariants.decode4 k) =
      ∑ l : Fin 16, (∏ j : Fin 4, pauliMatrix (a j) (b j)
        (FiniteInvariants.decode4 k j) (FiniteInvariants.decode4 l j)) * v l := by
  rw [pauliAction_tensor]
  have h := Equiv.sum_comp FiniteInvariants.decode4Equiv
    (fun w : Bits 4 => (∏ j : Fin 4, pauliMatrix (a j) (b j)
      (FiniteInvariants.decode4 k j) (w j)) * v (FiniteInvariants.encode4 w))
  simpa only [FiniteInvariants.decode4Equiv, Equiv.coe_fn_mk,
    FiniteInvariants.encode_decode4] using h.symm

/-- 任意四比特相位的测量列，逐振幅是其种子上的局域酉张量作用。 -/
theorem measurement_tensor_fin16 (u : Bits 4 → ℂ) (label : Bits 4) (k : Fin 16) :
    measurement u label (FiniteInvariants.decode4 k) =
      ∑ l : Fin 16, (∏ j : Fin 4,
        pauliMatrix (orbitX label j) (orbitZ label j)
          (FiniteInvariants.decode4 k j) (FiniteInvariants.decode4 l j)) *
        seed u (FiniteInvariants.decode4 l) := by
  rw [measurement_orbit (by norm_num)]
  have h := pauliAction_tensor_fin16 (orbitX label) (orbitZ label)
    (fun l => seed u (FiniteInvariants.decode4 l)) k
  simpa only [FiniteInvariants.decode_encode4] using h

end UnifiedEJM.Physical

