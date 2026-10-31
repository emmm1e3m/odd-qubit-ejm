import UnifiedEJM.ThreeQubitModel
open scoped BigOperators
open OddEJM
namespace UnifiedEJM.ThreeQubit

def bits : Fin 8 → Bits 3 :=
  ![![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
    ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]]
def index (z : Bits 3) : Fin 8 :=
  ⟨(4 * (z 0).val + 2 * (z 1).val + (z 2).val) % 8, Nat.mod_lt _ (by decide)⟩
lemma index_bits : ∀ k, index (bits k) = k := by decide
lemma bits_index : ∀ z, bits (index z) = z := by decide
def basisEquiv : Fin 8 ≃ Bits 3 where
  toFun := bits
  invFun := index
  left_inv := index_bits
  right_inv := bits_index
lemma original_exp_table (k : Fin 8) :
    originalExponent (bits k) = (![0,0,0,1,0,1,1,2] : Fin 8 → ℤ) k := by
  exact (show ∀ k : Fin 8, originalExponent (bits k) =
    (![0,0,0,1,0,1,1,2] : Fin 8 → ℤ) k by decide) k

lemma original_diag_table (k : Fin 8) :
    originalDiagonal (bits k) = (![1,1,1,Complex.I,1,Complex.I,Complex.I,-1] : Fin 8 → ℂ) k := by
  rw [originalDiagonal, original_exp_table]
  fin_cases k <;> norm_num [Complex.I_sq]



def circuitGate : Matrix (Fin 8) (Fin 8) ℝ := ![![1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, -1, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, -1], ![0, 0, 1, 1, 0, 0, 0, 0], ![1, -1, 0, 0, 0, 0, 0, 0]]

lemma normalization_product : (Real.sqrt 2 : ℂ)⁻¹ * normFactor 3 = (1/4:ℂ) := by
  have hs : Real.sqrt 2 * Real.sqrt 8 = 4 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hc : (Real.sqrt 2 : ℂ) * (Real.sqrt 8 : ℂ) = 4 := by exact_mod_cast hs
  norm_num only [normFactor, show (2:ℝ)^3 = 8 by norm_num]
  rw [← mul_inv, hc]
  norm_num
lemma circuit_table (u : Bits 3 → ℂ) (j : Fin 8) :
    circuit (fun z => normFactor 3 * u z) (bits j) =
      (1/4:ℂ) * ∑ k, (circuitGate j k : ℂ) * u (bits k) := by
  change (Real.sqrt 2 : ℂ)⁻¹ *
    (normFactor 3 * u (setBit (difference (bits j)) 2 0) +
      bitSign (coord (difference (bits j)) 2) *
        (normFactor 3 * u (setBit (difference (bits j)) 2 1))) = _
  have hf (a b c : ℂ) : (Real.sqrt 2 : ℂ)⁻¹ *
      (normFactor 3 * a + c * (normFactor 3 * b)) = (1/4:ℂ) * (a + c*b) := by
    calc
      _ = ((Real.sqrt 2 : ℂ)⁻¹ * normFactor 3) * (a+c*b) := by ring
      _ = _ := by rw [normalization_product]
  rw [hf]
  rw [← bits_index (setBit (difference (bits j)) 2 0),
      ← bits_index (setBit (difference (bits j)) 2 1)]
  fin_cases j <;> norm_num [index, bits, difference, coord, setBit, bitSign,
    circuitGate, Fin.sum_univ_succ, ZMod.val_one_eq_one_mod, ZMod.cast, ZMod.val_natCast, ZMod.val_ofNat] <;> ring




noncomputable section
lemma diagonal_parts (k : Fin 8) :
    originalDiagonal (bits k) = (baseRe k : ℂ) + Complex.I * (baseIm k : ℂ) := by
  rw [original_diag_table]
  fin_cases k <;> norm_num [baseRe, baseIm]
lemma input_complex (θ : Space) (k : Fin 8) :
    originalDiagonal (bits k) * anglePhase (phase θ k) =
      (inputRe θ k : ℂ) + Complex.I * (inputIm θ k : ℂ) := by
  rw [diagonal_parts]
  simp only [anglePhase, Complex.exp_ofReal_mul_I, inputRe, inputIm,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]
lemma state_table (θ : Space) (j : Fin 8) :
    state θ j = (1/4:ℂ) * ∑ k, (circuitGate j k : ℂ) *
      (originalDiagonal (bits k) * anglePhase (phase θ k)) := by
  simp_rw [input_complex]
  change state θ j = (1/4:ℂ) * ∑ k, (gate j k : ℂ) *
    ((inputRe θ k : ℂ) + Complex.I * (inputIm θ k : ℂ))
  apply Complex.ext <;> simp [state, ampRe, ampIm]

/-- 与旧工程的原始基本对称相位、原始CNOT链逐振幅相同。 -/
def physicalDiagonal (θ : Space) (z : Bits 3) : ℂ :=
  originalDiagonal z * anglePhase (phase θ (index z))
def physicalSeed (θ : Space) : Vec 3 :=
  circuit (fun z => normFactor 3 * physicalDiagonal θ z)
lemma state_eq_physicalSeed (θ : Space) (j : Fin 8) :
    state θ j = physicalSeed θ (bits j) := by
  rw [physicalSeed, circuit_table, state_table]
  simp [physicalDiagonal, index_bits]

def opA : Fin 9 → Bits 3 :=
  ![![1,0,0], ![1,0,0], ![0,0,0], ![0,1,0], ![0,1,0],
    ![0,0,0], ![0,0,1], ![0,0,1], ![0,0,0]]
def opB : Fin 9 → Bits 3 :=
  ![![0,0,0], ![1,0,0], ![1,0,0], ![0,0,0], ![0,1,0],
    ![0,1,0], ![0,0,0], ![0,0,1], ![0,0,1]]
def opC : Fin 9 → ℂ := ![1,Complex.I,1,1,Complex.I,1,1,-Complex.I,1]
lemma op_flip : ∀ p j, bits j + opA p = bits (flip p j) := by decide
lemma op_coefficient (p : Fin 9) (j : Fin 8) :
    opC p * character (opB p) (bits j) =
      (pauliRe p j : ℂ) + Complex.I * (pauliIm p j : ℂ) := by
  fin_cases p <;> fin_cases j <;>
    norm_num [opC, opB, character, dot, bitSign, bits, pauliRe, pauliIm,
      Fin.sum_univ_succ, ZMod.val_one_eq_one_mod, ZMod.val_ofNat, ZMod.val_natCast]

/-- 九个真实单比特Pauli；只把末位Y改为负号。 -/
def physicalExpectation (θ : Space) (p : Fin 9) : ℂ :=
  pauliExpectation (physicalSeed θ) (opA p) (opB p) (opC p)
lemma expectation_eq_physical (θ : Space) (p : Fin 9) :
    expectation θ p = (physicalExpectation θ p).re := by
  let term (z : Bits 3) : ℂ :=
    star (physicalSeed θ (z + opA p)) * opC p * character (opB p) z * physicalSeed θ z
  change expectation θ p = (∑ z, term z).re
  rw [← Fintype.sum_equiv basisEquiv (fun j => term (bits j)) term (fun _ => rfl)]
  simp only [term, op_flip, ← state_eq_physicalSeed, Complex.re_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc (star (state θ (flip p j))) (opC p) (character (opB p) (bits j)),
    op_coefficient]
  simp [state, Complex.mul_re, Complex.mul_im]
  ring

end
end UnifiedEJM.ThreeQubit

