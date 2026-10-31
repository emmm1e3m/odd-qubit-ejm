import UnifiedEJM.LowDimensionalDefs
import OddEJM.LocalExpectation
import OddEJM.Density

noncomputable section
namespace UnifiedEJM.LowDimensional
open OddEJM Complex
open scoped BigOperators
set_option maxHeartbeats 4000000

/-- 计算基整数编号，最高位在左。 -/
def bits (z : Fin 16) : Bits 4 :=
  ![((z.val / 8 : ℕ) : Bit), ((z.val / 4 : ℕ) : Bit), ((z.val / 2 : ℕ) : Bit), (z.val : Bit)]

def index (z : Bits 4) : Fin 16 :=
  ⟨(z 0).val * 8 + (z 1).val * 4 + (z 2).val * 2 + (z 3).val, by
    have h0 := (z 0).val_lt
    have h1 := (z 1).val_lt
    have h2 := (z 2).val_lt
    have h3 := (z 3).val_lt
    norm_num at h0 h1 h2 h3
    omega⟩

theorem index_bits : ∀ z, index (bits z) = z := by decide
theorem bits_index : ∀ z, bits (index z) = z := by decide

def basisEquiv : Fin 16 ≃ Bits 4 where
  toFun := bits
  invFun := index
  left_inv := index_bits
  right_inv := bits_index

def flipMask : Fin 12 → Fin 16 := ![8,9,1,12,13,1,6,7,1,2,3,1]
def charMask : Fin 12 → Fin 16 := ![0,14,14,0,6,6,0,2,2,1,1,0]
def pauliPhase : Fin 12 → ℂ := ![1,I,1,1,I,1,1,I,1,1,I,1]

def basePhase : Fin 16 → ℂ :=
  ![1,1,1,I,1,I,I,-1,1,I,I,-1,I,-1,-1,-I]

def weightTable : Fin 16 → ℕ := ![0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4]


theorem weight_certificate : ∀ z, weight (bits z) = weightTable z := by decide
theorem bits_zero_iff : ∀ z, bits z = 0 ↔ z = 0 := by decide

theorem basePhase_original (z : Fin 16) : basePhase z = originalDiagonal (bits z) := by
  rw [originalDiagonal_eq_rawPhase_zero (by norm_num), rawPhase_basepoint]
  simp only [weight_certificate, bits_zero_iff]
  fin_cases z <;> norm_num [basePhase, weightTable, Complex.I_sq]

theorem bits_flip (p : Fin 12) (z : Fin 16) :
    bits (flip p z) = bits z + bits (flipMask p) := by
  exact (show ∀ p z, bits (flip p z) = bits z + bits (flipMask p) by decide) p z

def charTable : Fin 12 → Fin 16 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1], ![1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1], ![1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1], ![1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1], ![1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1], ![1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]


theorem charTable_certificate : ∀ p z,
    (if dot (bits (charMask p)) (bits z) = 0 then (1:ℤ) else -1) = charTable p z := by decide

theorem character_certificate (p : Fin 12) (z : Fin 16) :
    character (bits (charMask p)) (bits z) = (charTable p z : ℂ) := by
  rw [← charTable_certificate]
  unfold character bitSign
  split <;> norm_num

/-- 原电路拉回的系数表，逐有限项由内核检查。 -/
theorem coefficient_certificate (p : Fin 12) (z : Fin 16) :
    star (basePhase (flip p z)) * pauliPhase p *
      character (bits (charMask p)) (bits z) * basePhase z =
      (coeffR p z : ℂ) + (coeffI p z : ℂ) * I := by
  rw [character_certificate]
  fin_cases p <;> fin_cases z <;>
    norm_num [basePhase, flip, pauliPhase, charTable, coeffR, coeffI, Complex.I_sq]

theorem anglePhase_star_mul_anglePhase (a b : ℝ) :
    star (anglePhase a) * anglePhase b = anglePhase (b-a) := by
  simp only [anglePhase, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
    map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  congr 1
  ring

def lineDiagonal (d : Direction) (t : ℝ) (z : Bits 4) : ℂ :=
  originalDiagonal z * anglePhase (d (index z)*t)

def lineSeed (d : Direction) (t : ℝ) : Vec 4 :=
  circuit (fun z => normFactor 4 * lineDiagonal d t z)

def signedLocal (v : Vec 4) : Fin 12 → ℂ :=
  ![localX v 0,localY v 0,localZ v 0,localX v 1,localY v 1,localZ v 1,
    localX v 2,localY v 2,localZ v 2,localX v 3,-localY v 3,localZ v 3]

def pulledA : Fin 12 → Bits 4 :=
  ![unitBit 4 0, unitBit 4 0 + unitBit 4 3, unitBit 4 3,
    unitBit 4 1 + unitBit 4 0, (unitBit 4 1 + unitBit 4 0) + unitBit 4 3, unitBit 4 3,
    unitBit 4 2 + unitBit 4 1, (unitBit 4 2 + unitBit 4 1) + unitBit 4 3, unitBit 4 3,
    unitBit 4 2, unitBit 4 3 + unitBit 4 2, unitBit 4 3]

def pulledB : Fin 12 → Bits 4 :=
  ![0, setBit (CircuitPauli.tailMask 4 0) 3 0, setBit (CircuitPauli.tailMask 4 0) 3 0,
    0, setBit (CircuitPauli.tailMask 4 1) 3 0, setBit (CircuitPauli.tailMask 4 1) 3 0,
    0, setBit (CircuitPauli.tailMask 4 2) 3 0, setBit (CircuitPauli.tailMask 4 2) 3 0,
    unitBit 4 3, unitBit 4 3, setBit (CircuitPauli.tailMask 4 3) 3 0]

theorem pulledA_certificate : ∀ p, bits (flipMask p) = pulledA p := by decide
theorem pulledB_certificate : ∀ p, bits (charMask p) = pulledB p := by decide

theorem expectation_neg_phase (f : Vec 4) (a b : Bits 4) (c : ℂ) :
    pauliExpectation f a b (-c) = -pauliExpectation f a b c := by
  simp [pauliExpectation, Finset.sum_neg_distrib]

/-- 原门共轭把所有实际单比特 Pauli 变成证书所用的单项掩码。 -/
theorem signed_circuit_pullback (f : Vec 4) (p : Fin 12) :
    signedLocal (circuit f) p =
      pauliExpectation f (bits (flipMask p)) (bits (charMask p)) (pauliPhase p) := by
  rw [pulledA_certificate, pulledB_certificate]
  fin_cases p
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localX_beforeLast 0 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localX] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localY_beforeLast 0 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localY] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localZ_table (by norm_num) 0 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localZ] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localX_beforeLast 1 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localX] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localY_beforeLast 1 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localY] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localZ_table (by norm_num) 1 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localZ] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localX_beforeLast 2 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localX] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localY_beforeLast 2 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localY] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localZ_table (by norm_num) 2 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localZ] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localX_last (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localX] using h
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localY_last (by norm_num) f)
    have hn := congrArg Neg.neg h
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localY, expectation_neg_phase] using hn
  · have h := CircuitPauli.circuit_expectation (by norm_num : 0 < 4) f _ _ _ _ _ _
      (CircuitPauli.localZ_table (by norm_num) 3 (by norm_num) f)
    simpa [signedLocal, pulledA, pulledB, pauliPhase, localZ] using h

theorem rawPhase_expectation_signal (d : Direction) (p : Fin 12) (t : ℝ) :
    (pauliExpectation (lineDiagonal d t) (bits (flipMask p))
      (bits (charMask p)) (pauliPhase p)).re = signal d p t := by
  unfold pauliExpectation
  rw [← Fintype.sum_equiv basisEquiv (fun z =>
    star (lineDiagonal d t (bits z + bits (flipMask p))) * pauliPhase p *
      character (bits (charMask p)) (bits z) * lineDiagonal d t (bits z))
    _ (fun z => rfl)]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← bits_flip, lineDiagonal, lineDiagonal, index_bits, index_bits,
    ← basePhase_original, ← basePhase_original, star_mul]
  have he :
      (star (anglePhase (d (flip p z)*t)) * star (basePhase (flip p z))) *
        pauliPhase p * character (bits (charMask p)) (bits z) *
        (basePhase z * anglePhase (d z*t)) =
      (star (basePhase (flip p z)) * pauliPhase p *
        character (bits (charMask p)) (bits z) * basePhase z) *
      (star (anglePhase (d (flip p z)*t)) * anglePhase (d z*t)) := by ring
  rw [he, coefficient_certificate, anglePhase_star_mul_anglePhase]
  have hd : d z*t - d (flip p z)*t = frequency d p z*t := by
    simp only [frequency]; ring
  rw [hd]
  simp only [anglePhase]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- 从原始规范化振幅计算的实际期望，与有限信号和完全一致。 -/
theorem signed_lineSeed_signal (d : Direction) (p : Fin 12) (t : ℝ) :
    (signedLocal (lineSeed d t) p).re = signal d p t / 16 := by
  rw [lineSeed, signed_circuit_pullback, pauliExpectation_scale]
  have hn : normFactor 4 = (1/4 : ℂ) := by norm_num [normFactor]
  rw [hn]
  norm_num [Complex.mul_re, rawPhase_expectation_signal]
  ring

end UnifiedEJM.LowDimensional



