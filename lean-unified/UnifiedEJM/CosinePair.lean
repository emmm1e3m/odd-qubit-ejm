import UnifiedEJM.CosineCount

noncomputable section
open scoped BigOperators Matrix
open Complex OddEJM OddEJM.CircuitPauli
open UnifiedEJM.EvenWalsh UnifiedEJM.StabilizerMarginal

namespace UnifiedEJM.CosineEndpoint

def pairMask (n : ℕ) (a : Pair) : Bits n :=
  a.1 • unitBit n 0 + a.2 • unitBit n 1

def preMask (n : ℕ) (b : Pair) : Bits n :=
  b.1 • CircuitPauli.tailMask n 0 + b.2 • CircuitPauli.tailMask n 1

def pullX (n : ℕ) (a b : Pair) : Bits n :=
  setBit (difference (pairMask n a)) (n-1) (b.1+b.2)

def pullZ (n : ℕ) (b : Pair) : Bits n := setBit (preMask n b) (n-1) 0

theorem pair_pullback {n : ℕ} (hn : 4 ≤ n) (a b : Pair) (c : ℂ) (ψ : Vec n) :
    pauliAction (pairMask n a) (pairMask n b) c (circuit ψ) =
      circuit (pauliAction (pullX n a b) (pullZ n b) c ψ) := by
  have hB (z : Bits n) :
      character (pairMask n b) z = character (preMask n b) (difference z) := by
    simp only [character, pairMask, preMask, OddEJM.dot_add_left, dot_smul_left]
    rw [dot_unit_left,dot_unit_left,dot_tail _ 0 (by omega),
      dot_tail _ 1 (by omega),suffix_difference]
    simp [coord,show 0<n by omega,show 1<n by omega]
  have hc : coord (difference (pairMask n a)) (n-1) = 0 := by
    simp [coord, difference, pairMask, unitBit, show n-1<n by omega,
      show n-1 ≠ 0 by omega, show n-1 ≠ 1 by omega, show n-1+1=n by omega]
  have hb : coord (preMask n b) (n-1) = b.1+b.2 := by
    simp [coord, preMask, CircuitPauli.tailMask, show n-1<n by omega,
      show 1 ≤ n-1 by omega]
  simpa only [hc,hb,zero_mul,bitSign_zero,mul_one,pullX,pullZ] using
    circuit_pauli (by omega) (pairMask n a) (pairMask n b) (preMask n b) c ψ hB

theorem pair_expectation {n : ℕ} (hn : 4 ≤ n) (a b : Pair) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n a) (pairMask n b) (pairPhase a b) =
      (star (normFactor n)*normFactor n) *
        (pairPhase a b * star (I ^ weight (pullX n a b))) *
      ∑ z, character (pullX n a b + pullZ n b) z *
        (I ^ (qA z).val * star (I ^ (qA (z+pullX n a b)).val)) := by
  change pauliExpectation (circuit _) _ _ _ = _
  rw [circuit_expectation (by omega) _ _ _ _ _ _ _ (pair_pullback hn a b _ _),
    input_expectation]

theorem pair_zero_last {n : ℕ} (hn : 4 ≤ n) (a b : Pair) (hb : b.1+b.2=1) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n a) (pairMask n b) (pairPhase a b) = 0 := by
  rw [pair_expectation hn]
  have hh : (pullX n a b + pullZ n b) ⟨n-1,by omega⟩ = 1 := by
    simp [pullX,pullZ,setBit,hb]
  rw [correlation_free_zero _ _ ⟨n-1,by omega⟩ (by unfold InE; simp only; omega) hh,
    mul_zero]

theorem pair_zero_first {n : ℕ} (hn : 4 ≤ n) (a b : Pair)
    (ha : a.1+a.2+b.1=1) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n a) (pairMask n b) (pairPhase a b) = 0 := by
  rw [pair_expectation hn]
  have hh : (pullX n a b + pullZ n b) ⟨0,by omega⟩ = 1 := by
    simpa [pullX,pullZ,setBit,difference,pairMask,preMask,coord,
      CircuitPauli.tailMask,unitBit,show 0 ≠ n-1 by omega,
      show 1<n by omega] using ha
  rw [correlation_free_zero _ _ ⟨0,by omega⟩ (by simp [InE]) hh,mul_zero]

theorem pair_identity {n : ℕ} (hn : 4 ≤ n) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n (0,0)) (pairMask n (0,0)) (pairPhase (0,0) (0,0)) = 1 := by
  have h := Physical.seed_normalized (by omega : 0<n)
    (EvenFamily.diagonal n (Real.pi/2) 0) (EvenFamily.diagonal_unit n (Real.pi/2) 0)
  simpa [EvenFamily.seed, pairMask,pairPhase,pauliExpectation,OddEJM.inner,character,dot] using h

theorem pair_yz {n : ℕ} (hn : 4 ≤ n) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n (1,0)) (pairMask n (1,1)) (pairPhase (1,0) (1,1)) = 1 := by
  simpa [pairMask,pairPhase,ZMod.val_one_eq_one_mod] using seed_yz (by omega : 2≤n)

theorem pullX_xx {n : ℕ} (hn : 4 ≤ n) : pullX n (1,1) (0,0) = unitBit n 1 := by
  have hd : difference (unitBit n 0 + unitBit n 1) = unitBit n 1 := by
    rw [difference_add,difference_unit 0 (by omega),difference_unit 1 (by omega)]
    simp only [ite_true, add_zero, one_ne_zero, ite_false, Nat.sub_self]
    rw [show unitBit n 0 + (unitBit n 1 + unitBit n 0) =
      unitBit n 1 + (unitBit n 0 + unitBit n 0) by abel, bits_add_self, add_zero]
  simp only [pullX,pairMask,one_smul,zero_add]
  rw [hd]
  apply setBit_eq_self
  simp [coord_unit _ _ (by omega : 1<n), show n-1 ≠ 1 by omega]

theorem pullZ_zero (n : ℕ) : pullZ n (0,0) = 0 := by
  ext j
  simp [pullZ,preMask,setBit]

theorem normalized_count {n : ℕ} (hn : 4 ≤ n) :
    (star (normFactor n)*normFactor n) * (2:ℂ)^(n-(n/2-2)) =
      ((2:ℂ)^(n/2-2))⁻¹ := by
  have hk : n/2-2 ≤ n := by omega
  have h := normFactor_card n
  apply (mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ (by norm_num : (2:ℂ)≠0))).mp
  rw [mul_assoc,← pow_add,Nat.sub_add_cancel hk]
  exact h

theorem pair_xx {n : ℕ} (hn : 4 ≤ n) (hev : Even n) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n (1,1)) (pairMask n (0,0)) (pairPhase (1,1) (0,0)) =
        ((2:ℂ)^(n/2-2))⁻¹ := by
  rw [pair_expectation hn,pullX_xx hn,pullZ_zero,add_zero,
    flip_one_correlation hn hev,MaskFacts.weight_unit 1 (by omega)]
  have h := normalized_count hn
  have hi (p : ℂ) : I*(I*p) = -p := by rw [← mul_assoc,I_mul_I]; ring
  simpa [pairPhase,mul_assoc,hi] using h

theorem pullX_zy {n : ℕ} (hn : 4 ≤ n) :
    pullX n (0,1) (1,1) = unitBit n 1 + unitBit n 0 := by
  simp only [pullX,pairMask,zero_smul,one_smul,zero_add,
    show (1:Bit)+1=0 by decide]
  rw [difference_unit 1 (by omega)]
  simp only [show ¬(1:ℕ)=0 by omega, ite_false, Nat.sub_self]
  apply setBit_eq_self
  simp [coord_add,coord_unit _ _ (by omega : 1<n),coord_unit _ _ (by omega : 0<n),
    show n-1 ≠ 1 by omega,show n-1 ≠ 0 by omega]

theorem pullZ_zy {n : ℕ} (hn : 4 ≤ n) : pullZ n (1,1) = unitBit n 0 := by
  ext j
  by_cases hj : j.val=0
  · simp [pullZ,preMask,setBit,CircuitPauli.tailMask,unitBit,hj,
      show 0≠n-1 by omega]
  · by_cases hl : j.val=n-1
    · simp [pullZ,preMask,setBit,unitBit,hj,hl,show n-1≠0 by omega]
    · simp [pullZ,preMask,setBit,CircuitPauli.tailMask,unitBit,hj,hl,
        show 1≤j.val by omega,show (1:Bit)+1=0 by decide]

theorem pair_zy {n : ℕ} (hn : 4 ≤ n) (hev : Even n) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n (0,1)) (pairMask n (1,1)) (pairPhase (0,1) (1,1)) =
        ((2:ℂ)^(n/2-2))⁻¹ := by
  rw [pair_expectation hn,pullX_zy hn,pullZ_zy hn]
  rw [show unitBit n 1 + unitBit n 0 + unitBit n 0 = unitBit n 1 by
    rw [add_assoc,bits_add_self,add_zero]]
  have hq (z : Bits n) : qA (z+(unitBit n 1+unitBit n 0)) = qA (z+unitBit n 1) := by
    rw [← add_assoc,qA_add _ _ (ezero_unit 0 (by simp [InE]))]
  simp_rw [hq]
  rw [flip_one_correlation hn hev,
    MaskFacts.weight_pair 1 0 (by omega) (by omega) (by omega)]
  have h := normalized_count hn
  have hi (p : ℂ) : I*(I*p) = -p := by rw [← mul_assoc,I_mul_I]; ring
  simpa [pairPhase,ZMod.val_one_eq_one_mod,pow_two,mul_assoc,hi] using h

/-- 所有16个真实两体Pauli系数，仅四项非零。 -/
theorem pair_table {n : ℕ} (hn : 4 ≤ n) (hev : Even n) (a b : Pair) :
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (pairMask n a) (pairMask n b) (pairPhase a b) =
      if a=(0,0) ∧ b=(0,0) ∨ a=(1,0) ∧ b=(1,1) then 1 else
      if a=(1,1) ∧ b=(0,0) ∨ a=(0,1) ∧ b=(1,1) then ((2:ℂ)^(n/2-2))⁻¹ else 0 := by
  rcases a with ⟨a₀,a₁⟩
  rcases b with ⟨b₀,b₁⟩
  rcases OddEJM.bit_cases a₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases a₁ with rfl | rfl <;>
    rcases OddEJM.bit_cases b₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases b₁ with rfl | rfl
  all_goals simp only [Prod.mk.injEq,zero_ne_one,one_ne_zero,and_self,or_self,
    and_false,false_and,true_and,and_true,false_or,or_false,ite_true,ite_false]
  · exact pair_identity hn
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_zero_first hn _ _ (by decide)
  · exact pair_zero_first hn _ _ (by decide)
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_zy hn hev
  · exact pair_zero_first hn _ _ (by decide)
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_yz hn
  · exact pair_xx hn hev
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_zero_last hn _ _ (by decide)
  · exact pair_zero_first hn _ _ (by decide)

theorem pairMask_embed {n : ℕ} (hn : 4≤n) (a : Pair) :
    pairMask n a = embedPair ⟨0,by omega⟩ ⟨1,by omega⟩ a := by
  ext j
  by_cases h0 : j.val=0
  · have hj : j=(⟨0,by omega⟩:Fin n) := Fin.ext h0
    rw [hj]; simp [pairMask,embedPair,unitBit]
  · by_cases h1 : j.val=1
    · have hj : j=(⟨1,by omega⟩:Fin n) := Fin.ext h1
      rw [hj]; simp [pairMask,embedPair,unitBit]
    · have hj0 : j≠(⟨0,by omega⟩:Fin n) := by intro h; exact h0 (congrArg Fin.val h)
      have hj1 : j≠(⟨1,by omega⟩:Fin n) := by intro h; exact h1 (congrArg Fin.val h)
      simp [pairMask,embedPair,unitBit,h0,h1,hj0,hj1]

theorem pair_purity {n : ℕ} (hn : 4≤n) (hev : Even n) :
    Multipartite.cutPurity ({⟨0,by omega⟩,⟨1,by omega⟩}:Finset (Fin n))
      (EvenFamily.seed n (Real.pi/2) 0) =
        (1/2:ℂ) + (((2:ℂ)^(n/2-2))⁻¹)^2/2 := by
  have h := pair_parseval (pairReduced ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp [Fin.ext_iff])
    (EvenFamily.seed n (Real.pi/2) 0))
  rw [pairReduced_purity] at h
  simp_rw [pair_coefficient_expectation,PhysicsEndpoint.HermitianPauli.act,
    inner_pauliExpectation] at h
  change 4 * Multipartite.cutPurity _ (EvenFamily.seed n (Real.pi/2) 0) =
    ∑ a : Pair, ∑ b : Pair,
      (pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
        (embedPair _ _ a) (embedPair _ _ b) (pairPhase a b))^2 at h
  simp_rw [← pairMask_embed hn,pair_table hn hev] at h
  simp only [Fintype.sum_prod_type,sum_bit] at h
  norm_num at h
  linear_combination h / 4

end UnifiedEJM.CosineEndpoint
