import UnifiedEJM.CosinePair
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped BigOperators Matrix
open Complex OddEJM OddEJM.CircuitPauli
open UnifiedEJM.StabilizerMarginal UnifiedEJM.Multipartite

namespace UnifiedEJM.CosineEndpoint

/-- 与期望约定一致的真实两比特Pauli矩阵。 -/
def pairMatrix (a b : Pair) : Matrix Pair Pair ℂ :=
  fun row col => if col=row+a then pairPhase a b * pairChar b col else 0

theorem pair_reconstruction (R : Matrix Pair Pair ℂ) (row col : Pair) :
    R row col = (1/4:ℂ) * ∑ a : Pair, ∑ b : Pair,
      coefficient R a b * pairMatrix a b row col := by
  rcases row with ⟨r₀,r₁⟩
  rcases col with ⟨c₀,c₁⟩
  rcases OddEJM.bit_cases r₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases r₁ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₁ with rfl | rfl <;>
    norm_num [coefficient,pairMatrix,pairPhase,pairChar,Fintype.sum_prod_type,sum_bit,
      bitSign,ZMod.val_one_eq_one_mod,Prod.fst_add,Prod.snd_add,
      show (2:Bit)=0 by decide] <;> ring_nf <;>
      simp [show (2:Bit)=0 by decide, I_sq] <;> ring

/-- 实际偏迹的矩阵表达，首项是单位阵；其余分别为YZ、XX、ZY。 -/
theorem seed_pairReduced {n : ℕ} (hn : 4≤n) (hev : Even n) :
    pairReduced ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp [Fin.ext_iff])
      (EvenFamily.seed n (Real.pi/2) 0) =
      (1/4:ℂ) • (pairMatrix (0,0) (0,0) + pairMatrix (1,0) (1,1) +
        ((2:ℂ)^(n/2-2))⁻¹ • (pairMatrix (1,1) (0,0) + pairMatrix (0,1) (1,1))) := by
  apply Matrix.ext
  intro row col
  rw [pair_reconstruction (pairReduced (⟨0,by omega⟩:Fin n) ⟨1,by omega⟩
    (by simp [Fin.ext_iff]) (EvenFamily.seed n (Real.pi/2) 0)) row col]
  simp_rw [pair_coefficient_expectation,PhysicsEndpoint.HermitianPauli.act,
    inner_pauliExpectation]
  change (1/4:ℂ) * (∑ a : Pair, ∑ b : Pair,
    pauliExpectation (EvenFamily.seed n (Real.pi/2) 0)
      (embedPair _ _ a) (embedPair _ _ b) (pairPhase a b) * pairMatrix a b row col) = _
  simp_rw [← pairMask_embed hn,pair_table hn hev]
  simp only [Fintype.sum_prod_type,sum_bit]
  norm_num
  ring

theorem pairMatrix_identity : pairMatrix (0,0) (0,0) = 1 := by
  ext row col
  simp [pairMatrix,pairPhase,pairChar,Matrix.one_apply,eq_comm, show ((0,0):Pair)=0 from rfl]

theorem pairMatrix_yz : pairMatrix (1,0) (1,1) =
    Matrix.kronecker sigmaY sigmaZ := by
  ext row col
  rcases row with ⟨r₀,r₁⟩
  rcases col with ⟨c₀,c₁⟩
  rcases OddEJM.bit_cases r₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases r₁ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₁ with rfl | rfl <;>
    norm_num [pairMatrix,pairPhase,pairChar,Matrix.kronecker,sigmaY,sigmaZ,
      bitSign,ZMod.val_one_eq_one_mod,show (2:Bit)=0 by decide] <;>
      simp [show (2:Bit)=0 by decide, I_sq]

theorem pairMatrix_xx : pairMatrix (1,1) (0,0) =
    Matrix.kronecker sigmaX sigmaX := by
  ext row col
  rcases row with ⟨r₀,r₁⟩
  rcases col with ⟨c₀,c₁⟩
  rcases OddEJM.bit_cases r₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases r₁ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₁ with rfl | rfl <;>
    norm_num [pairMatrix,pairPhase,pairChar,Matrix.kronecker,sigmaX,
      bitSign,ZMod.val_one_eq_one_mod,show (2:Bit)=0 by decide] <;>
      simp [show (2:Bit)=0 by decide, I_sq]

theorem pairMatrix_zy : pairMatrix (0,1) (1,1) =
    Matrix.kronecker sigmaZ sigmaY := by
  ext row col
  rcases row with ⟨r₀,r₁⟩
  rcases col with ⟨c₀,c₁⟩
  rcases OddEJM.bit_cases r₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases r₁ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₀ with rfl | rfl <;>
    rcases OddEJM.bit_cases c₁ with rfl | rfl <;>
    norm_num [pairMatrix,pairPhase,pairChar,Matrix.kronecker,sigmaY,sigmaZ,
      bitSign,ZMod.val_one_eq_one_mod,show (2:Bit)=0 by decide] <;>
      simp [show (2:Bit)=0 by decide, I_sq]

theorem seed_rho12 {n : ℕ} (hn : 4≤n) (hev : Even n) :
    pairReduced ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp [Fin.ext_iff])
      (EvenFamily.seed n (Real.pi/2) 0) =
      (1/4:ℂ) • ((1:Matrix Pair Pair ℂ) + Matrix.kronecker sigmaY sigmaZ +
        ((2:ℂ)^(n/2-2))⁻¹ •
          (Matrix.kronecker sigmaX sigmaX + Matrix.kronecker sigmaZ sigmaY)) := by
  rw [seed_pairReduced hn hev,pairMatrix_identity,pairMatrix_yz,pairMatrix_xx,pairMatrix_zy]

theorem pair_in_cuts {n : ℕ} (hn : 4≤n) :
    ({⟨0,by omega⟩,⟨1,by omega⟩}:Finset (Fin n)) ∈ cuts n := by
  simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · simp
  · intro h
    have hm : (⟨2,by omega⟩:Fin n) ∈ ({⟨0,by omega⟩,⟨1,by omega⟩}:Finset (Fin n)) := by
      rw [h]; simp
    norm_num at hm

theorem seed_gme_bound {n : ℕ} (hn : 4≤n) (hev : Even n) :
    gme (by omega : 2≤n) (EvenFamily.seed n (Real.pi/2) 0) ≤
      Real.sqrt (1 - (((2:ℝ)^(n/2-2))⁻¹)^2) := by
  have hle : gme (by omega : 2≤n) (EvenFamily.seed n (Real.pi/2) 0) ≤
      Real.sqrt (2*(1-(cutPurity ({⟨0,by omega⟩,⟨1,by omega⟩}:Finset (Fin n))
        (EvenFamily.seed n (Real.pi/2) 0)).re)) :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_,pair_in_cuts hn,rfl⟩)
  rw [pair_purity hn hev] at hle
  have hr : ((1/2:ℂ) + (((2:ℂ)^(n/2-2))⁻¹)^2/2).re =
      1/2 + (((2:ℝ)^(n/2-2))⁻¹)^2/2 := by
    have hc : ((1/2 + (((2:ℝ)^(n/2-2))⁻¹)^2/2 : ℝ) : ℂ) =
        (1/2:ℂ) + (((2:ℂ)^(n/2-2))⁻¹)^2/2 := by push_cast; rfl
    rw [← hc]
    rfl
  rw [hr] at hle
  convert hle using 1 <;> congr 1 <;> ring

theorem seed_gme_lt_one {n : ℕ} (hn : 4≤n) (hev : Even n) :
    gme (by omega : 2≤n) (EvenFamily.seed n (Real.pi/2) 0) < 1 := by
  apply lt_of_le_of_lt (seed_gme_bound hn hev)
  apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).2
  have h : 0 < (((2:ℝ)^(n/2-2))⁻¹)^2 := by positivity
  nlinarith

theorem measurement_purity {n : ℕ} (hn : 4≤n) (hev : Even n) (label : Bits n) :
    cutPurity ({⟨0,by omega⟩,⟨1,by omega⟩}:Finset (Fin n))
      (EvenFamily.measurement n (Real.pi/2) 0 label) =
        (1/2:ℂ) + (((2:ℂ)^(n/2-2))⁻¹)^2/2 := by
  rw [show EvenFamily.measurement n (Real.pi/2) 0 label =
    Physical.measurement (EvenFamily.diagonal n (Real.pi/2) 0) label from rfl,
    cutPurity_measurement (by omega)]
  exact pair_purity hn hev

theorem measurement_gme_bound {n : ℕ} (hn : 4≤n) (hev : Even n) (label : Bits n) :
    gme (by omega : 2≤n) (EvenFamily.measurement n (Real.pi/2) 0 label) ≤
      Real.sqrt (1 - (((2:ℝ)^(n/2-2))⁻¹)^2) := by
  rw [show EvenFamily.measurement n (Real.pi/2) 0 label =
    Physical.measurement (EvenFamily.diagonal n (Real.pi/2) 0) label from rfl,
    gme_measurement]
  exact seed_gme_bound hn hev

end UnifiedEJM.CosineEndpoint
