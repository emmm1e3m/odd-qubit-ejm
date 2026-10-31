import OddEJM.OriginalPhase
import OddEJM.Pauli
import OddEJM.LocalExpectation
import OddEJM.Density
import Mathlib.Tactic

namespace UnifiedEJM.CurvedPhysical
open OddEJM Complex
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-- 计算基标签采用最高位在左的整数顺序。 -/
def encode (k : Fin 16) : Bits 4 :=
  ![(k.val / 8 : ℕ), (k.val / 4 : ℕ), (k.val / 2 : ℕ), k.val]

def index (z : Bits 4) : Fin 16 :=
  ⟨8 * (z 0).val + 4 * (z 1).val + 2 * (z 2).val + (z 3).val, by
    have h0 := ZMod.val_lt (z 0)
    have h1 := ZMod.val_lt (z 1)
    have h2 := ZMod.val_lt (z 2)
    have h3 := ZMod.val_lt (z 3)
    omega⟩

@[simp] theorem index_encode (k : Fin 16) : index (encode k) = k := by
  exact (show ∀ k : Fin 16, index (encode k) = k by decide) k

@[simp] theorem encode_index (z : Bits 4) : encode (index z) = z := by
  exact (show ∀ z : Bits 4, encode (index z) = z by decide) z

@[simp] theorem encode_add (k a : Fin 16) :
    encode k + encode a = encode (k ^^^ a) := by
  exact (show ∀ k a : Fin 16, encode k + encode a = encode (k ^^^ a) by decide) k a

def basisEquiv : Fin 16 ≃ Bits 4 where
  toFun := encode
  invFun := index
  left_inv := index_encode
  right_inv := encode_index

theorem sum_bits4 (f : Bits 4 → ℂ) : (∑ z, f z) = ∑ k : Fin 16, f (encode k) := by
  exact (Equiv.sum_comp basisEquiv f).symm

/-- 两个固定相位掩码。 -/
def bMask : Fin 16 → ℕ := ![0,1,1,1,2,2,0,0,1,1,0,0,0,0,1,1]
def dMask : Fin 16 → ℕ := ![0,1,1,0,1,1,1,1,0,1,0,1,1,1,0,0]

/-- 原始相位与两个角度单项式；这是全部16个输入振幅。 -/
def table (u v : ℂ) : Fin 16 → ℂ :=
  ![1, u*v, u*v, I*u, u^2*v, I*u^2*v, I*v, -v,
    u, I*u*v, I, -v, I*v, -v, -u, -I*u]

def phasePoly (u v : ℂ) (z : Bits 4) : ℂ := table u v (index z)

@[simp] theorem phasePoly_encode (u v : ℂ) (k : Fin 16) :
    phasePoly u v (encode k) = table u v k := by simp [phasePoly]

/-- 原基本对称相位的逐输入精确表。 -/
theorem originalDiagonal_encode (k : Fin 16) :
    originalDiagonal (encode k) =
      (![1,1,1,I,1,I,I,-1,1,I,I,-1,I,-1,-1,-I] : Fin 16 → ℂ) k := by
  have he : ∀ j : Fin 16, originalExponent (encode j) =
      (![0,0,0,1,0,1,1,2,0,1,1,2,1,2,2,3] : Fin 16 → ℤ) j := by decide
  rw [originalDiagonal, he]
  fin_cases k <;> norm_num

theorem phasePoly_original (u v : ℂ) (z : Bits 4) :
    phasePoly u v z = originalDiagonal z * u ^ bMask (index z) * v ^ dMask (index z) := by
  obtain ⟨k, rfl⟩ := basisEquiv.surjective z
  change phasePoly u v (encode k) = originalDiagonal (encode k) * u ^ bMask (index (encode k)) * v ^ dMask (index (encode k))
  rw [phasePoly_encode, index_encode, originalDiagonal_encode]
  fin_cases k <;> simp [table, bMask, dMask]

theorem char_0 (k : Fin 16) :
    character (encode 0) (encode k) =
      (![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] : Fin 16 → ℂ) k := by
  have hd : ∀ j : Fin 16, dot (encode 0) (encode j) =
      (![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 16 → Bit) j := by decide
  rw [character,hd]
  fin_cases k <;> norm_num [bitSign]

theorem char_1 (k : Fin 16) :
    character (encode 1) (encode k) =
      (![1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1] : Fin 16 → ℂ) k := by
  have hd : ∀ j : Fin 16, dot (encode 1) (encode j) =
      (![0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1] : Fin 16 → Bit) j := by decide
  rw [character,hd]
  fin_cases k <;> norm_num [bitSign]

theorem char_2 (k : Fin 16) :
    character (encode 2) (encode k) =
      (![1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1] : Fin 16 → ℂ) k := by
  have hd : ∀ j : Fin 16, dot (encode 2) (encode j) =
      (![0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1] : Fin 16 → Bit) j := by decide
  rw [character,hd]
  fin_cases k <;> norm_num [bitSign]

theorem char_6 (k : Fin 16) :
    character (encode 6) (encode k) =
      (![1,1,-1,-1,-1,-1,1,1,1,1,-1,-1,-1,-1,1,1] : Fin 16 → ℂ) k := by
  have hd : ∀ j : Fin 16, dot (encode 6) (encode j) =
      (![0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0] : Fin 16 → Bit) j := by decide
  rw [character,hd]
  fin_cases k <;> norm_num [bitSign]

theorem char_14 (k : Fin 16) :
    character (encode 14) (encode k) =
      (![1,1,-1,-1,-1,-1,1,1,-1,-1,1,1,1,1,-1,-1] : Fin 16 → ℂ) k := by
  have hd : ∀ j : Fin 16, dot (encode 14) (encode j) =
      (![0,0,1,1,1,1,0,0,1,1,0,0,0,0,1,1] : Fin 16 → Bit) j := by decide
  rw [character,hd]
  fin_cases k <;> norm_num [bitSign]

theorem raw_x0 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 8) (encode 0) 1 =
      u + (star u) - I*(u + (star u))*(v - (star v)) - 2*I*(u^2 - (star u)^2) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_0]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := ring_nf) (-2*I*u^2 + 2*I*((starRingEnd ℂ) u)^2) * _hv
theorem raw_y0 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 9) (encode 14) I =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_14]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := (ring_nf; norm_num)) (I*v - I*((starRingEnd ℂ) v)) * _hu + (I*u - I*((starRingEnd ℂ) u)) * _hv
theorem raw_z0 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 1) (encode 14) 1 =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_14]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  ring_nf
theorem raw_x1 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 12) (encode 0) 1 =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_0]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := (ring_nf; norm_num)) (u*v*((starRingEnd ℂ) v) + u*v + ((starRingEnd ℂ) u)*v*((starRingEnd ℂ) v) + ((starRingEnd ℂ) u)*((starRingEnd ℂ) v) - v - ((starRingEnd ℂ) v) - 2) * _hu + (2) * _hv
theorem raw_y1 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 13) (encode 6) I =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_6]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := (ring_nf; norm_num; ring)) (-u*v*((starRingEnd ℂ) v) + u*v - ((starRingEnd ℂ) u)*v*((starRingEnd ℂ) v) + ((starRingEnd ℂ) u)*((starRingEnd ℂ) v) + v + ((starRingEnd ℂ) v) - 2) * _hu + (2) * _hv
theorem raw_z1 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 1) (encode 6) 1 =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_6]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := ring_nf) (2*I*v - 2*I*((starRingEnd ℂ) v)) * _hu
theorem raw_x2 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 6) (encode 0) 1 =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_0]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := (ring_nf; norm_num; ring)) (u*v*((starRingEnd ℂ) v) + u*v + ((starRingEnd ℂ) u)*v*((starRingEnd ℂ) v) + ((starRingEnd ℂ) u)*((starRingEnd ℂ) v) - v - ((starRingEnd ℂ) v) - 2) * _hu + (2) * _hv
theorem raw_y2 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 7) (encode 2) I =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_2]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := (ring_nf; norm_num; ring)) (-u*v*((starRingEnd ℂ) v) + u*v - ((starRingEnd ℂ) u)*v*((starRingEnd ℂ) v) + ((starRingEnd ℂ) u)*((starRingEnd ℂ) v) + v + ((starRingEnd ℂ) v) - 2) * _hu + (2) * _hv
theorem raw_z2 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 1) (encode 2) 1 =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_2]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := ring_nf) (2*I*v - 2*I*((starRingEnd ℂ) v)) * _hu
theorem raw_x3 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 2) (encode 1) 1 =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_1]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := ring_nf) (I*v - I*((starRingEnd ℂ) v)) * _hu + (I*u - I*((starRingEnd ℂ) u)) * _hv
theorem raw_y3 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 3) (encode 1) I =
      u + (star u) - I*(u + (star u))*(v - (star v)) - 2*I*(u^2 - (star u)^2) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_1]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  linear_combination (norm := (ring_nf; norm_num; ring)) (-2*I*u^2 + 2*I*((starRingEnd ℂ) u)^2) * _hv
theorem raw_z3 (u v : ℂ)
    (_hu : star u * u = 1) (_hv : star v * v = 1) :
    pauliExpectation (phasePoly u v) (encode 1) (encode 0) 1 =
      u*v + (star u)*(star v) + I*(v - (star v)) := by
  unfold pauliExpectation
  rw [sum_bits4]
  simp only [encode_add, phasePoly_encode,char_0]
  simp only [Fin.sum_univ_succ]
  norm_num [table,star_mul,star_pow]
  simp only [Complex.star_def] at _hu _hv ⊢
  ring_nf

noncomputable def H (b δ : ℝ) : ℝ :=
  Real.cos b + 2 * Real.sin δ * Real.cos b + 4 * Real.sin b * Real.cos b
noncomputable def T (b δ : ℝ) : ℝ := Real.cos (b + δ) - Real.sin δ

noncomputable def phase (b δ : ℝ) : Bits 4 → ℂ :=
  phasePoly (anglePhase b) (anglePhase δ)

noncomputable def theta (b δ : ℝ) (z : Bits 4) : ℝ :=
  bMask (index z) * b + dMask (index z) * δ

lemma anglePhase_add (a b : ℝ) : anglePhase (a+b) = anglePhase a * anglePhase b := by
  simp only [anglePhase, Complex.ofReal_add, add_mul, Complex.exp_add]
lemma anglePhase_nat_mul (n : ℕ) (a : ℝ) : anglePhase (n*a) = anglePhase a ^ n := by
  simp only [anglePhase, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc,
    Complex.exp_nat_mul]

theorem phase_original (b δ : ℝ) (z : Bits 4) :
    phase b δ z = originalDiagonal z * anglePhase (theta b δ z) := by
  rw [phase,phasePoly_original,theta,anglePhase_add,anglePhase_nat_mul,anglePhase_nat_mul]
  ring

theorem phase_unit (b δ : ℝ) (z : Bits 4) : star (phase b δ z) * phase b δ z = 1 := by
  have hb : ‖originalDiagonal z‖ = 1 := by
    rw [originalDiagonal_eq_rawPhase_zero (by norm_num)]
    exact rawPhase_angle_norm 0 z
  have hm : ‖phase b δ z‖ = 1 := by
    rw [phase_original]
    simp [hb]
  simpa only [Complex.star_def,hm,one_pow,Complex.ofReal_one] using
    Complex.conj_mul' (phase b δ z)

lemma exceptional_trig (b δ : ℝ) :
    anglePhase b + star (anglePhase b) -
      I*(anglePhase b+star (anglePhase b))*(anglePhase δ-star (anglePhase δ)) -
      2*I*(anglePhase b^2-(star (anglePhase b))^2) = (2*H b δ : ℝ) := by
  simp only [anglePhase,Complex.exp_ofReal_mul_I,H]
  apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,pow_two]
  ring

lemma regular_trig (b δ : ℝ) :
    anglePhase b*anglePhase δ + star (anglePhase b)*star (anglePhase δ) +
      I*(anglePhase δ-star (anglePhase δ)) = (2*T b δ : ℝ) := by
  simp only [anglePhase,Complex.exp_ofReal_mul_I,T,Real.cos_add]
  apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im] <;> ring

lemma normFactor_four : normFactor 4 = (1/4 : ℂ) := by norm_num [normFactor]

/-- 实际门电路对三个单比特Pauli的精确拉回表。 -/
lemma pullback_X (ψ : Vec 4) (j : Fin 4) :
    localX (circuit ψ) j =
      pauliExpectation ψ (encode ((![8,12,6,2] : Fin 4 → Fin 16) j))
        (encode ((![0,0,0,1] : Fin 4 → Fin 16) j)) 1 := by
  have ha : ∀ k : Fin 4, setBit (difference (unitBit 4 k.val)) 3 0 =
      encode ((![8,12,6,2] : Fin 4 → Fin 16) k) := by decide
  have hb : ∀ k : Fin 4, setBit (0 : Bits 4) 3
      (coord (difference (unitBit 4 k.val)) 3) =
      encode ((![0,0,0,1] : Fin 4 → Fin 16) k) := by decide
  have h := CircuitPauli.localX_pullback (by norm_num : 0 < 4) j.val ψ
  rw [show 4-1=3 by decide,ha j,hb j] at h
  exact CircuitPauli.circuit_expectation (by norm_num) ψ _ _ _ _ _ _ h

lemma pullback_Y (ψ : Vec 4) (j : Fin 4) :
    localY (circuit ψ) j =
      pauliExpectation ψ (encode ((![9,13,7,3] : Fin 4 → Fin 16) j))
        (encode ((![14,6,2,1] : Fin 4 → Fin 16) j))
        (if j.val = 3 then -I else I) := by
  have ha : ∀ k : Fin 4, setBit (difference (unitBit 4 k.val)) 3 1 =
      encode ((![9,13,7,3] : Fin 4 → Fin 16) k) := by decide
  have hb : ∀ k : Fin 4, setBit (CircuitPauli.tailMask 4 k.val) 3
      (coord (difference (unitBit 4 k.val)) 3) =
      encode ((![14,6,2,1] : Fin 4 → Fin 16) k) := by decide
  have hc : ∀ k : Fin 4, coord (difference (unitBit 4 k.val)) 3 =
      if k.val = 3 then 1 else 0 := by decide
  have h := CircuitPauli.localY_pullback (by norm_num : 0 < 4) j.val j.isLt ψ
  rw [show 4-1=3 by decide,ha j,hb j,hc j] at h
  apply CircuitPauli.circuit_expectation (by norm_num) ψ _ _ _ _ _ _
  by_cases hj : j.val = 3
  · simpa [hj,bitSign] using h
  · simpa [hj,bitSign] using h

lemma pullback_Z (ψ : Vec 4) (j : Fin 4) :
    localZ (circuit ψ) j = pauliExpectation ψ (encode 1)
      (encode ((![14,6,2,0] : Fin 4 → Fin 16) j)) 1 := by
  have ha : unitBit 4 3 = encode 1 := by decide
  have hb : ∀ k : Fin 4, setBit (CircuitPauli.tailMask 4 k.val) 3 0 =
      encode ((![14,6,2,0] : Fin 4 → Fin 16) k) := by decide
  have h := CircuitPauli.localZ_table (by norm_num : 0 < 4) j.val j.isLt ψ
  rw [show 4-1=3 by decide,ha,hb j] at h
  exact CircuitPauli.circuit_expectation (by norm_num) ψ _ _ _ _ _ _ h

lemma normalized_raw (b δ : ℝ) (a B : Fin 16) (c : ℂ) (m : ℝ)
    (h : pauliExpectation (phase b δ) (encode a) (encode B) c = (2*m : ℝ)) :
    pauliExpectation (fun z => normFactor 4 * phase b δ z)
      (encode a) (encode B) c = (m/8 : ℝ) := by
  rw [pauliExpectation_scale,normFactor_four,h]
  push_cast
  norm_num
  ring

lemma raw_x0_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 8) (encode 0) 1 = (2*H b δ : ℝ) := by
  rw [phase,raw_x0 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact exceptional_trig b δ

lemma raw_y0_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 9) (encode 14) I = (2*T b δ : ℝ) := by
  rw [phase,raw_y0 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_z0_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 1) (encode 14) 1 = (2*T b δ : ℝ) := by
  rw [phase,raw_z0 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_x1_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 12) (encode 0) 1 = (2*T b δ : ℝ) := by
  rw [phase,raw_x1 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_y1_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 13) (encode 6) I = (2*T b δ : ℝ) := by
  rw [phase,raw_y1 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_z1_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 1) (encode 6) 1 = (2*T b δ : ℝ) := by
  rw [phase,raw_z1 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_x2_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 6) (encode 0) 1 = (2*T b δ : ℝ) := by
  rw [phase,raw_x2 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_y2_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 7) (encode 2) I = (2*T b δ : ℝ) := by
  rw [phase,raw_y2 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_z2_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 1) (encode 2) 1 = (2*T b δ : ℝ) := by
  rw [phase,raw_z2 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_x3_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 2) (encode 1) 1 = (2*T b δ : ℝ) := by
  rw [phase,raw_x3 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma raw_y3_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 3) (encode 1) I = (2*H b δ : ℝ) := by
  rw [phase,raw_y3 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact exceptional_trig b δ

lemma raw_z3_angle (b δ : ℝ) :
    pauliExpectation (phase b δ) (encode 1) (encode 0) 1 = (2*T b δ : ℝ) := by
  rw [phase,raw_z3 _ _ (anglePhase_star_mul b) (anglePhase_star_mul δ)]
  exact regular_trig b δ

lemma pauliExpectation_neg {n : ℕ} (f : Vec n) (a b : Bits n) (c : ℂ) :
    pauliExpectation f a b (-c) = -pauliExpectation f a b c := by
  simp [pauliExpectation,mul_neg,neg_mul,Finset.sum_neg_distrib]

lemma seed_X (b δ : ℝ) (hHT : H b δ = T b δ) (j : Fin 4) :
    localX (circuit (fun z => normFactor 4 * phase b δ z)) j = (T b δ/8 : ℝ) := by
  rw [pullback_X]
  fin_cases j
  · exact normalized_raw b δ 8 0 1 (T b δ) (by simpa only [hHT] using raw_x0_angle b δ)
  · exact normalized_raw b δ 12 0 1 (T b δ) (raw_x1_angle b δ)
  · exact normalized_raw b δ 6 0 1 (T b δ) (raw_x2_angle b δ)
  · exact normalized_raw b δ 2 1 1 (T b δ) (raw_x3_angle b δ)

lemma seed_Y (b δ : ℝ) (hHT : H b δ = T b δ) (j : Fin 4) :
    localY (circuit (fun z => normFactor 4 * phase b δ z)) j =
      if j.val = 3 then -((T b δ/8 : ℝ) : ℂ) else (T b δ/8 : ℝ) := by
  rw [pullback_Y]
  fin_cases j
  · exact normalized_raw b δ 9 14 I (T b δ) (raw_y0_angle b δ)
  · exact normalized_raw b δ 13 6 I (T b δ) (raw_y1_angle b δ)
  · exact normalized_raw b δ 7 2 I (T b δ) (raw_y2_angle b δ)
  · change pauliExpectation _ (encode 3) (encode 1) (-I) = -((T b δ/8 : ℝ) : ℂ)
    rw [pauliExpectation_neg]
    congr 1
    exact normalized_raw b δ 3 1 I (T b δ) (by simpa only [hHT] using raw_y3_angle b δ)

lemma seed_Z (b δ : ℝ) (j : Fin 4) :
    localZ (circuit (fun z => normFactor 4 * phase b δ z)) j = (T b δ/8 : ℝ) := by
  rw [pullback_Z]
  fin_cases j
  · exact normalized_raw b δ 1 14 1 (T b δ) (raw_z0_angle b δ)
  · exact normalized_raw b δ 1 6 1 (T b δ) (raw_z1_angle b δ)
  · exact normalized_raw b δ 1 2 1 (T b δ) (raw_z2_angle b δ)
  · exact normalized_raw b δ 1 0 1 (T b δ) (raw_z3_angle b δ)

/-- 曲线隐式方程只用于最后一步；此前全部期望都来自真实门电路有限和。 -/
theorem seed_components (b δ : ℝ) (hHT : H b δ = T b δ) (j : Fin 4) :
    localX (circuit (fun z => normFactor 4 * phase b δ z)) j = (T b δ/8 : ℝ) ∧
    localY (circuit (fun z => normFactor 4 * phase b δ z)) j =
      (if j.val = 3 then -((T b δ/8 : ℝ) : ℂ) else (T b δ/8 : ℝ)) ∧
    localZ (circuit (fun z => normFactor 4 * phase b δ z)) j = (T b δ/8 : ℝ) :=
  ⟨seed_X b δ hHT j,seed_Y b δ hHT j,seed_Z b δ j⟩

theorem phase_basepoint (z : Bits 4) : phase 0 0 z = originalDiagonal z := by
  rw [phase_original]
  simp [theta]

end UnifiedEJM.CurvedPhysical

