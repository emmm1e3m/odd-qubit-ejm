import OddEJM.Quantum
import OddEJM.OriginalPhase
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open Complex

namespace UnifiedEJM.FiniteInvariants

abbrev State := Fin 16 → ℂ
abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

/-- 用真实振幅按12|34划分重排，不预设约化态公式。 -/
def reshape12 (v : State) : Mat :=
  !![v 0,v 1,v 2,v 3; v 4,v 5,v 6,v 7; v 8,v 9,v 10,v 11; v 12,v 13,v 14,v 15]

def reshape13 (v : State) : Mat :=
  !![v 0,v 1,v 4,v 5; v 2,v 3,v 6,v 7; v 8,v 9,v 12,v 13; v 10,v 11,v 14,v 15]

def reshape14 (v : State) : Mat :=
  !![v 0,v 2,v 4,v 6; v 1,v 3,v 5,v 7; v 8,v 10,v 12,v 14; v 9,v 11,v 13,v 15]

/-- 对补系统显式求和的真正二体约化密度矩阵。 -/
def reduced (A : Mat) : Mat := A * Aᴴ

def purity (A : Mat) : ℂ := Matrix.trace (reduced A * reduced A)

def sumPurity (v : State) : ℂ :=
  purity (reshape12 v) + purity (reshape13 v) + purity (reshape14 v)

/-- 未归一化原始相位表，x=e^(ia)。 -/
def phase159 (x : ℂ) : State :=
  ![1,x,x⁻¹,-I*x⁻¹,1,x,I,1,x⁻¹,x^2,1,-x,x^3,I*x^3,-I*x,-I]

/-- 末位Hadamard和原CNOT链产生的未归一化振幅表。 -/
def numerator159 (x : ℂ) : State :=
  ![x+1,x⁻¹+I*x⁻¹,1+I,1-x,x^3+I*x^3,-I*x+I,1-x,-x^2+x⁻¹,
    x^2+x⁻¹,x+1,-I*x-I,x^3-I*x^3,x+1,-1+I,x⁻¹-I*x⁻¹,1-x]

/-- 显式有限求和版本的原门序：先末位Hadamard，再后缀XOR。 -/
def gateNumerator (v : State) : State :=
  ![v 0+v 1,v 2-v 3,v 6+v 7,v 4-v 5,v 12+v 13,v 14-v 15,v 10+v 11,v 8-v 9,
    v 8+v 9,v 10-v 11,v 14+v 15,v 12-v 13,v 4+v 5,v 6-v 7,v 2+v 3,v 0-v 1]

theorem numerator159_eq_gates (x : ℂ) : numerator159 x = gateNumerator (phase159 x) := by
  ext i
  fin_cases i <;> simp [numerator159,gateNumerator,phase159] <;> ring

theorem star_eq_inv (x : ℂ) (hu : x * star x = 1) : star x = x⁻¹ := by
  exact eq_inv_of_mul_eq_one_right hu

/-- 最高位优先的四位解码。 -/
def decode4 (k : Fin 16) : OddEJM.Bits 4 :=
  ![((k.val / 8 : ℕ) : OddEJM.Bit),((k.val / 4 : ℕ) : OddEJM.Bit),
    ((k.val / 2 : ℕ) : OddEJM.Bit),(k.val : OddEJM.Bit)]

def encode4 (z : OddEJM.Bits 4) : Fin 16 :=
  ⟨8*(z 0).val + 4*(z 1).val + 2*(z 2).val + (z 3).val, by
    have h0 := (z 0).val_lt
    have h1 := (z 1).val_lt
    have h2 := (z 2).val_lt
    have h3 := (z 3).val_lt
    omega⟩

theorem encode_decode4 : ∀ k : Fin 16, encode4 (decode4 k) = k := by decide

theorem decode_encode4 : ∀ z : OddEJM.Bits 4, decode4 (encode4 z) = z := by decide

def decode4Equiv : Fin 16 ≃ OddEJM.Bits 4 where
  toFun := decode4
  invFun := encode4
  left_inv := encode_decode4
  right_inv := decode_encode4

def firstIndex : Fin 16 → Fin 16 :=
  ![0,2,6,4,12,14,10,8,8,10,14,12,4,6,2,0]

def secondIndex : Fin 16 → Fin 16 :=
  ![1,3,7,5,13,15,11,9,9,11,15,13,5,7,3,1]

theorem input0_checked : ∀ k : Fin 16,
    encode4 (OddEJM.setBit (OddEJM.difference (decode4 k)) 3 0) = firstIndex k := by decide

theorem input1_checked : ∀ k : Fin 16,
    encode4 (OddEJM.setBit (OddEJM.difference (decode4 k)) 3 1) = secondIndex k := by decide

theorem sign_checked : ∀ k : Fin 16,
    OddEJM.coord (OddEJM.difference (decode4 k)) 3 =
      if k.val % 2 = 0 then 0 else 1 := by decide

theorem gateNumerator_lookup (v : State) (k : Fin 16) :
    gateNumerator v k = v (firstIndex k) +
      (if k.val % 2 = 0 then 1 else -1) * v (secondIndex k) := by
  fin_cases k <;> simp [gateNumerator, firstIndex, secondIndex, sub_eq_add_neg]

/-- 显式振幅表的门序与旧库真实CNOT/Hadamard电路逐坐标相同。 -/
theorem gateNumerator_circuit (v : State) (k : Fin 16) :
    OddEJM.circuit (fun z => v (encode4 z)) (decode4 k) =
      (Real.sqrt 2 : ℂ)⁻¹ * gateNumerator v k := by
  change (Real.sqrt 2 : ℂ)⁻¹ *
    (v (encode4 (OddEJM.setBit (OddEJM.difference (decode4 k)) 3 0)) +
    OddEJM.bitSign (OddEJM.coord (OddEJM.difference (decode4 k)) 3) *
    v (encode4 (OddEJM.setBit (OddEJM.difference (decode4 k)) 3 1))) = _
  rw [input0_checked,input1_checked,sign_checked,gateNumerator_lookup]
  by_cases h : k.val % 2 = 0 <;> simp [h,OddEJM.bitSign]

end UnifiedEJM.FiniteInvariants

