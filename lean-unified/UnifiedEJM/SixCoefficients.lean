import UnifiedEJM.Core
import OddEJM.Finite
import OddEJM.WeightPhase
import Mathlib.Tactic

namespace UnifiedEJM.SixCertificate
open OddEJM
open scoped BigOperators
open Complex

/-- 六比特计算基字的最高位优先解码。 -/
def decode6 (k : ℕ) : Bits 6 :=
  ![((k/32:ℕ):Bit),((k/16:ℕ):Bit),((k/8:ℕ):Bit),((k/4:ℕ):Bit),((k/2:ℕ):Bit),(k:Bit)]

/-- 联合颜色编号00,01,10,11；AND支只读物理第2、4位。 -/
def colour (z : Bits 6) : Fin 4 :=
  ⟨2 * (if z 1 = 0 ∧ z 3 = 0 then 1 else 0) + (q z).val, by
    have h := (q z).val_lt
    split <;> omega⟩

/-- 18行依次为X1..X6,Y1..Y6,Z1..Z6，signed末位Y取反。 -/
def flipCode : Fin 18 → ℕ := ![32,48,24,12,6,2,33,49,25,13,7,3,1,1,1,1,1,1]
def charCode : Fin 18 → ℕ := ![32,48,24,12,6,3,31,47,23,11,5,2,63,31,15,7,3,1]
def gamma (p : Fin 18) : ℂ := if p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨
    p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 then -1 else -I

def coeff (p : Fin 18) (r s : Fin 4) : ℤ :=
  ∑ z : Bits 6, if colour z = r ∧ colour (z + decode6 (flipCode p)) = s
    then intSign (dot (decode6 (charCode p)) z) else 0

def matrixX : Fin 4 → Fin 4 → ℤ :=
  ![![-4,0,2,-2], ![0,4,2,-2], ![2,2,0,0], ![-2,-2,0,0]]
def matrixY : Fin 4 → Fin 4 → ℤ :=
  ![![-8,0,-4,0], ![0,8,0,4], ![-4,0,0,0], ![0,4,0,0]]
def matrixZ : Fin 4 → Fin 4 → ℤ :=
  ![![0,4,0,0], ![-4,0,0,0], ![0,0,0,-4], ![0,0,4,0]]
def expectedCoeff (p : Fin 18) : Fin 4 → Fin 4 → ℤ :=
  if p = 2 ∨ p = 3 then matrixX else if p = 8 then matrixY else
    if p = 5 ∨ p = 15 ∨ p = 16 then matrixZ else 0

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- 18个实际拉回掩码的64点整数颜色对证书，288项全部核查。 -/
theorem all_coefficients_checked : ∀ (p : Fin 18) (r s : Fin 4),
    coeff p r s = expectedCoeff p r s := by decide

end UnifiedEJM.SixCertificate

