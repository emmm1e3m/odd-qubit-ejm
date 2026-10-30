import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Trigonometric

/-!
# 任意奇数比特 EJM 的公共定义

物理位采用零基编号。所有态均为计算基上的实际复振幅函数，
期望采用显式有限和。这里仅放定义与基础恒等式，不把物理结论作为假设。
-/

namespace OddEJM

open scoped BigOperators
open Complex

abbrev Bit := ZMod 2
abbrev Bits (n : ℕ) := Fin n → Bit
abbrev Vec (n : ℕ) := Bits n → ℂ

def bitSign (b : Bit) : ℂ := if b = 0 then 1 else -1

def dot {n : ℕ} (x y : Bits n) : Bit := ∑ j, x j * y j

def character {n : ℕ} (k z : Bits n) : ℂ := bitSign (dot k z)

def walsh {n : ℕ} (q : Bits n → Bit) (k : Bits n) : ℂ :=
  ∑ z, bitSign (q z + dot k z)

def derivative {n : ℕ} (q : Bits n → Bit) (a z : Bits n) : Bit :=
  q z + q (z + a)

def weight {n : ℕ} (z : Bits n) : ℕ := ∑ j, (z j).val

/-- 越界坐标补零，避免端点公式反复携带下标证明。 -/
def coord {n : ℕ} (z : Bits n) (j : ℕ) : Bit :=
  if hj : j < n then z ⟨j, hj⟩ else 0

def setBit {n : ℕ} (z : Bits n) (j : ℕ) (b : Bit) : Bits n :=
  fun k => if k.val = j then b else z k

def unitBit (n j : ℕ) : Bits n := fun k => if k.val = j then 1 else 0

/-- 中间偶、奇物理位；零基编号下奇偶性互换。 -/
def blockParity {n : ℕ} (z : Bits n) (p : ℕ) : Bit :=
  ∑ j : Fin n, if 1 ≤ j.val ∧ j.val < n - 2 ∧ j.val % 2 = p then z j else 0

def compress {n : ℕ} (z : Bits n) : Bits 5 :=
  ![coord z 0, blockParity z 1, blockParity z 0, coord z (n - 2), coord z (n - 1)]

/-- 固定五位布尔函数，变量顺序为首位、偶内块、奇内块、倒数第二位、末位。 -/
def Q (v : Bits 5) : Bit :=
  1 + v 0 + v 1 + v 2 + v 3 + v 4 +
    v 3 * v 4 + v 1 * v 4 + v 1 * v 3 + v 0 * v 4 + v 0 * v 1 * v 4

def phaseSupport {n : ℕ} (z : Bits n) : Bit :=
  if z = 0 then 0 else Q (compress z)

def deltaZero {n : ℕ} (z : Bits n) : ℂ := if z = 0 then 1 else 0

def background {n : ℕ} (u : ℂ) (z : Bits n) : ℂ :=
  I ^ weight z * u ^ (Q (compress z)).val

def corrected {n : ℕ} (u : ℂ) (z : Bits n) : ℂ :=
  background u z + (I - u) * deltaZero z

/-- 原相位逐振幅正规形：物理零串振幅为一。 -/
def rawPhase {n : ℕ} (u : ℂ) (z : Bits n) : ℂ :=
  if z = 0 then 1 else -I * I ^ weight z * u ^ (Q (compress z)).val

noncomputable def anglePhase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * I)

noncomputable def normFactor (n : ℕ) : ℂ :=
  ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)⁻¹

def inner {n : ℕ} (ψ φ : Vec n) : ℂ := ∑ z, star (ψ z) * φ z

def pauliAction {n : ℕ} (a b : Bits n) (c : ℂ) (ψ : Vec n) : Vec n :=
  fun z => c * character b (z + a) * ψ (z + a)

/-- 对应 ket 作用 `|z⟩ ↦ c (-1)^(b·z) |z+a⟩`。 -/
def pauliExpectation {n : ℕ} (ψ : Vec n) (a b : Bits n) (c : ℂ) : ℂ :=
  ∑ z, star (ψ (z + a)) * c * character b z * ψ z

def suffix {n : ℕ} (z : Bits n) : Bits n :=
  fun j => ∑ k : Fin n, if j ≤ k then z k else 0

def difference {n : ℕ} (z : Bits n) : Bits n :=
  fun j => z j + coord z (j.val + 1)

def chain {n : ℕ} (ψ : Vec n) : Vec n := fun z => ψ (difference z)

noncomputable def hadamardAt {n : ℕ} (j : ℕ) (ψ : Vec n) : Vec n :=
  fun z => (Real.sqrt 2 : ℂ)⁻¹ *
    (ψ (setBit z j 0) + bitSign (coord z j) * ψ (setBit z j 1))

noncomputable def circuit {n : ℕ} (ψ : Vec n) : Vec n :=
  chain (hadamardAt (n - 1) ψ)

noncomputable def seed (n : ℕ) (t : ℝ) : Vec n :=
  circuit (fun z => normFactor n * rawPhase (anglePhase t) z)

/-- 所有输入字符列；后续须证明它们与指定 Pauli 轨道逐态一致。 -/
noncomputable def measurement (n : ℕ) (t : ℝ) (label : Bits n) : Vec n :=
  circuit (fun z => normFactor n * rawPhase (anglePhase t) z * character label z)

noncomputable def componentScale (n : ℕ) (t : ℝ) : ℝ :=
  (1 - Real.sin t) / (2 : ℝ) ^ (n - 1)

noncomputable def radius (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt 3 * componentScale n t

end OddEJM

