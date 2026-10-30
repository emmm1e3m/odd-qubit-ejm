import OddEJM.Core
import OddEJM.Character
import Mathlib.Tactic
namespace OddEJM
open scoped BigOperators

private theorem sign_sum {α : Type*} (s : Finset α) (f : α → Bit) :
    bitSign (∑ a ∈ s, f a) = ∏ a ∈ s, bitSign (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, bitSign_add, ih]

private theorem sqrt_two_pow (n : ℕ) : Real.sqrt ((2:ℝ)^n) = (Real.sqrt 2)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

theorem normFactor_eq_inv_sqrt_pow (n : ℕ) :
    normFactor n = ((Real.sqrt 2 : ℂ)⁻¹)^n := by
  unfold normFactor
  rw [sqrt_two_pow, Complex.ofReal_pow, inv_pow]

/-- 单比特Hadamard矩阵元的张量积，给出H的n次张量幂。 -/
noncomputable def tensorHadamardKernel {n : ℕ} (label z : Bits n) : ℂ :=
  ∏ j, (Real.sqrt 2 : ℂ)⁻¹ * bitSign (label j * z j)

theorem tensorHadamardKernel_eq_character {n : ℕ} (label z : Bits n) :
    tensorHadamardKernel label z = normFactor n * character label z := by
  unfold tensorHadamardKernel character dot
  rw [Finset.prod_mul_distrib, ← sign_sum]
  simp [normFactor_eq_inv_sqrt_pow]

noncomputable def tensorHadamard {n : ℕ} (ψ : Vec n) : Vec n :=
  fun z => ∑ label, tensorHadamardKernel label z * ψ label

def ket {n : ℕ} (label : Bits n) : Vec n := fun z => if z=label then 1 else 0

def phaseGate {n : ℕ} (u : Bits n → ℂ) (ψ : Vec n) : Vec n := fun z => u z * ψ z

/-- 计算基列逐振幅等于归一化Walsh字符。 -/
theorem tensorHadamard_ket {n : ℕ} (label : Bits n) :
    tensorHadamard (ket label) = fun z => normFactor n * character label z := by
  funext z
  simp [tensorHadamard, ket, tensorHadamardKernel_eq_character]

/-- 公共measurement定义逐振幅等于C_n D_t H^{⊗n}|label⟩。 -/
theorem measurement_eq_gate_column (n : ℕ) (t : ℝ) (label : Bits n) :
    measurement n t label =
      circuit (phaseGate (rawPhase (anglePhase t)) (tensorHadamard (ket label))) := by
  rw [tensorHadamard_ket]
  unfold measurement phaseGate
  congr 1
  funext z
  ring

end OddEJM
