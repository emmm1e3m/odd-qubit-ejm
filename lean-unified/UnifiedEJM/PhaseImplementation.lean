import UnifiedEJM.Phase
import UnifiedEJM.Features
import OddEJM.Tensor
import Mathlib.Tactic

noncomputable section
namespace UnifiedEJM.PhaseImplementation
open OddEJM Complex
open scoped BigOperators

/-- 完整相位中的物理全零串条件门。 -/
def zeroStringPhase {n : ℕ} (t : ℝ) (z : Bits n) : ℂ :=
  if z = 0 then anglePhase (Real.pi / 2 - t) else 1

theorem anglePhase_sub (s t : ℝ) :
    anglePhase (s - t) = anglePhase s / anglePhase t := by
  simp only [anglePhase, Complex.ofReal_sub, sub_mul, Complex.exp_sub]

theorem anglePhase_half_pi : anglePhase (Real.pi / 2) = I := by
  simp [anglePhase]

theorem anglePhase_neg_half_pi : anglePhase (-Real.pi / 2) = -I := by
  simp [anglePhase]

/-- 不省略物理零串修正的逐输入门分解。 -/
theorem rawPhase_factorization {n : ℕ} (t : ℝ) (z : Bits n) :
    UnifiedEJM.rawPhase (anglePhase t) z =
      -I * I ^ weight z * (anglePhase t) ^ (UnifiedEJM.q z).val *
        zeroStringPhase t z := by
  by_cases hz : z = 0
  · subst z
    rw [zeroStringPhase, ite_eq_left rfl, anglePhase_sub, anglePhase_half_pi]
    have hu : anglePhase t ≠ 0 := Complex.exp_ne_zero _
    simp only [UnifiedEJM.rawPhase_zero, weight, Pi.zero_apply, ZMod.val_zero,
      Finset.sum_const_zero, pow_zero, UnifiedEJM.q_zero,
      ZMod.val_one_eq_one_mod, Nat.one_mod, pow_one, mul_one]
    field_simp
    simp
  · simp [UnifiedEJM.rawPhase, zeroStringPhase, hz]

/-- 因式分解作用于任意输入态，故不只是一列的恒等式。 -/
theorem phaseGate_factorization {n : ℕ} (t : ℝ) (ψ : Vec n) :
    phaseGate (UnifiedEJM.rawPhase (anglePhase t)) ψ =
      fun z => -I * I ^ weight z *
        (phaseGate (fun w => (anglePhase t) ^ (UnifiedEJM.q w).val)
          (phaseGate (zeroStringPhase t) ψ)) z := by
  funext z
  simp only [phaseGate, rawPhase_factorization]
  ring

/-- 零半径端点中全零条件相位恰好消失。 -/
theorem zeroStringPhase_plus {n : ℕ} (z : Bits n) :
    zeroStringPhase (Real.pi / 2) z = 1 := by
  simp [zeroStringPhase]

/-- 增强端点保留全零串符号反射。 -/
theorem zeroStringPhase_minus {n : ℕ} (z : Bits n) :
    zeroStringPhase (-Real.pi / 2) z = if z = 0 then -1 else 1 := by
  have h : Real.pi / 2 - -Real.pi / 2 = Real.pi := by ring
  simp [zeroStringPhase, h, anglePhase, Complex.exp_ofReal_mul_I]

theorem rawPhase_plus {n : ℕ} (z : Bits n) :
    UnifiedEJM.rawPhase (anglePhase (Real.pi / 2)) z =
      -I * I ^ weight z * I ^ (UnifiedEJM.q z).val := by
  rw [rawPhase_factorization, zeroStringPhase_plus, anglePhase_half_pi, mul_one]

theorem rawPhase_minus {n : ℕ} (z : Bits n) :
    UnifiedEJM.rawPhase (anglePhase (-Real.pi / 2)) z =
      -I * I ^ weight z * (-I) ^ (UnifiedEJM.q z).val *
        (if z = 0 then -1 else 1) := by
  rw [rawPhase_factorization, zeroStringPhase_minus, anglePhase_neg_half_pi]

/-- 四特征核的模四多线性表达，与布尔核逐输入一致。 -/
def kernelPolynomial (v : Bits 4) : ZMod 4 :=
  let x : ZMod 4 := (v 0).val
  let b : ZMod 4 := (v 1).val
  let c : ZMod 4 := (v 2).val
  let s : ZMod 4 := (v 3).val
  1 + 3*x + 3*b + 2*x*b + x*c + b*c + 2*x*b*c +
    3*s + x*s + 2*b*s + 2*x*b*s + 3*b*c*s

theorem kernelPolynomial_eq : ∀ v : Bits 4,
    kernelPolynomial v = ((UnifiedEJM.F v).val : ZMod 4) := by decide

/-- 模四相位的标准复数实现。 -/
def root4 (a : ZMod 4) : ℂ := I ^ a.val

theorem root4_add (a b : ZMod 4) : root4 (a+b) = root4 a * root4 b := by
  unfold root4
  rw [ZMod.val_add, ← pow_eq_pow_mod (a.val + b.val) Complex.I_pow_four, pow_add]

@[simp] theorem root4_zero : root4 0 = 1 := by change I^0=1; simp
@[simp] theorem root4_one : root4 1 = I := by change I^1=I; simp
@[simp] theorem root4_two : root4 2 = -1 := by change I^2 = -1; exact Complex.I_sq
@[simp] theorem root4_neg_one : root4 (-1) = -I := by
  change I^3 = -I
  exact Complex.I_pow_three

theorem root4_nat (m : ℕ) : root4 (m : ZMod 4) = I ^ m := by
  unfold root4
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m Complex.I_pow_four]

theorem root4_neg (a : ZMod 4) : root4 (-a) = star (root4 a) := by
  fin_cases a
  · change I^0 = star (I^0)
    simp
  · change I^3 = star (I^1)
    simp [Complex.I_pow_three]
  · change I^2 = star (I^2)
    simp [Complex.I_sq]
  · change I^1 = star (I^3)
    simp [Complex.I_pow_three]

theorem root4_neg_nat (m : ℕ) : root4 (-(m : ZMod 4)) = (-I)^m := by
  rw [root4_neg, root4_nat, star_pow]
  simp

/-- 单比特相位层的模四指数。 -/
def weightPhase {n : ℕ} (z : Bits n) : ZMod 4 := (weight z : ZMod 4) - 1

/-- 唯一物理零串的模四指示。 -/
def zeroIndicator {n : ℕ} (z : Bits n) : ZMod 4 := if z = 0 then 1 else 0

/-- 仅四特征背景的模四相位指数。 -/
def kernelPhase {n : ℕ} (z : Bits n) : ZMod 4 := (UnifiedEJM.q z).val

def referenceExponent {n : ℕ} (z : Bits n) : ZMod 4 := weightPhase z + zeroIndicator z
def plusExponent {n : ℕ} (z : Bits n) : ZMod 4 := weightPhase z + kernelPhase z
def minusExponent {n : ℕ} (z : Bits n) : ZMod 4 :=
  weightPhase z - kernelPhase z + 2 * zeroIndicator z

theorem kernelPhase_eq_polynomial {n : ℕ} (z : Bits n) :
    kernelPhase z = kernelPolynomial (features z) := by
  rw [kernelPolynomial_eq]
  rfl

theorem root4_weightPhase {n : ℕ} (z : Bits n) :
    root4 (weightPhase z) = -I * I ^ weight z := by
  rw [weightPhase, sub_eq_add_neg, root4_add, root4_nat, root4_neg_one]
  ring

/-- 原相位的逐输入模四指数桥。 -/
theorem reference_phase_exponent {n : ℕ} (z : Bits n) :
    UnifiedEJM.rawPhase (anglePhase 0) z = root4 (referenceExponent z) := by
  by_cases hz : z = 0
  · subst z
    simp [referenceExponent, weightPhase, zeroIndicator, weight]
  · rw [referenceExponent, root4_add, root4_weightPhase]
    simp [UnifiedEJM.rawPhase, hz, zeroIndicator]

theorem plus_phase_exponent {n : ℕ} (z : Bits n) :
    UnifiedEJM.rawPhase (anglePhase (Real.pi/2)) z = root4 (plusExponent z) := by
  rw [rawPhase_plus, plusExponent, root4_add, root4_weightPhase]
  simp only [kernelPhase, root4_nat]

theorem minus_phase_exponent {n : ℕ} (z : Bits n) :
    UnifiedEJM.rawPhase (anglePhase (-Real.pi/2)) z = root4 (minusExponent z) := by
  rw [rawPhase_minus, minusExponent, sub_eq_add_neg, root4_add, root4_add,
    root4_weightPhase]
  simp only [kernelPhase, root4_neg_nat]
  by_cases hz : z = 0 <;> simp [zeroIndicator, hz]

theorem zeroStringPhase_eq_exp {n : ℕ} (t : ℝ) (z : Bits n) :
    zeroStringPhase t z =
      Complex.exp (((Real.pi / 2 - t : ℝ) : ℂ) * I * deltaZero z) := by
  by_cases hz : z = 0 <;> simp [zeroStringPhase, deltaZero, hz, anglePhase]

/-- 单比特P门的张量积逐振幅给出i的Hamming重量次幂。 -/
theorem weight_tensor_phase {n : ℕ} (z : Bits n) :
    (∏ j : Fin n, I ^ (z j).val) = I ^ weight z := by
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun j => (z j).val) I

/-- 全参数门分解的指数与单比特张量积写法。 -/
theorem rawPhase_exponential_factorization {n : ℕ} (t : ℝ) (z : Bits n) :
    UnifiedEJM.rawPhase (anglePhase t) z =
      -I * (∏ j : Fin n, I ^ (z j).val) *
        Complex.exp (((t * ((UnifiedEJM.q z).val : ℝ) : ℝ) : ℂ) * I) *
        Complex.exp (((Real.pi / 2 - t : ℝ) : ℂ) * I * deltaZero z) := by
  rw [weight_tensor_phase, rawPhase_factorization,
    UnifiedEJM.anglePhase_bit, zeroStringPhase_eq_exp]

/-- 数据寄存器和四个辅助比特上的实际复振幅。 -/
abbrev EncodedVec (n : ℕ) := Bits n → Bits 4 → ℂ

def appendZero {n : ℕ} (ψ : Vec n) : EncodedVec n :=
  fun z a => if a = 0 then ψ z else 0

/-- 可逆四奇偶校验编码：辅助寄存器异或四个真实特征。 -/
def parityEncode {n : ℕ} (ψ : EncodedVec n) : EncodedVec n :=
  fun z a => ψ z (a + features z)

def fourCoreGate {n : ℕ} (u : ℂ) (ψ : EncodedVec n) : EncodedVec n :=
  fun z a => u ^ (UnifiedEJM.F a).val * ψ z a

theorem parityEncode_involutive {n : ℕ} (ψ : EncodedVec n) :
    parityEncode (parityEncode ψ) = ψ := by
  funext z a
  simp only [parityEncode, add_assoc, bits_add_self, add_zero]

/-- 计算、四比特核、反算后辅助位回零，数据实现完整背景核相位。 -/
theorem compute_core_uncompute {n : ℕ} (u : ℂ) (ψ : Vec n) :
    parityEncode (fourCoreGate u (parityEncode (appendZero ψ))) =
      appendZero (phaseGate (fun z => u ^ (UnifiedEJM.q z).val) ψ) := by
  funext z a
  simp only [parityEncode, fourCoreGate, appendZero, add_assoc,
    bits_add_self, add_zero, phaseGate]
  by_cases ha : a = 0
  · subst a
    simp only [zero_add, ite_true]
    rfl
  · simp [ha]

private def basisTerm {n : ℕ} (z : Bits n) (j : Fin n) : Bits n :=
  fun k => if k = j then z j else 0

private theorem basisTerm_eq {n : ℕ} (z : Bits n) (j : Fin n) :
    basisTerm z j = if z j = 0 then 0 else unitBit n j.val := by
  rcases bit_cases (z j) with h | h
  · funext k
    simp [basisTerm, h]
  · funext k
    simp [basisTerm, h, unitBit, Fin.ext_iff]

private theorem bits_expand {n : ℕ} (z : Bits n) :
    z = ∑ j : Fin n, basisTerm z j := by
  funext k
  simp [basisTerm, Finset.sum_apply]

/-- 四特征逐输出位等于输入位的线性校验矩阵。 -/
theorem features_linear_expansion {n : ℕ} (z : Bits n) (k : Fin 4) :
    features z k = ∑ j : Fin n, features (unitBit n j.val) k * z j := by
  have h := congrArg (featuresHom n) (bits_expand z)
  rw [map_sum] at h
  change features z = ∑ j : Fin n, (featuresHom n) (basisTerm z j) at h
  rw [h, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [basisTerm_eq]
  rcases bit_cases (z j) with hj | hj <;> simp [hj] <;> rfl

/-- 数据位j控制辅助位k的真正二进制CNOT。 -/
def auxiliaryCNOT {n : ℕ} (j : Fin n) (k : Fin 4)
    (z : Bits n) (a : Bits 4) : Bits 4 :=
  fun l => if l = k then a l + z j else a l

def checkContribution {n : ℕ} (z : Bits n) (p : Fin n × Fin 4) : Bits 4 :=
  fun l => if l = p.2 then features (unitBit n p.1.val) p.2 * z p.1 else 0

/-- 线性校验矩阵中零系数省去门，非零系数执行一个CNOT。 -/
def checkGate {n : ℕ} (z : Bits n) (p : Fin n × Fin 4) (a : Bits 4) : Bits 4 :=
  if features (unitBit n p.1.val) p.2 = 0 then a
  else auxiliaryCNOT p.1 p.2 z a

theorem checkGate_eq_add {n : ℕ} (z : Bits n) (p : Fin n × Fin 4) (a : Bits 4) :
    checkGate z p a = a + checkContribution z p := by
  rcases bit_cases (features (unitBit n p.1.val) p.2) with h | h
  · funext l
    simp [checkGate, checkContribution, h]
  · funext l
    by_cases hl : l = p.2 <;> simp [checkGate, auxiliaryCNOT, checkContribution, h, hl]

def checkCircuit {n : ℕ} (z : Bits n) : List (Fin n × Fin 4) → Bits 4 → Bits 4
  | [], a => a
  | p :: ps, a => checkCircuit z ps (checkGate z p a)

theorem checkCircuit_eq_sum {n : ℕ} (z : Bits n)
    (ps : List (Fin n × Fin 4)) (a : Bits 4) :
    checkCircuit z ps a = a + (ps.map (checkContribution z)).sum := by
  induction ps generalizing a with
  | nil => simp [checkCircuit]
  | cons p ps ih => simp [checkCircuit, ih, checkGate_eq_add, add_assoc]

theorem checkContributions_sum {n : ℕ} (z : Bits n) :
    (∑ p : Fin n × Fin 4, checkContribution z p) = features z := by
  funext l
  simp only [Finset.sum_apply, Fintype.sum_prod_type]
  simpa [checkContribution] using (features_linear_expansion z l).symm

/-- 至多4n个CNOT槽实现四奇偶校验，允许省略零系数槽。 -/
theorem checkCircuit_realizes_features {n : ℕ} (z : Bits n) (a : Bits 4) :
    checkCircuit z (Finset.univ.toList : List (Fin n × Fin 4)) a = a + features z := by
  rw [checkCircuit_eq_sum]
  congr 1
  simpa using checkContributions_sum z

theorem checkCircuit_slot_count (n : ℕ) :
    (Finset.univ.toList : List (Fin n × Fin 4)).length = 4*n := by
  simp [mul_comm]

/-- 把已证明的经典基置换提升为实际复振幅上的CNOT电路。 -/
theorem parityEncode_eq_CNOT_circuit {n : ℕ} (ψ : EncodedVec n) :
    parityEncode ψ = fun z a =>
      ψ z (checkCircuit z (Finset.univ.toList : List (Fin n × Fin 4)) a) := by
  funext z a
  rw [checkCircuit_realizes_features]
  rfl

end UnifiedEJM.PhaseImplementation
