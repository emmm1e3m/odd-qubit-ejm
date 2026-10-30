import OddEJM.Split
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace OddEJM
open scoped BigOperators
open Complex

/-- 对其余 n-1 个计算基指标求和的真实单比特偏迹。 -/
def reduced {n : ℕ} (ψ : Vec n) (j : Fin n) : Matrix Bit Bit ℂ :=
  Matrix.of fun a b => ∑ r : BitRest j, ψ (joinBit j a r) * star (ψ (joinBit j b r))

def sigmaX : Matrix Bit Bit ℂ := Matrix.of fun a b => if a = b then 0 else 1
def sigmaY : Matrix Bit Bit ℂ := Matrix.of fun a b =>
  if a = b then 0 else if a = 0 then -I else I
def sigmaZ : Matrix Bit Bit ℂ := Matrix.of fun a b =>
  if a = b then bitSign a else 0

def localX {n : ℕ} (ψ : Vec n) (j : Fin n) : ℂ :=
  pauliExpectation ψ (unitBit n j.val) 0 1

def localY {n : ℕ} (ψ : Vec n) (j : Fin n) : ℂ :=
  pauliExpectation ψ (unitBit n j.val) (unitBit n j.val) I

def localZ {n : ℕ} (ψ : Vec n) (j : Fin n) : ℂ :=
  pauliExpectation ψ 0 (unitBit n j.val) 1

@[simp] theorem joinBit_add_unit {n : ℕ} (j : Fin n) (b : Bit) (r : BitRest j) :
    joinBit j b r + unitBit n j.val = joinBit j (b + 1) r := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [unitBit]
  · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp [unitBit, hk, hv]

@[simp] theorem character_unit {n : ℕ} (j : Fin n) (z : Bits n) :
    character (unitBit n j.val) z = bitSign (z j) := by
  unfold character dot unitBit
  simp only [ite_mul, one_mul, zero_mul]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    have hv : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    simp [hv]
  · simp

@[simp] theorem character_zero_local {n : ℕ} (z : Bits n) :
    character (0 : Bits n) z = 1 := by simp [character, dot, bitSign]

/-- 偏迹保持全态内积给出的总迹。 -/
theorem reduced_trace {n : ℕ} (ψ : Vec n) (j : Fin n) :
    Matrix.trace (reduced ψ j) = inner ψ ψ := by
  unfold Matrix.trace
  rw [sum_bit]
  change reduced ψ j 0 0 + reduced ψ j 1 1 = inner ψ ψ
  simp only [inner, reduced, Matrix.of_apply]
  rw [sum_split_bit j]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- 偏迹逐矩阵元满足 Hermitian 共轭对称。 -/
theorem reduced_hermitian {n : ℕ} (ψ : Vec n) (j : Fin n) (a b : Bit) :
    star (reduced ψ j a b) = reduced ψ j b a := by
  simp only [reduced, Matrix.of_apply, star_sum, star_mul, star_star]

theorem localX_reduced {n : ℕ} (ψ : Vec n) (j : Fin n) :
    localX ψ j = reduced ψ j 0 1 + reduced ψ j 1 0 := by
  unfold localX pauliExpectation
  rw [sum_split_bit j]
  simp only [joinBit_add_unit, zero_add, character_zero_local, mul_one]
  have h11 : (1 : Bit) + 1 = 0 := by decide
  rw [h11]
  simp only [reduced, Matrix.of_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem localY_reduced {n : ℕ} (ψ : Vec n) (j : Fin n) :
    localY ψ j = I * reduced ψ j 0 1 - I * reduced ψ j 1 0 := by
  unfold localY pauliExpectation
  rw [sum_split_bit j]
  simp only [joinBit_add_unit, zero_add, character_unit, joinBit_self]
  have h11 : (1 : Bit) + 1 = 0 := by decide
  rw [h11]
  simp only [bitSign, eq_self, ite_true, one_ne_zero, ite_false, mul_one, mul_neg_one]
  simp only [reduced, Matrix.of_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem localZ_reduced {n : ℕ} (ψ : Vec n) (j : Fin n) :
    localZ ψ j = reduced ψ j 0 0 - reduced ψ j 1 1 := by
  unfold localZ pauliExpectation
  rw [sum_split_bit j]
  simp only [add_zero, character_unit, joinBit_self]
  simp only [bitSign, eq_self, ite_true, one_ne_zero, ite_false, mul_one, mul_neg_one]
  simp only [reduced, Matrix.of_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Pauli-X 的约化态迹期望等于全态期望。 -/
theorem reduced_trace_sigmaX {n : ℕ} (ψ : Vec n) (j : Fin n) :
    Matrix.trace (reduced ψ j * sigmaX) = localX ψ j := by
  rw [localX_reduced]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sum_bit, sigmaX, Matrix.of_apply]

/-- Pauli-Y 的约化态迹期望等于全态期望。 -/
theorem reduced_trace_sigmaY {n : ℕ} (ψ : Vec n) (j : Fin n) :
    Matrix.trace (reduced ψ j * sigmaY) = localY ψ j := by
  rw [localY_reduced]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sum_bit, sigmaY, Matrix.of_apply]
  ring

/-- Pauli-Z 的约化态迹期望等于全态期望。 -/
theorem reduced_trace_sigmaZ {n : ℕ} (ψ : Vec n) (j : Fin n) :
    Matrix.trace (reduced ψ j * sigmaZ) = localZ ψ j := by
  rw [localZ_reduced]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sum_bit, sigmaZ, bitSign, Matrix.of_apply]
  ring

/-- 未归一化 Bloch 矩阵；系数稍后由真实期望定理给出。 -/
noncomputable def blochMatrix (w x y z : ℂ) : Matrix Bit Bit ℂ :=
  Matrix.of fun a b => if a = 0 then
    (if b = 0 then (w + z) / 2 else (x - I * y) / 2)
  else (if b = 0 then (x + I * y) / 2 else (w - z) / 2)

/-- 单比特矩阵的 Pauli 基展开。 -/
theorem blochMatrix_pauli (w x y z : ℂ) :
    blochMatrix w x y z =
      (1 / 2 : ℂ) • (w • (1 : Matrix Bit Bit ℂ) +
        x • sigmaX + y • sigmaY + z • sigmaZ) := by
  ext a b
  have cases₂ (b : Bit) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
    simp [Matrix.of_apply, blochMatrix, sigmaX, sigmaY, sigmaZ, bitSign, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- 真实偏迹等于由真实 Pauli 期望构成的 Bloch 矩阵。 -/
theorem reduced_bloch {n : ℕ} (ψ : Vec n) (j : Fin n) :
    reduced ψ j = blochMatrix (inner ψ ψ) (localX ψ j) (localY ψ j) (localZ ψ j) := by
  have ht : reduced ψ j 0 0 + reduced ψ j 1 1 = inner ψ ψ := by
    simpa only [Matrix.trace, sum_bit, Matrix.diag_apply] using reduced_trace ψ j
  rw [localX_reduced, localY_reduced, localZ_reduced, ← ht]
  ext a b
  have cases₂ (b : Bit) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;> simp [Matrix.of_apply, blochMatrix] <;> try ring_nf
  all_goals try simp [I_sq]
  all_goals ring

/-- 原始有限和定义下的密度矩阵 Pauli 展开，不把目标式当作定义。 -/
theorem reduced_pauli {n : ℕ} (ψ : Vec n) (j : Fin n) :
    reduced ψ j = (1 / 2 : ℂ) •
      (inner ψ ψ • (1 : Matrix Bit Bit ℂ) + localX ψ j • sigmaX +
       localY ψ j • sigmaY + localZ ψ j • sigmaZ) := by
  rw [reduced_bloch, blochMatrix_pauli]

/-- 接入已经证明的归一化与三分量后，得到实际偏迹公式。 -/
theorem reduced_of_components {n : ℕ} (ψ : Vec n) (j : Fin n) (x y z : ℂ)
    (hnorm : inner ψ ψ = 1) (hx : localX ψ j = x)
    (hy : localY ψ j = y) (hz : localZ ψ j = z) :
    reduced ψ j = blochMatrix 1 x y z := by
  rw [reduced_bloch, hnorm, hx, hy, hz]

/-- Bloch 矩阵的迹平方，允许非归一化复系数。 -/
theorem blochMatrix_purity (w x y z : ℂ) :
    Matrix.trace (blochMatrix w x y z * blochMatrix w x y z) =
      (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) / 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sum_bit]
  simp [Matrix.of_apply, blochMatrix]
  ring_nf
  simp [I_sq]
  ring

/-- 归一化真实偏迹的纯度由三个实际 Pauli 期望决定。 -/
theorem reduced_purity {n : ℕ} (ψ : Vec n) (j : Fin n)
    (hnorm : inner ψ ψ = 1) :
    Matrix.trace (reduced ψ j * reduced ψ j) =
      (1 + (localX ψ j) ^ 2 + (localY ψ j) ^ 2 + (localZ ψ j) ^ 2) / 2 := by
  rw [reduced_bloch, blochMatrix_purity, hnorm]
  simp

/-- 已证归一化和径向分量接入任意固定方向，包含四面体顶点。 -/
theorem reduced_radial {n : ℕ} (ψ : Vec n) (j : Fin n) (r : ℂ) (v : Fin 3 → ℂ)
    (hnorm : inner ψ ψ = 1)
    (hx : localX ψ j = r * v 0) (hy : localY ψ j = r * v 1)
    (hz : localZ ψ j = r * v 2) :
    reduced ψ j = (1 / 2 : ℂ) • ((1 : Matrix Bit Bit ℂ) +
      r • (v 0 • sigmaX + v 1 • sigmaY + v 2 • sigmaZ)) := by
  rw [reduced_pauli, hnorm, hx, hy, hz]
  simp only [one_smul, smul_add, mul_smul, add_assoc]

/-- 当方向长度为一，真实偏迹的纯度恰为 (1+r²)/2。 -/
theorem reduced_purity_radial {n : ℕ} (ψ : Vec n) (j : Fin n) (r : ℂ)
    (v : Fin 3 → ℂ) (hnorm : inner ψ ψ = 1)
    (hx : localX ψ j = r * v 0) (hy : localY ψ j = r * v 1)
    (hz : localZ ψ j = r * v 2)
    (hv : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1) :
    Matrix.trace (reduced ψ j * reduced ψ j) = (1 + r ^ 2) / 2 := by
  rw [reduced_purity ψ j hnorm, hx, hy, hz]
  calc
    _ = (1 + r ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2)) / 2 := by ring
    _ = (1 + r ^ 2) / 2 := by rw [hv]; ring

end OddEJM
