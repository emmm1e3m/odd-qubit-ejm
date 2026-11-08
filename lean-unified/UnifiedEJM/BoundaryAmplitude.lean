import UnifiedEJM.BoundaryFeatures
import UnifiedEJM.PhysicsFinite

open OddEJM OddEJM.CircuitPauli Complex
open UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.BoundaryAmplitude

/-- 输出路径差分上的公共相位；末位已固定为零。 -/
def pathPhase {n : ℕ} (y : Bits n) : ℂ :=
  -I * I ^ weight (inputBranch y 0)

/-- 两条Hadamard支路只有末位的权重不同。 -/
theorem weight_inputBranch {n : ℕ} (hn : 0 < n) (y : Bits n) (b : Bit) :
    weight (inputBranch y b) = weight (inputBranch y 0) + b.val := by
  have ht (j : Fin n) : (inputBranch y b j).val =
      (inputBranch y 0 j).val + if j.val = n-1 then b.val else 0 := by
    by_cases hj : j.val = n-1 <;> simp [inputBranch, setBit, hj]
  simp only [weight, ht, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (⟨n-1, by omega⟩ : Fin n)]
  · simp
  · intro j _ hj
    have hne : j.val ≠ n-1 := fun he => hj (Fin.ext he)
    simp [hne]
  · simp

theorem inputBranch_one_ne_zero {n : ℕ} (hn : 0 < n) (y : Bits n) :
    inputBranch y 1 ≠ 0 := by
  intro h
  have he := congrFun h (⟨n-1, by omega⟩ : Fin n)
  norm_num [inputBranch, setBit] at he

theorem difference_last {n : ℕ} (hn : 0 < n) (y : Bits n) :
    coord (difference y) (n-1) = coord y (n-1) := by
  simp [coord, difference, show n-1 < n by omega, show ¬n-1+1 < n by omega]

/-- 分支零当且仅当输出为常量串；缺陷保留两个物理端点。 -/
theorem inputBranch_zero_iff_constant {n : ℕ} (hn : 0 < n) (y : Bits n) :
    inputBranch y 0 = 0 ↔ ∀ j, y j = coord y 0 := by
  constructor
  · intro h
    have hd : difference y = difference (fun _ : Fin n => coord y (n-1)) := by
      rw [difference_const hn]
      ext j
      by_cases hj : j.val = n-1
      · have heq : j = (⟨n-1, by omega⟩ : Fin n) := Fin.ext hj
        rw [heq]
        simp [difference, coord, show n-1 < n by omega, show ¬ n-1+1 < n by omega]
      · have hjz := congrFun h j
        simpa [inputBranch, setBit, hj] using hjz
    have hy := (differenceEquiv n).injective hd
    have h0 := congrFun hy (⟨0, hn⟩ : Fin n)
    intro j
    have hj := congrFun hy j
    simpa [coord, hn] using hj.trans h0.symm
  · intro h
    have hy : y = fun _ : Fin n => coord y 0 := funext h
    rw [hy, inputBranch, difference_const hn]
    ext j
    by_cases hj : j.val = n-1 <;> simp [setBit, hj]

/-- 无参数模长假设的实际电路振幅恒等式。 -/
theorem actual_seed_two_branch {n : ℕ} (hn : 0 < n) (u : ℂ) (y : Bits n) :
    Physical.seed (UnifiedEJM.rawPhase u) y = scale n * pathPhase y *
      (u ^ (UnifiedEJM.q (inputBranch y 0)).val +
        I * bitSign (coord y (n-1)) * u ^ (UnifiedEJM.q (inputBranch y 1)).val +
        (I-u) * (if inputBranch y 0 = 0 then 1 else 0)) := by
  have h1 := inputBranch_one_ne_zero hn y
  have hw := weight_inputBranch hn y (1 : Bit)
  norm_num only [ZMod.val_one_eq_one_mod] at hw
  simp only [Physical.seed, circuit, chain, hadamardAt, difference_last hn]
  change (Real.sqrt 2 : ℂ)⁻¹ *
      (normFactor n * UnifiedEJM.rawPhase u (inputBranch y 0) +
        bitSign (coord y (n-1)) * (normFactor n * UnifiedEJM.rawPhase u (inputBranch y 1))) = _
  by_cases h0 : inputBranch y 0 = 0
  · have hw1 : weight (inputBranch y 1) = 1 := by simpa [h0] using hw
    simp [UnifiedEJM.rawPhase, h0, h1, hw1, pathPhase, scale,
      ZMod.val_one_eq_one_mod] <;> ring_nf <;> norm_num <;> ring
  · simp only [UnifiedEJM.rawPhase, h0, h1, ite_false, pathPhase, scale,
      hw, pow_succ, mul_zero, add_zero]
    ring
/-- 奇偶长度标志，0为偶，1为奇。 -/
def lengthParity (n : ℕ) : Bit := if n%2 = 0 then 0 else 1

def reducedFeature (nu : Bit) (e : Bits 4) (p b : Bit) : Bits 4 :=
  ![e 0 + e 1 + e 2 + e 3,
    e 1 + p + if nu = 0 then e 2 else 0,
    p + if nu = 0 then 0 else e 2,
    e 0 + e 1 + b]

/-- 边界核，保留完整常量串缺陷。 -/
def boundaryValue (nu : Bit) (e : Bits 4) (p : Bit) (constant : Bool) (u : ℂ) : ℂ :=
  u ^ (F (reducedFeature nu e p 0)).val +
    I * bitSign (e 3) * u ^ (F (reducedFeature nu e p 1)).val +
    (I-u) * if constant then 1 else 0

theorem features_inputBranch_reduced {n : ℕ} (hn : 5 ≤ n) (y : Bits n) (b : Bit) :
    features (inputBranch y b) =
      reducedFeature (lengthParity n) (boundary y) (middleParity y) b := by
  rw [features_inputBranch hn]
  by_cases he : n%2 = 0 <;> simp [reducedFeature, boundary, lengthParity, he]

/-- 174.1：原门种子的全部n边界振幅公式。 -/
theorem actual_seed_boundary {n : ℕ} (hn : 5 ≤ n) (u : ℂ) (y : Bits n) :
    Physical.seed (UnifiedEJM.rawPhase u) y = scale n * pathPhase y *
      boundaryValue (lengthParity n) (boundary y) (middleParity y)
        (decide (∀ j, y j = coord y 0)) u := by
  rw [actual_seed_two_branch (by omega)]
  simp only [UnifiedEJM.q_eq_features, features_inputBranch_reduced hn]
  simp [boundaryValue, boundary, inputBranch_zero_iff_constant (by omega : 0 < n)]

/-- 统一族的真实参数种子直接接入，不再引入新物理态定义。 -/
theorem seed_boundary {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (y : Bits n) :
    UnifiedEJM.seed n t y = scale n * pathPhase y *
      boundaryValue (lengthParity n) (boundary y) (middleParity y)
        (decide (∀ j, y j = coord y 0)) (anglePhase t) :=
  actual_seed_boundary hn (anglePhase t) y

end UnifiedEJM.BoundaryAmplitude



