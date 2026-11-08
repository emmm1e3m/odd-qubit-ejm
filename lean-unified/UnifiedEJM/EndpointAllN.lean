import UnifiedEJM.PhysicsEndpointStabilizer
import OddEJM.Walsh

noncomputable section
open scoped BigOperators Matrix
open Complex OddEJM OddEJM.CircuitPauli
open UnifiedEJM.Multipartite UnifiedEJM.StabilizerMarginal
open UnifiedEJM.PhysicsEndpoint

namespace UnifiedEJM.EndpointAllN

/-- 首两位的物理 Pauli 掩码。 -/
def outMask (n : ℕ) (a : Pair) : Bits n :=
  a.1 • unitBit n 0 + a.2 • unitBit n 1

def preZ (n : ℕ) (b : Pair) : Bits n :=
  b.1 • CircuitPauli.tailMask n 0 + b.2 • CircuitPauli.tailMask n 1

def inputA (n : ℕ) (a b : Pair) : Bits n :=
  (a.1+a.2) • unitBit n 0 + a.2 • unitBit n 1 +
    (b.1+b.2) • unitBit n (n-1)

def inputB (n : ℕ) (b : Pair) : Bits n := setBit (preZ n b) (n-1) 0

def kernelA (a b : Pair) : Bits 5 :=
  (a.1+a.2) • unitBit 5 0 + a.2 • unitBit 5 1 +
    (b.1+b.2) • unitBit 5 4

def kernelH (a b : Pair) : Bits 5 :=
  ![a.1+a.2+b.1, b.1+b.2, b.1+b.2, b.1+b.2, b.1+b.2]

lemma coord_smul' {n} (r : Bit) (z : Bits n) (j : ℕ) :
    coord (r • z) j = r * coord z j := by
  by_cases hj : j < n <;> simp [coord, hj]

lemma difference_smul' {n} (r : Bit) (z : Bits n) :
    difference (r • z) = r • difference z := by
  funext k
  simp [difference, coord_smul', mul_add]

lemma difference_outMask {n} (hn : 2 ≤ n) (a : Pair) :
    difference (outMask n a) = (a.1+a.2) • unitBit n 0 + a.2 • unitBit n 1 := by
  rw [outMask, difference_add, difference_smul', difference_smul',
    difference_unit 0 (by omega), difference_unit 1 (by omega)]
  ext k
  simp
  ring

lemma pair_pullback {n} (hn : 5 ≤ n) (a b : Pair) (ψ : Vec n) :
    pauliAction (outMask n a) (outMask n b) (pairPhase a b) (circuit ψ) =
      circuit (pauliAction (inputA n a b) (inputB n b) (pairPhase a b) ψ) := by
  have hchar (z : Bits n) : character (outMask n b) z =
      character (preZ n b) (difference z) := by
    simp only [outMask, preZ, character, OddEJM.dot_add_left, dot_smul_left]
    rw [dot_unit_left, dot_unit_left, dot_tail _ 0 (by omega),
      dot_tail _ 1 (by omega), suffix_difference]
    simp [coord, show 0 < n by omega, show 1 < n by omega]
  have hz : coord (preZ n b) (n-1) = b.1+b.2 := by
    simp [preZ, coord, CircuitPauli.tailMask,
      show n-1 < n by omega, show 1 ≤ n-1 by omega]
  have ha : coord (difference (outMask n a)) (n-1) = 0 := by
    rw [difference_outMask (by omega)]
    simp [coord_add, coord_smul', coord_unit _ _ (by omega : 0 < n),
      coord_unit _ _ (by omega : 1 < n), show n-1 ≠ 0 by omega,
      show n-1 ≠ 1 by omega]
  have hA : setBit (difference (outMask n a)) (n-1) (b.1+b.2) = inputA n a b := by
    rw [setBit_add_unit, ha, difference_outMask (by omega)]
    ext k
    simp [inputA, mul_comm]
  simpa only [hz, ha, hA, zero_mul, bitSign_zero, mul_one, inputB] using
    circuit_pauli (by omega) (outMask n a) (outMask n b) (preZ n b)
      (pairPhase a b) ψ hchar

lemma compress_inputA {n} (hn : 5 ≤ n) (a b : Pair) :
    compress (inputA n a b) = kernelA a b := by
  simp only [inputA, kernelA, compress_add, compress_smul,
    compress_first hn, compress_second hn, compress_last hn]

/-- 拉回后的字符只比五位压缩字符多一个第二坐标。 -/
lemma input_mask {n} (hn : 5 ≤ n) (a b : Pair) :
    inputA n a b + inputB n b = liftMask n (kernelH a b) + a.2 • unitBit n 1 := by
  ext k
  have hk := k.isLt
  have hp : k.val % 2 = 0 ∨ k.val % 2 = 1 := by omega
  by_cases h0 : k.val = 0
  · simp [inputA, inputB, preZ, liftMask, kernelH, unitBit, blockMask,
      setBit, CircuitPauli.tailMask, h0, show 0 ≠ n-1 by omega,
      show 0 ≠ n-2 by omega]
  by_cases hl : k.val = n-1
  · simp [inputA, inputB, preZ, liftMask, kernelH, unitBit, blockMask,
      setBit, hl, show n-1 ≠ 0 by omega,
      show n-1 ≠ 1 by omega, show n-1 ≠ n-2 by omega,
      show ¬ n-1 < n-2 by omega]
  by_cases hp2 : k.val = n-2
  · simp [inputA, inputB, preZ, liftMask, kernelH, unitBit, blockMask,
      setBit, CircuitPauli.tailMask, hp2, show n-2 ≠ 0 by omega,
      show n-2 ≠ 1 by omega, show n-2 ≠ n-1 by omega,
      show 1 ≤ n-2 by omega]
  have hlow : 1 ≤ k.val := by omega
  have hhigh : k.val < n-2 := by omega
  rcases hp with hp | hp <;>
    simp [inputA, inputB, preZ, liftMask, kernelH, unitBit, blockMask,
      setBit, CircuitPauli.tailMask, h0, hl, hp2, hlow, hhigh, hp] <;> ring

lemma endpoint_expectation_sum {n} (hn : 5 ≤ n) (a b : Pair) :
    pauliExpectation (UnifiedEJM.seed n (Real.pi/2)) (outMask n a) (outMask n b)
      (pairPhase a b) =
      (star (normFactor n) * normFactor n) *
      (pairPhase a b * star (I ^ weight (inputA n a b))) *
      ∑ z : Bits n, character (inputA n a b + inputB n b) z *
        star (I ^ (Q20 (compress z + kernelA a b)).val) *
          I ^ (Q20 (compress z)).val := by
  unfold UnifiedEJM.seed
  rw [positive_angle, circuit_expectation (by omega) _ _ _ _ _ _ _
    (pair_pullback hn a b _), UnifiedEJM.pauliExpectation_scale,
    UnifiedEJM.rawPhase_pauliExpectation]
  have he : (UnifiedEJM.corrected I : Vec n) = UnifiedEJM.background I := by
    ext z
    simp [UnifiedEJM.corrected]
  rw [he, UnifiedEJM.background_pauli_sum]
  simp only [compress_add, compress_inputA hn]
  ring

/-- 当 n≥6，翻转输入第二、第四坐标保留全部五个压缩特征。 -/
lemma compress_cancel_shift {n} (hn : 6 ≤ n) :
    compress (unitBit n 1 + unitBit n 3) = 0 := by
  rw [compress_add, compress_second (by omega),
    compress_internal_odd (⟨3, by omega⟩ : Fin n) (by norm_num) (by simp; omega) (by norm_num)]
  exact bits_add_self _

lemma expectation_secondX_zero {n} (hn : 6 ≤ n) (a b : Pair) (ha : a.2=1) :
    pauliExpectation (UnifiedEJM.seed n (Real.pi/2)) (outMask n a) (outMask n b)
      (pairPhase a b) = 0 := by
  rw [endpoint_expectation_sum (by omega)]
  suffices hs : (∑ z : Bits n, character (inputA n a b + inputB n b) z *
      (star (I ^ (Q20 (compress z + kernelA a b)).val) *
        I ^ (Q20 (compress z)).val)) = 0 by
    simp only [mul_assoc, hs, mul_zero]
  apply weighted_character_zero _ (unitBit n 1 + unitBit n 3)
  · rw [input_mask (by omega), OddEJM.dot_add_left, dot_liftMask (by omega),
      compress_cancel_shift hn]
    rw [dot_smul_left, dot_add_right, dot_unit_right, dot_unit_right]
    simp [ha, dot, coord, unitBit, show 1 < n by omega, show 3 < n by omega]
  · intro z
    simp only [compress_add, compress_cancel_shift hn, add_zero]

/-- 固定五位核的带符号联合计数，所有值在整数中计算。 -/
def signedCount (a b c p q' : Bit) : ℤ :=
  ∑ v : Bits 5, if Q20 v = p ∧ Q20 (v + kernelA (a,0) (b,c)) = q'
    then intSign (dot (kernelH (a,0) (b,c)) v) else 0

def kernelValue (a b c : Bit) : ℤ :=
  if a=0 ∧ b=0 ∧ c=0 then 32 else if a=1 ∧ b=1 ∧ c=1 then 16 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signedCount_certificate : ∀ a b c : Bit,
    signedCount a b c 0 0 + signedCount a b c 1 1 = kernelValue a b c ∧
    signedCount a b c 1 0 = signedCount a b c 0 1 := by
  decide +kernel

lemma signedCount_cast (a b c p q' : Bit) :
    (signedCount a b c p q' : ℂ) =
      ∑ v : Bits 5, if Q20 v = p ∧ Q20 (v + kernelA (a,0) (b,c)) = q'
        then character (kernelH (a,0) (b,c)) v else 0 := by
  simp [signedCount, character]

lemma kernel_sum (a b c : Bit) :
    (∑ v : Bits 5, character (kernelH (a,0) (b,c)) v *
      star (I ^ (Q20 (v + kernelA (a,0) (b,c))).val) * I ^ (Q20 v).val) =
      (kernelValue a b c : ℂ) := by
  have hterm (v : Bits 5) : character (kernelH (a,0) (b,c)) v *
      star (I ^ (Q20 (v + kernelA (a,0) (b,c))).val) * I ^ (Q20 v).val =
      (if Q20 v=0 ∧ Q20 (v+kernelA (a,0) (b,c))=0 then character (kernelH (a,0) (b,c)) v else 0) +
      (-I) * (if Q20 v=0 ∧ Q20 (v+kernelA (a,0) (b,c))=1 then character (kernelH (a,0) (b,c)) v else 0) +
      I * (if Q20 v=1 ∧ Q20 (v+kernelA (a,0) (b,c))=0 then character (kernelH (a,0) (b,c)) v else 0) +
      (if Q20 v=1 ∧ Q20 (v+kernelA (a,0) (b,c))=1 then character (kernelH (a,0) (b,c)) v else 0) := by
    rcases OddEJM.bit_cases (Q20 v) with h | h <;>
      rcases OddEJM.bit_cases (Q20 (v+kernelA (a,0) (b,c))) with h' | h' <;>
        simp [h,h', ZMod.val_one_eq_one_mod] <;> ring_nf
    all_goals simp
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← signedCount_cast]
  obtain ⟨hr, hi⟩ := signedCount_certificate a b c
  have hrc : (signedCount a b c 0 0 : ℂ) + (signedCount a b c 1 1 : ℂ) =
      (kernelValue a b c : ℂ) := by exact_mod_cast hr
  rw [hi]
  linear_combination hrc

lemma sum_compress_average {n} (hn : 5 ≤ n) (f : Bits 5 → ℂ) :
    (∑ z : Bits n, f (compress z)) = (2 : ℂ)^n * (∑ v, f v) / 32 := by
  have hz := sum_compress_zero hn (fun v => f v - (∑ w, f w) / 32) (by
    rw [Finset.sum_sub_distrib]
    simp
    ring)
  rw [Finset.sum_sub_distrib] at hz
  have hc : (∑ _ : Bits n, (∑ w, f w) / 32) = (2 : ℂ)^n * (∑ w, f w) / 32 := by
    simp [mul_div_assoc]
  rw [hc] at hz
  exact sub_eq_zero.mp hz

lemma expectation_no_secondX {n} (hn : 5 ≤ n) (a b c : Bit) :
    pauliExpectation (UnifiedEJM.seed n (Real.pi/2)) (outMask n (a,0))
      (outMask n (b,c)) (pairPhase (a,0) (b,c)) =
      (pairPhase (a,0) (b,c) * star (I ^ weight (inputA n (a,0) (b,c)))) *
        (kernelValue a b c : ℂ) / 32 := by
  rw [endpoint_expectation_sum hn]
  simp only [input_mask hn, zero_smul, add_zero]
  simp only [character, dot_liftMask hn]
  change _ * _ * (∑ z : Bits n,
    (fun v : Bits 5 => character (kernelH (a,0) (b,c)) v *
      star (I ^ (Q20 (v + kernelA (a,0) (b,c))).val) * I ^ (Q20 v).val) (compress z)) = _
  rw [sum_compress_average hn (fun v => character (kernelH (a,0) (b,c)) v *
    star (I ^ (Q20 (v + kernelA (a,0) (b,c))).val) * I ^ (Q20 v).val), kernel_sum]
  calc
    _ = (star (normFactor n) * normFactor n * (2 : ℂ)^n) *
      (pairPhase (a,0) (b,c) * star (I ^ weight (inputA n (a,0) (b,c)))) *
        (kernelValue a b c : ℂ) / 32 := by ring
    _ = _ := by rw [normFactor_card, one_mul]

/-- 全 n 的真实首两体 Pauli 表；除恒等和 Y⊗Z 外全部为零。 -/
theorem endpoint_pair_expectation {n} (hn : 6 ≤ n) (a b : Pair) :
    pauliExpectation (UnifiedEJM.seed n (Real.pi/2)) (outMask n a) (outMask n b)
      (pairPhase a b) =
      if a=(0,0) ∧ b=(0,0) then 1 else if a=(1,0) ∧ b=(1,1) then 1/2 else 0 := by
  rcases a with ⟨a,a'⟩
  rcases b with ⟨b,c⟩
  rcases OddEJM.bit_cases a' with rfl | rfl
  · rw [expectation_no_secondX (by omega)]
    rcases OddEJM.bit_cases a with rfl | rfl <;>
      rcases OddEJM.bit_cases b with rfl | rfl <;>
      rcases OddEJM.bit_cases c with rfl | rfl <;>
      norm_num [kernelValue, pairPhase, inputA, ZMod.val_one_eq_one_mod,
        show (2 : Bit)=0 by decide, two_smul,
        MaskFacts.weight_unit 0 (by omega : 0 < n)]
  · rw [expectation_secondX_zero hn _ _ rfl]
    simp

lemma outMask_eq_embedPair {n} (hn : 2 ≤ n) (a : Pair) :
    outMask n a = embedPair (⟨0,by omega⟩ : Fin n) ⟨1,by omega⟩ a := by
  ext k
  by_cases h0 : k.val=0
  · have hk : k=(⟨0,by omega⟩ : Fin n) := Fin.ext h0
    rw [hk]
    simp [outMask, embedPair, unitBit]
  by_cases h1 : k.val=1
  · have hk : k=(⟨1,by omega⟩ : Fin n) := Fin.ext h1
    rw [hk]
    simp [outMask, embedPair, unitBit]
  · have hk0 : k ≠ (⟨0,by omega⟩ : Fin n) := by simpa [Fin.ext_iff] using h0
    have hk1 : k ≠ (⟨1,by omega⟩ : Fin n) := by simpa [Fin.ext_iff] using h1
    simp [outMask, embedPair, unitBit, h0, h1, hk0, hk1]

/-- 两体纯度直接由真实偏迹的 Pauli Parseval 恒等式得到。 -/
theorem endpoint_pair_purity_ge_six {n} (hn : 6 ≤ n) :
    cutPurity ({⟨0,by omega⟩,⟨1,by omega⟩} : Finset (Fin n))
      (UnifiedEJM.seed n (Real.pi/2)) = (5/16 : ℂ) := by
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i ≠ j := by simp [i,j]
  have hp := pair_parseval (pairReduced i j hij (UnifiedEJM.seed n (Real.pi/2)))
  rw [pairReduced_purity] at hp
  have hc (a b : Pair) : coefficient (pairReduced i j hij (UnifiedEJM.seed n (Real.pi/2))) a b =
      if a=(0,0) ∧ b=(0,0) then 1 else if a=(1,0) ∧ b=(1,1) then 1/2 else 0 := by
    rw [pair_coefficient_expectation, HermitianPauli.act, inner_pauliExpectation]
    change pauliExpectation _ (embedPair i j a) (embedPair i j b) (pairPhase a b) = _
    simpa only [outMask_eq_embedPair (by omega : 2 ≤ n), i, j] using
      endpoint_pair_expectation hn a b
  simp_rw [hc] at hp
  norm_num [Fintype.sum_prod_type, sum_bit] at hp
  change cutPurity {i,j} _ = _
  linear_combination (1/4 : ℂ) * hp

/-- 第一、第二个物理量子比特组成的割，索引显式携带范围证明。 -/
def pairCut {n : ℕ} (hn : 5 ≤ n) : Finset (Fin n) :=
  {⟨0,by omega⟩,⟨1,by omega⟩}

lemma pairCut_card {n : ℕ} (hn : 5 ≤ n) : (pairCut hn).card = 2 := by
  have hij : (⟨0,by omega⟩ : Fin n) ≠ ⟨1,by omega⟩ := by
    simp [Fin.ext_iff]
  simp [pairCut, hij]

/-- 全部 n≥5 的实际正端点两体纯度，包含五比特特例。 -/
theorem endpoint_pair_purity {n : ℕ} (hn : 5 ≤ n) :
    cutPurity (pairCut hn) (UnifiedEJM.seed n (Real.pi/2)) =
      if n=5 then (11/32 : ℂ) else 5/16 := by
  by_cases hn5 : n=5
  · subst n
    simpa [pairCut] using PhysicsFinite.new5_endpoint_pair_purity
  · rw [ite_eq_right hn5]
    exact endpoint_pair_purity_ge_six (by omega)

theorem measurement_pair_purity {n : ℕ} (hn : 5 ≤ n) (label : Bits n) :
    cutPurity (pairCut hn) (UnifiedEJM.measurement n (Real.pi/2) label) =
      if n=5 then (11/32 : ℂ) else 5/16 := by
  change cutPurity _ (Physical.measurement
    (UnifiedEJM.rawPhase (anglePhase (Real.pi/2))) label) = _
  rw [cutPurity_measurement (by omega)]
  exact endpoint_pair_purity hn

/-- 全 n 端点排除任意稳定子纯态的局域酉、比特置换和整体相位轨道。 -/
theorem endpoint_not_LU_stabilizer {n : ℕ} (hn : 5 ≤ n)
    (φ : Vec n) (hφ : IsStabilizer φ)
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin n)) (c : ℂ) (hc : star c*c=1) :
    UnifiedEJM.seed n (Real.pi/2) ≠ c • localAction U (permute p φ) := by
  apply not_stabilizer_LU_of_pairPurity (pairCut hn) (pairCut_card hn) _ _ φ hφ U hU p c hc
  rw [endpoint_pair_purity hn]
  split_ifs <;> simp

/-- 每个测量列均继承上述全 n 排除结论。 -/
theorem measurement_not_LU_stabilizer {n : ℕ} (hn : 5 ≤ n) (label : Bits n)
    (φ : Vec n) (hφ : IsStabilizer φ)
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin n)) (c : ℂ) (hc : star c*c=1) :
    UnifiedEJM.measurement n (Real.pi/2) label ≠ c • localAction U (permute p φ) := by
  apply not_stabilizer_LU_of_pairPurity (pairCut hn) (pairCut_card hn) _ _ φ hφ U hU p c hc
  rw [measurement_pair_purity hn label]
  split_ifs <;> simp

end UnifiedEJM.EndpointAllN
