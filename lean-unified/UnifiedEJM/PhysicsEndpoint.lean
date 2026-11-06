import UnifiedEJM.Main
import UnifiedEJM.Features
import UnifiedEJM.Background
import UnifiedEJM.Multipartite
import OddEJM.Finite
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Complex

namespace UnifiedEJM.PhysicsEndpoint
open OddEJM
open OddEJM.CircuitPauli

/-- 五位压缩表示中，首位物理翻转对应的精确联合计数。 -/
def jointCount (a b : Bit) : ℤ :=
  ∑ v : Bits 5, if Q20 v = a ∧ Q20 (v + unitBit 5 0) = b then 1 else 0

theorem jointCount_values :
    jointCount 0 0 = 4 ∧ jointCount 0 1 = 8 ∧
    jointCount 1 0 = 8 ∧ jointCount 1 1 = 12 := by decide

lemma jointCount_cast (a b : Bit) :
    (jointCount a b : ℂ) =
      ∑ v : Bits 5, if Q20 v = a ∧ Q20 (v + unitBit 5 0) = b then 1 else 0 := by
  simp [jointCount]

lemma correlation_bit (a b : Bit) :
    star (I ^ b.val) * I ^ a.val =
      (if a = 0 ∧ b = 0 then (1 : ℂ) else 0) +
      (-I) * (if a = 0 ∧ b = 1 then 1 else 0) +
      I * (if a = 1 ∧ b = 0 then 1 else 0) +
      (if a = 1 ∧ b = 1 then 1 else 0) := by
  rcases OddEJM.bit_cases a with rfl | rfl <;>
    rcases OddEJM.bit_cases b with rfl | rfl <;>
      norm_num [ZMod.val_one_eq_one_mod]

theorem kernel_correlation :
    (∑ v : Bits 5, star (I ^ (Q20 (v + unitBit 5 0)).val) * I ^ (Q20 v).val) = 16 := by
  simp_rw [correlation_bit]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← jointCount_cast]
  rcases jointCount_values with ⟨h00, h01, h10, h11⟩
  rw [h00, h01, h10, h11]
  ring

/-- 对所有n的平均提升，使用已证明的压缩满射而非规模采样。 -/
theorem lifted_correlation {n : ℕ} (hn : 5 ≤ n) :
    (∑ z : Bits n,
      star (I ^ (q (z + unitBit n 0)).val) * I ^ (q z).val) = (2 : ℂ)^n / 2 := by
  have hz := sum_compress_zero hn
    (fun v : Bits 5 =>
      star (I ^ (Q20 (v + unitBit 5 0)).val) * I ^ (Q20 v).val - (1 / 2 : ℂ))
    (by rw [Finset.sum_sub_distrib, kernel_correlation]; norm_num [Fintype.card_fun])
  simp only [Finset.sum_sub_distrib, q, compress_add, compress_first hn] at hz ⊢
  have hcard : (∑ _ : Bits n, (1 / 2 : ℂ)) = (2 : ℂ)^n / 2 := by
    simp [div_eq_mul_inv]
  rw [hcard] at hz
  exact sub_eq_zero.mp hz

/-- Y_1 Z_2 经原H/CNOT电路拉回为输入Y_1。 -/
theorem yz_pullback {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n) :
    pauliAction (unitBit n 0) (unitBit n 0 + unitBit n 1) I (circuit ψ) =
      circuit (pauliAction (unitBit n 0) (unitBit n 0) I ψ) := by
  have hc : coord (unitBit n 0) (n - 1) = 0 := by
    rw [coord_unit _ _ (by omega), ite_eq_right (by omega)]
  have hd : difference (unitBit n 0) = unitBit n 0 := by
    rw [difference_unit 0 (by omega)]
    simp
  have hchar (z : Bits n) :
      character (unitBit n 0 + unitBit n 1) z =
        character (unitBit n 0) (difference z) := by
    simp only [character, CircuitPauli.dot_add_left, dot_unit_left]
    simp [coord, difference, show 0 < n by omega, show 1 < n by omega]
  simpa only [hd, hc, setBit_eq_self _ _ _ hc, mul_zero, bitSign_zero, mul_one] using
    circuit_pauli (by omega) (unitBit n 0) (unitBit n 0 + unitBit n 1)
      (unitBit n 0) I ψ hchar

theorem positive_angle : anglePhase (Real.pi / 2) = I := by
  simp [anglePhase]

/-- 真正种子态的两体Pauli见证，覆盖全部n≥5。 -/
theorem seed_yz_half {n : ℕ} (hn : 5 ≤ n) :
    pauliExpectation (UnifiedEJM.seed n (Real.pi / 2))
      (unitBit n 0) (unitBit n 0 + unitBit n 1) I = 1 / 2 := by
  unfold UnifiedEJM.seed
  rw [positive_angle]
  rw [circuit_expectation (by omega) _ _ _ _ _ _ _ (yz_pullback (by omega) _)]
  rw [UnifiedEJM.pauliExpectation_scale, UnifiedEJM.rawPhase_pauliExpectation]
  have hc : (corrected I : Vec n) = background I := by
    ext z
    simp [corrected]
  rw [hc, background_pauli_sum, bits_add_self]
  simp only [character_zero_local, one_mul]
  rw [MaskFacts.weight_unit 0 (by omega)]
  have hi : I * star I = 1 := by simp
  simp only [pow_one, hi, one_mul]
  rw [show (∑ z : Bits n,
      star (I ^ (Q20 (compress (z + unitBit n 0))).val) *
      I ^ (Q20 (compress z)).val) = (2 : ℂ)^n / 2 by
        simpa only [q] using lifted_correlation hn]
  calc
    _ = (star (normFactor n) * normFactor n * (2 : ℂ)^n) / 2 := by ring
    _ = 1 / 2 := by rw [normFactor_card]

/-- 带物理X/Z掩码的Hermitian Pauli；单位模和平方为一均按实际相位表达。 -/
structure HermitianPauli (n : ℕ) where
  x : Bits n
  z : Bits n
  phase : ℂ
  unit : star phase * phase = 1
  square : phase * phase * character z x = 1

def HermitianPauli.act {n : ℕ} (P : HermitianPauli n) (ψ : Vec n) : Vec n :=
  pauliAction P.x P.z P.phase ψ

lemma pauli_scale {n : ℕ} (a b : Bits n) (c s : ℂ) (ψ : Vec n) :
    pauliAction a b c (fun z => s * ψ z) =
      fun z => s * pauliAction a b c ψ z := by
  funext z
  simp only [pauliAction]
  ring

lemma pauli_phase {n : ℕ} (a b : Bits n) (c : ℂ) (ψ : Vec n) :
    pauliAction a b c ψ = fun z => c * pauliAction a b 1 ψ z := by
  funext z
  simp [pauliAction, mul_assoc]

lemma inner_scaled {n : ℕ} (ψ φ : Vec n) (s t : ℂ) :
    inner (fun z => s * ψ z) (fun z => t * φ z) =
      star s * t * inner ψ φ := by
  unfold OddEJM.inner
  simp only [star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma HermitianPauli.inner_act {n : ℕ} (P : HermitianPauli n) (ψ φ : Vec n) :
    inner (P.act ψ) (P.act φ) = inner ψ φ := by
  unfold HermitianPauli.act
  rw [pauli_phase P.x P.z P.phase ψ, pauli_phase P.x P.z P.phase φ,
    inner_scaled, P.unit, one_mul, pauli_inner]

lemma HermitianPauli.act_twice {n : ℕ} (P : HermitianPauli n) (ψ : Vec n) :
    P.act (P.act ψ) = ψ := by
  funext z
  have haa := bits_add_self P.x
  have hchar := character_mul_self P.z z
  simp only [HermitianPauli.act, pauliAction, add_assoc, haa, add_zero, char_add]
  calc
    _ = (P.phase * P.phase * character P.z P.x) *
        (character P.z z * character P.z z) * ψ z := by ring
    _ = ψ z := by rw [P.square, hchar]; ring

def commSign {n : ℕ} (P Q : HermitianPauli n) : ℂ :=
  character Q.z P.x * character P.z Q.x

lemma commSign_cases {n : ℕ} (P Q : HermitianPauli n) :
    commSign P Q = 1 ∨ commSign P Q = -1 := by
  unfold commSign character bitSign
  split_ifs <;> norm_num

lemma pauli_commutation {n : ℕ} (P Q : HermitianPauli n) (ψ : Vec n) :
    Q.act (P.act ψ) = fun z => commSign P Q * P.act (Q.act ψ) z := by
  funext z
  have h := congrArg (fun f => f z) (pauli_commute P.x P.z Q.x Q.z Q.phase ψ)
  simp only [HermitianPauli.act, pauliAction, one_mul, commSign] at h ⊢
  linear_combination P.phase * h

/-- 标准完整Pauli稳定子态：n个对易Hermitian Pauli共同固定的空间恰是一维。 -/
def IsStabilizer {n : ℕ} (ψ : Vec n) : Prop :=
  inner ψ ψ = 1 ∧ ∃ generators : Fin n → HermitianPauli n,
    (∀ i j, commSign (generators i) (generators j) = 1) ∧
    (∀ i, (generators i).act ψ = ψ) ∧
    (∀ φ : Vec n, (∀ i, (generators i).act φ = φ) →
      ∃ c : ℂ, φ = fun z => c * ψ z)

/-- 完整稳定子共同本征空间使任意Hermitian Pauli期望只能为0或±1。 -/
theorem stabilizer_expectation_discrete {n : ℕ} (ψ : Vec n)
    (hψ : IsStabilizer ψ) (P : HermitianPauli n) :
    inner ψ (P.act ψ) = 0 ∨ inner ψ (P.act ψ) = 1 ∨ inner ψ (P.act ψ) = -1 := by
  obtain ⟨hnorm, generators, _, hfixed, hone⟩ := hψ
  by_cases hcomm : ∀ i, commSign P (generators i) = 1
  · have hPfixed : ∀ i, (generators i).act (P.act ψ) = P.act ψ := by
      intro i
      rw [pauli_commutation, hfixed i, hcomm i]
      simp
    obtain ⟨c, hc⟩ := hone (P.act ψ) hPfixed
    have hnonzero : ∃ z, ψ z ≠ 0 := by
      by_contra h
      push Not at h
      have : inner ψ ψ = 0 := by simp [OddEJM.inner, h]
      rw [hnorm] at this
      exact one_ne_zero this
    obtain ⟨z, hz⟩ := hnonzero
    have hsquare : c * c = 1 := by
      have htwice := congrArg (fun f => f z) (P.act_twice ψ)
      rw [hc] at htwice
      change P.act (fun w => c * ψ w) z = ψ z at htwice
      have hlinear : P.act (fun w => c * ψ w) = fun w => c * P.act ψ w :=
        pauli_scale _ _ _ _ _
      rw [hlinear, hc] at htwice
      dsimp at htwice
      apply (mul_right_cancel₀ hz)
      calc
        (c*c) * ψ z = c * (c * ψ z) := by ring
        _ = ψ z := htwice
        _ = 1 * ψ z := by ring
    have hvalues : c = 1 ∨ c = -1 := by
      have hfactor : (c - 1) * (c + 1) = 0 := by linear_combination hsquare
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rw [hc, inner_scale_right, hnorm, mul_one]
    exact Or.inr hvalues
  · push Not at hcomm
    obtain ⟨i, hi⟩ := hcomm
    have hsign : commSign P (generators i) = -1 :=
      (commSign_cases P (generators i)).resolve_left hi
    have heq : inner ψ (P.act ψ) = -inner ψ (P.act ψ) := by
      calc
        inner ψ (P.act ψ) = inner ((generators i).act ψ)
            ((generators i).act (P.act ψ)) := ((generators i).inner_act _ _).symm
        _ = inner ψ (fun z => -1 * P.act ψ z) := by
          rw [hfixed, pauli_commutation, hfixed, hsign]
        _ = -inner ψ (P.act ψ) := by rw [inner_scale_right]; ring
    exact Or.inl (by linear_combination (1/2 : ℂ) * heq)

/-- 此标签按原相位约定正是第1、2物理比特上的Y⊗Z。 -/
def yzPauli {n : ℕ} (hn : 2 ≤ n) : HermitianPauli n where
  x := unitBit n 0
  z := unitBit n 0 + unitBit n 1
  phase := I
  unit := by simp
  square := by
    have hc : character (unitBit n 0 + unitBit n 1) (unitBit n 0) = -1 := by
      simp [character, CircuitPauli.dot_add_left, dot_unit_left,
        coord_unit _ _ (by omega : 0 < n), bitSign]
    rw [hc]
    simp

/-- 对全部n≥5的实际零半径端点排除完整Pauli稳定子态。 -/
theorem endpoint_not_stabilizer {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsStabilizer (UnifiedEJM.seed n (Real.pi / 2)) := by
  intro hs
  have h := stabilizer_expectation_discrete _ hs (yzPauli (by omega : 2 ≤ n))
  simp only [HermitianPauli.act, yzPauli, inner_pauliExpectation] at h
  rw [seed_yz_half hn] at h
  norm_num at h

open UnifiedEJM.Multipartite

lemma merge_add_supported {n : ℕ} (S : Finset (Fin n)) (a : Bits n)
    (ha : ∀ j, j ∉ S → a j = 0) (u : Side S) (v : OtherSide S) :
    (split S).symm (u,v) + a =
      (split S).symm ((fun j => u j + a j),v) := by
  funext j
  by_cases hj : j ∈ S
  · simp [split, Equiv.piEquivPiSubtypeProd, hj]
  · simp [split, Equiv.piEquivPiSubtypeProd, hj, ha j hj]

lemma character_merge_supported {n : ℕ} (S : Finset (Fin n)) (b : Bits n)
    (hb : ∀ j, j ∉ S → b j = 0) (u : Side S) (v : OtherSide S) :
    character b ((split S).symm (u,v)) =
      character b ((split S).symm (u,0)) := by
  unfold character
  congr 1
  unfold dot
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ S
  · simp [split, Equiv.piEquivPiSubtypeProd, hj]
  · simp [hb j hj]

/-- 实际偏迹若为对角阵，支撑在该子系统且翻转至少一位的Pauli期望为零。 -/
theorem pauliExpectation_eq_zero_of_diagonal_reduced {n : ℕ}
    (S : Finset (Fin n)) (ψ : Vec n) (a b : Bits n) (c : ℂ)
    (ha : ∀ j, j ∉ S → a j = 0) (hb : ∀ j, j ∉ S → b j = 0)
    (hflip : ∃ j ∈ S, a j ≠ 0)
    (hρ : ∀ u u' : Side S, u ≠ u' → reduced S ψ u u' = 0) :
    pauliExpectation ψ a b c = 0 := by
  classical
  unfold pauliExpectation
  rw [← (split S).symm.sum_comp (fun z =>
    star (ψ (z + a)) * c * character b z * ψ z)]
  simp only [Fintype.sum_prod_type, merge_add_supported S a ha,
    character_merge_supported S b hb]
  apply Finset.sum_eq_zero
  intro u _
  have hne : u ≠ (fun j : {j // j ∈ S} => u j + a j) := by
    intro heq
    obtain ⟨j,hj,haj⟩ := hflip
    apply haj
    have heqj := congrFun heq ⟨j,hj⟩
    simpa using heqj.symm
  calc
    _ = (c * character b ((split S).symm (u,0))) *
        reduced S ψ u (fun j => u j + a j) := by
      rw [reduced_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = 0 := by rw [hρ _ _ hne, mul_zero]

/-- 真实所有二比特约化均为I/4。 -/
def IsTwoUniform {n : ℕ} (ψ : Vec n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 2 → reduced S ψ = (1/4 : ℂ) • 1

/-- 非零Y⊗Z期望与真实二比特最大混合约化互斥。 -/
theorem not_twoUniform_of_yz_ne_zero {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n)
    (hyz : pauliExpectation ψ (unitBit n 0) (unitBit n 0 + unitBit n 1) I ≠ 0) :
    ¬ IsTwoUniform ψ := by
  classical
  intro hu
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  let S : Finset (Fin n) := {i,j}
  have hij : i ≠ j := by simp [i,j]
  have hcard : S.card = 2 := by simp [S,hij]
  have hρ := hu S hcard
  have hzero := pauliExpectation_eq_zero_of_diagonal_reduced S
    ψ (unitBit n 0)
    (unitBit n 0 + unitBit n 1) I
  have ha : ∀ k, k ∉ S → unitBit n 0 k = 0 := by
    intro k hk
    have hki : k ≠ i := by simpa [S] using (not_or.mp (by simpa [S] using hk)).1
    have hk0 : k.val ≠ 0 := by simpa [i, Fin.ext_iff] using hki
    simp [unitBit, hk0]
  have hb : ∀ k, k ∉ S → (unitBit n 0 + unitBit n 1) k = 0 := by
    intro k hk
    have hki : k ≠ i := by simpa [S] using (not_or.mp (by simpa [S] using hk)).1
    have hkj : k ≠ j := by simpa [S] using (not_or.mp (by simpa [S] using hk)).2
    have hk0 : k.val ≠ 0 := by simpa [i, Fin.ext_iff] using hki
    have hk1 : k.val ≠ 1 := by simpa [j, Fin.ext_iff] using hkj
    simp [unitBit, hk0, hk1]
  have hflip : ∃ k ∈ S, unitBit n 0 k ≠ 0 := by
    refine ⟨i, by simp [S], ?_⟩
    simp [unitBit,i]
  have hd : ∀ u u' : Side S, u ≠ u' →
      reduced S ψ u u' = 0 := by
    intro u u' hne
    rw [hρ]
    simp [hne]
  specialize hzero ha hb hflip hd
  exact hyz hzero

/-- 对全部n≥5，零半径端点有非零二体相关，故不可能2-uniform。 -/
theorem endpoint_not_twoUniform {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsTwoUniform (UnifiedEJM.seed n (Real.pi / 2)) := by
  apply not_twoUniform_of_yz_ne_zero (by omega)
  rw [seed_yz_half hn]
  norm_num

/-- 实际全部测量列的两体见证只差Pauli轨道符号。 -/
theorem measurement_yz_sign {n : ℕ} (hn : 5 ≤ n) (label : Bits n) :
    pauliExpectation (UnifiedEJM.measurement n (Real.pi / 2) label)
      (unitBit n 0) (unitBit n 0 + unitBit n 1) I =
      (character (unitBit n 0 + unitBit n 1) (orbitX label) *
        character (orbitZ label) (unitBit n 0)) / 2 := by
  change pauliExpectation (Physical.measurement (rawPhase (anglePhase (Real.pi/2))) label)
    (unitBit n 0) (unitBit n 0 + unitBit n 1) I = _
  rw [Physical.measurement_orbit (by omega), pauli_conjugation_expectation]
  change _ * pauliExpectation (UnifiedEJM.seed n (Real.pi/2))
    (unitBit n 0) (unitBit n 0 + unitBit n 1) I = _
  rw [seed_yz_half hn]
  ring

theorem measurement_yz_half_or_neg {n : ℕ} (hn : 5 ≤ n) (label : Bits n) :
    pauliExpectation (UnifiedEJM.measurement n (Real.pi / 2) label)
      (unitBit n 0) (unitBit n 0 + unitBit n 1) I = 1/2 ∨
    pauliExpectation (UnifiedEJM.measurement n (Real.pi / 2) label)
      (unitBit n 0) (unitBit n 0 + unitBit n 1) I = -1/2 := by
  rw [measurement_yz_sign hn]
  unfold character bitSign
  split_ifs <;> norm_num

theorem measurement_endpoint_not_stabilizer {n : ℕ} (hn : 5 ≤ n) (label : Bits n) :
    ¬ IsStabilizer (UnifiedEJM.measurement n (Real.pi / 2) label) := by
  intro hs
  have h := stabilizer_expectation_discrete _ hs (yzPauli (by omega : 2 ≤ n))
  simp only [HermitianPauli.act, yzPauli, inner_pauliExpectation] at h
  rcases measurement_yz_half_or_neg hn label with hyz | hyz <;>
    rw [hyz] at h <;> norm_num at h

theorem measurement_endpoint_not_twoUniform {n : ℕ} (hn : 5 ≤ n) (label : Bits n) :
    ¬ IsTwoUniform (UnifiedEJM.measurement n (Real.pi / 2) label) := by
  apply not_twoUniform_of_yz_ne_zero (by omega)
  rcases measurement_yz_half_or_neg hn label with hyz | hyz <;>
    rw [hyz] <;> norm_num

theorem radius_strictly_lt_one {n : ℕ} (hn : 5 ≤ n) (t : ℝ) :
    OddEJM.radius n t < 1 := by
  rw [radius_eq_geometry]
  apply (Geometry.radius_le_max n (by omega) t).trans_lt
  unfold Geometry.radiusMax
  apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ (n - 2))).2
  have hp : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (n - 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith [Geometry.sqrt_three_sq, Real.sqrt_nonneg (3 : ℝ)]
  norm_num at hp ⊢
  linarith

/-- 任意参数的实际单体约化纯度严格小于1，因而端点也没有纯单体因子。 -/
theorem measurement_single_purity_lt_one {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    (Matrix.trace (OddEJM.reduced (UnifiedEJM.measurement n t label) j *
      OddEJM.reduced (UnifiedEJM.measurement n t label) j)).re < 1 := by
  rw [UnifiedEJM.measurement_purity hn]
  simp only [ofReal_re]
  have hlt := radius_strictly_lt_one hn t
  have hnonneg : 0 ≤ OddEJM.radius n t := by
    rw [radius_eq_geometry]
    exact Geometry.radius_nonneg n t
  nlinarith

theorem measurement_single_purity_ne_one {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (j : Fin n) :
    Matrix.trace (OddEJM.reduced (UnifiedEJM.measurement n t label) j *
      OddEJM.reduced (UnifiedEJM.measurement n t label) j) ≠ 1 := by
  intro h
  have hlt := measurement_single_purity_lt_one hn t label j
  rw [h] at hlt
  norm_num at hlt

/-- 任意参数的实际测量列经局域酉、物理位置换及整体相位后仍无纯单比特因子。 -/
theorem measurement_no_pure_qubit_factor {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (label : Bits n) (U : Fin n → Matrix Bit Bit ℂ)
    (hU : ∀ j, (U j).conjTranspose * U j = 1) (p : Equiv.Perm (Fin n))
    (c : ℂ) (hc : star c * c = 1) (j : Fin n) :
    ¬ ProductAcross {j} (c • localAction U
      (permute p (UnifiedEJM.measurement n t label))) := by
  exact no_pure_qubit_factor _ (measurement_single_purity_lt_one hn t label) U hU p c hc j

end UnifiedEJM.PhysicsEndpoint
