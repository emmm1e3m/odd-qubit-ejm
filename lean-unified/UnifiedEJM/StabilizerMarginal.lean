import UnifiedEJM.PhysicsEndpoint

noncomputable section
open scoped BigOperators Matrix
open Complex OddEJM OddEJM.CircuitPauli
open UnifiedEJM.Multipartite UnifiedEJM.PhysicsEndpoint

namespace UnifiedEJM.StabilizerMarginal

abbrev Pair := Bit × Bit

def pairPhase (a b : Pair) : ℂ := I ^ (a.1*b.1).val * I ^ (a.2*b.2).val
def pairChar (b z : Pair) : ℂ := bitSign (b.1*z.1) * bitSign (b.2*z.2)
def coefficient (R : Matrix Pair Pair ℂ) (a b : Pair) : ℂ :=
  ∑ z : Pair, pairPhase a b * pairChar b z * R z (z+a)

/-- 两比特Pauli展开的有限维Parseval恒等式，适用于任意复矩阵。 -/
theorem pair_parseval (R : Matrix Pair Pair ℂ) :
    4 * Matrix.trace (R*R) = ∑ a : Pair, ∑ b : Pair, (coefficient R a b)^2 := by
  simp only [coefficient, pairPhase, pairChar, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, sum_bit]
  norm_num [bitSign, ZMod.val_one_eq_one_mod, Prod.fst_add, Prod.snd_add]
  ring_nf
  simp [show (2 : Bit) = 0 by decide]
  ring

/-- 在任意两个不同物理位上嵌入二位串。 -/
def embedPair {n : ℕ} (i j : Fin n) (a : Pair) : Bits n :=
  fun k => if k=i then a.1 else if k=j then a.2 else 0

lemma embedPair_i {n} (i j : Fin n) (a : Pair) : embedPair i j a i = a.1 := by
  simp [embedPair]
lemma embedPair_j {n} (i j : Fin n) (hij : i ≠ j) (a : Pair) :
    embedPair i j a j = a.2 := by simp [embedPair, Ne.symm hij]

lemma character_embedPair {n} (i j : Fin n) (hij : i ≠ j) (b : Pair) (z : Bits n) :
    character (embedPair i j b) z = bitSign (b.1*z i) * bitSign (b.2*z j) := by
  have heq : (fun k => embedPair i j b k * z k) =
      (fun k => (if k=i then b.1*z i else 0) + (if k=j then b.2*z j else 0)) := by
    funext k
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [embedPair]
  simp only [character, dot, heq, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, sign_add]

def pairPauli {n} (i j : Fin n) (hij : i ≠ j) (a b : Pair) : HermitianPauli n where
  x := embedPair i j a
  z := embedPair i j b
  phase := pairPhase a b
  unit := by
    rcases a with ⟨a,a'⟩; rcases b with ⟨b,b'⟩
    rcases OddEJM.bit_cases a with rfl | rfl <;>
      rcases OddEJM.bit_cases a' with rfl | rfl <;>
      rcases OddEJM.bit_cases b with rfl | rfl <;>
      rcases OddEJM.bit_cases b' with rfl | rfl <;>
      norm_num [pairPhase, ZMod.val_one_eq_one_mod]
  square := by
    rw [character_embedPair i j hij, embedPair_i, embedPair_j i j hij]
    rcases a with ⟨a,a'⟩; rcases b with ⟨b,b'⟩
    rcases OddEJM.bit_cases a with rfl | rfl <;>
      rcases OddEJM.bit_cases a' with rfl | rfl <;>
      rcases OddEJM.bit_cases b with rfl | rfl <;>
      rcases OddEJM.bit_cases b' with rfl | rfl <;>
      norm_num [pairPhase, bitSign, ZMod.val_one_eq_one_mod]

def pairSideEquiv {n} (i j : Fin n) (hij : i ≠ j) : Pair ≃ Side ({i,j} : Finset (Fin n)) where
  toFun a k := if k.val=i then a.1 else a.2
  invFun f := (f ⟨i,by simp⟩, f ⟨j,by simp⟩)
  left_inv a := by simp [Ne.symm hij]
  right_inv f := by
    funext k
    rcases k with ⟨k,hk⟩
    have hk' : k=i ∨ k=j := by simpa using hk
    rcases hk' with rfl | rfl <;> simp [Ne.symm hij]

def pairReduced {n} (i j : Fin n) (hij : i ≠ j) (ψ : Vec n) : Matrix Pair Pair ℂ :=
  (reduced {i,j} ψ).submatrix (pairSideEquiv i j hij) (pairSideEquiv i j hij)

lemma pairReduced_purity {n} (i j : Fin n) (hij : i ≠ j) (ψ : Vec n) :
    Matrix.trace (pairReduced i j hij ψ * pairReduced i j hij ψ) = cutPurity {i,j} ψ := by
  unfold pairReduced
  rw [Matrix.submatrix_mul_equiv]
  exact (pairSideEquiv i j hij).sum_comp (fun a => (reduced {i,j} ψ * reduced {i,j} ψ) a a)

lemma pairSideEquiv_add {n} (i j : Fin n) (hij : i ≠ j) (u a : Pair) :
    (fun k : {k // k ∈ ({i,j} : Finset (Fin n))} =>
      pairSideEquiv i j hij u k + embedPair i j a k) = pairSideEquiv i j hij (u+a) := by
  funext k
  rcases k with ⟨k,hk⟩
  have hk' : k=i ∨ k=j := by simpa using hk
  rcases hk' with rfl | rfl <;> simp [pairSideEquiv, embedPair, Ne.symm hij]

lemma pairChar_merge {n} (i j : Fin n) (hij : i ≠ j) (b u : Pair)
    (v : OtherSide ({i,j} : Finset (Fin n))) :
    character (embedPair i j b) ((split {i,j}).symm (pairSideEquiv i j hij u,v)) =
      pairChar b u := by
  rw [character_embedPair i j hij]
  simp [pairChar, split, Equiv.piEquivPiSubtypeProd, pairSideEquiv, Ne.symm hij]

/-- 全系统Pauli期望确为真实两体偏迹的Pauli展开系数。 -/
theorem pair_coefficient_expectation {n} (i j : Fin n) (hij : i ≠ j)
    (ψ : Vec n) (a b : Pair) :
    coefficient (pairReduced i j hij ψ) a b = inner ψ ((pairPauli i j hij a b).act ψ) := by
  classical
  rw [HermitianPauli.act, inner_pauliExpectation]
  change _ = pauliExpectation ψ (embedPair i j a) (embedPair i j b) (pairPhase a b)
  have ha : ∀ k, k ∉ ({i,j} : Finset (Fin n)) → embedPair i j a k = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [embedPair, hk.1, hk.2]
  unfold pauliExpectation
  rw [← (split ({i,j} : Finset (Fin n))).symm.sum_comp (fun z =>
    star (ψ (z + embedPair i j a)) * pairPhase a b * character (embedPair i j b) z * ψ z)]
  simp only [Fintype.sum_prod_type, merge_add_supported _ _ ha]
  rw [← (pairSideEquiv i j hij).sum_comp (fun u => ∑ v : OtherSide ({i,j} : Finset (Fin n)),
    star (ψ ((split {i,j}).symm ((fun k => u k + embedPair i j a k),v))) *
      pairPhase a b * character (embedPair i j b) ((split {i,j}).symm (u,v)) *
      ψ ((split {i,j}).symm (u,v)))]
  unfold coefficient
  apply Finset.sum_congr rfl
  intro u hu
  simp only [pairSideEquiv_add, pairChar_merge]
  unfold pairReduced
  rw [Matrix.submatrix_apply, reduced_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- 标准稳定子纯态的任意两体约化纯度的四倍是非负整数。 -/
theorem stabilizer_pairPurity_quantized {n} (i j : Fin n) (hij : i ≠ j)
    (ψ : Vec n) (hψ : IsStabilizer ψ) :
    ∃ m : ℕ, 4 * cutPurity {i,j} ψ = (m : ℂ) := by
  have h : ∀ a b : Pair, ∃ m : ℕ,
      (coefficient (pairReduced i j hij ψ) a b)^2 = (m : ℂ) := by
    intro a b
    rw [pair_coefficient_expectation]
    rcases stabilizer_expectation_discrete ψ hψ (pairPauli i j hij a b) with h | h | h
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
  choose m hm using h
  refine ⟨∑ a : Pair, ∑ b : Pair, m a b, ?_⟩
  rw [← pairReduced_purity i j hij ψ, pair_parseval]
  simp only [hm, Nat.cast_sum]

theorem stabilizer_twoBodyPurity_quantized {n} (S : Finset (Fin n)) (hS : S.card = 2)
    (ψ : Vec n) (hψ : IsStabilizer ψ) :
    ∃ m : ℕ, 4 * cutPurity S ψ = (m : ℂ) := by
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hS
  exact stabilizer_pairPurity_quantized i j hij ψ hψ

lemma eleven_eighths_not_nat (m : ℕ) : (m : ℂ) ≠ 11/8 := by
  intro h
  have hc : (8 : ℂ) * (m : ℂ) = 11 := by rw [h]; norm_num
  have hn : 8*m = 11 := by exact_mod_cast hc
  omega

lemma five_fourths_not_nat (m : ℕ) : (m : ℂ) ≠ 5/4 := by
  intro h
  have hc : (4 : ℂ) * (m : ℂ) = 5 := by rw [h]; norm_num
  have hn : 4*m = 5 := by exact_mod_cast hc
  omega

/-- 此两种真实纯度均排除标准稳定子态。 -/
theorem not_stabilizer_of_pairPurity {n} (S : Finset (Fin n)) (hS : S.card = 2)
    (ψ : Vec n) (hp : cutPurity S ψ = 11/32 ∨ cutPurity S ψ = 5/16) :
    ¬ IsStabilizer ψ := by
  intro hψ
  obtain ⟨m,hm⟩ := stabilizer_twoBodyPurity_quantized S hS ψ hψ
  rcases hp with hp | hp
  · apply eleven_eighths_not_nat m
    rw [← hm, hp]
    norm_num
  · apply five_fourths_not_nat m
    rw [← hm, hp]
    norm_num

/-- 任意局域酉、全局相位与物理位重排后，纯度量化障碍仍成立。 -/
theorem not_stabilizer_LU_of_pairPurity {n} (S : Finset (Fin n)) (hS : S.card = 2)
    (ψ : Vec n) (hp : cutPurity S ψ = 11/32 ∨ cutPurity S ψ = 5/16)
    (φ : Vec n) (hφ : IsStabilizer φ)
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin n)) (c : ℂ) (hc : star c*c=1) :
    ψ ≠ c • localAction U (permute p φ) := by
  intro heq
  have hcut : cutPurity S ψ = cutPurity (S.map p.toEmbedding) φ := by
    rw [heq, cutPurity_phase S c hc, cutPurity_localAction S U hU, cutPurity_permute]
  obtain ⟨m,hm⟩ := stabilizer_twoBodyPurity_quantized (S.map p.toEmbedding)
    (by simpa using hS) φ hφ
  rw [← hcut] at hm
  rcases hp with hp | hp
  · apply eleven_eighths_not_nat m
    rw [← hm, hp]
    norm_num
  · apply five_fourths_not_nat m
    rw [← hm, hp]
    norm_num

end UnifiedEJM.StabilizerMarginal
