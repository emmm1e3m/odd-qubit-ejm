import UnifiedEJM.Multipartite
import OddEJM.Character

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open OddEJM Complex

namespace UnifiedEJM.CutPauliParseval
open UnifiedEJM.Multipartite

/-- 有限物理指标的位串重新编号；只用于复用已有字符正交定理。 -/
def bitsEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] : (ι → Bit) ≃ Bits (Fintype.card ι) where
  toFun z k := z ((Fintype.equivFin ι).symm k)
  invFun z j := z (Fintype.equivFin ι j)
  left_inv z := by funext j; simp
  right_inv z := by funext k; simp

def finiteCharacter {ι : Type*} [Fintype ι] [DecidableEq ι] (b z : ι → Bit) : ℂ :=
  bitSign (∑ j, b j * z j)

theorem finiteCharacter_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b z : ι → Bit) :
    finiteCharacter b z = character (bitsEquiv b) (bitsEquiv z) := by
  unfold finiteCharacter character dot bitsEquiv
  congr 1
  exact ((Fintype.equivFin ι).symm.sum_comp (fun j => b j * z j)).symm

@[simp] theorem finiteCharacter_star {ι : Type*} [Fintype ι] [DecidableEq ι] (b z : ι → Bit) :
    star (finiteCharacter b z) = finiteCharacter b z := bitSign_star _

theorem finiteCharacter_symm {ι : Type*} [Fintype ι] [DecidableEq ι] (b z : ι → Bit) :
    finiteCharacter b z = finiteCharacter z b := by
  simp only [finiteCharacter, mul_comm]

/-- 任意有限指标的字符正交直接继承已验证的Bits版本。 -/
theorem finiteCharacter_orthogonality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z w : ι → Bit) :
    (∑ b : ι → Bit, finiteCharacter b z * finiteCharacter b w) =
      if z = w then (2 : ℂ) ^ Fintype.card ι else 0 := by
  classical
  calc
    _ = ∑ b : ι → Bit, character (bitsEquiv z) (bitsEquiv b) *
        character (bitsEquiv w) (bitsEquiv b) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [finiteCharacter_symm b z, finiteCharacter_symm b w,
        finiteCharacter_eq, finiteCharacter_eq]
    _ = ∑ b : Bits (Fintype.card ι), character (bitsEquiv z) b *
        character (bitsEquiv w) b :=
      (bitsEquiv (ι := ι)).sum_comp (fun b =>
        character (bitsEquiv z) b * character (bitsEquiv w) b)
    _ = _ := by
      simpa only [character_star, Equiv.apply_eq_iff_eq] using
        character_orthogonality (bitsEquiv z) (bitsEquiv w)

def finiteFourier {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bit) → ℂ) (b : ι → Bit) : ℂ :=
  ∑ z, finiteCharacter b z * f z

/-- 未归一化Walsh变换的Parseval，适用于任意复值函数。 -/
theorem finiteFourier_parseval {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bit) → ℂ) :
    (∑ b, star (finiteFourier f b) * finiteFourier f b) =
      (2 : ℂ) ^ Fintype.card ι * ∑ z, star (f z) * f z := by
  classical
  calc
    _ = ∑ b, ∑ z, ∑ w,
        finiteCharacter b z * finiteCharacter b w * (star (f w) * f z) := by
      simp only [finiteFourier, star_sum, star_mul, finiteCharacter_star,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = ∑ z, ∑ w, (∑ b, finiteCharacter b z * finiteCharacter b w) *
        (star (f w) * f z) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      simp only [finiteCharacter_orthogonality]
      simp [ite_mul, Finset.mul_sum]

/-- 不附加Hermitian相位的Pauli系数；用模平方统一处理反Hermitian情形。 -/
def matrixCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (ι → Bit) (ι → Bit) ℂ) (a b : ι → Bit) : ℂ :=
  finiteFourier (fun z => R z (z + a)) b

/-- 任意有限比特指标的Hermitian矩阵Pauli Parseval。 -/
theorem matrix_parseval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (ι → Bit) (ι → Bit) ℂ) (hR : Rᴴ = R) :
    (2 : ℂ) ^ Fintype.card ι * Matrix.trace (R * R) =
      ∑ a, ∑ b, star (matrixCoefficient R a b) * matrixCoefficient R a b := by
  classical
  have hstar (z w : ι → Bit) : star (R z w) = R w z :=
    congrArg (fun M : Matrix (ι → Bit) (ι → Bit) ℂ => M w z) hR
  symm
  calc
    _ = (2 : ℂ) ^ Fintype.card ι *
        ∑ a : ι → Bit, ∑ z : ι → Bit, star (R z (z + a)) * R z (z + a) := by
      simp only [matrixCoefficient, finiteFourier_parseval, Finset.mul_sum]
    _ = (2 : ℂ) ^ Fintype.card ι *
        ∑ z : ι → Bit, ∑ w : ι → Bit, star (R z w) * R z w := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      exact Equiv.sum_comp (Equiv.addLeft z) (fun w => star (R z w) * R z w)
    _ = _ := by
      congr 1
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      rw [hstar]
      ring

/-- 子系统位串按实际物理位置零延拓。 -/
def embedSide {n : ℕ} (S : Finset (Fin n)) (a : Side S) : Bits n :=
  fun j => if hj : j ∈ S then a ⟨j, hj⟩ else 0

def Supported {n : ℕ} (S : Finset (Fin n)) (a : Bits n) : Prop :=
  ∀ j, j ∉ S → a j = 0

instance {n : ℕ} (S : Finset (Fin n)) (a : Bits n) : Decidable (Supported S a) :=
  inferInstanceAs (Decidable (∀ j, j ∉ S → a j = 0))

@[simp] theorem embedSide_apply {n : ℕ} (S : Finset (Fin n)) (a : Side S)
    (j : {j // j ∈ S}) : embedSide S a j = a j := by
  simp [embedSide, j.property]

theorem embedSide_supported {n : ℕ} (S : Finset (Fin n)) (a : Side S) :
    Supported S (embedSide S a) := by
  intro j hj
  simp [embedSide, hj]

theorem merge_add_embedSide {n : ℕ} (S : Finset (Fin n)) (u a : Side S)
    (v : OtherSide S) :
    (split S).symm (u, v) + embedSide S a = (split S).symm (u + a, v) := by
  funext j
  by_cases hj : j ∈ S <;>
    simp [split, Equiv.piEquivPiSubtypeProd, embedSide, hj]

theorem character_embedSide_merge {n : ℕ} (S : Finset (Fin n)) (b u : Side S)
    (v : OtherSide S) :
    character (embedSide S b) ((split S).symm (u, v)) = finiteCharacter b u := by
  unfold character dot finiteCharacter
  congr 1
  calc
    _ = ∑ j ∈ S, embedSide S b j * ((split S).symm (u, v)) j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j hj hnot
      simp [embedSide, hnot]
    _ = ∑ j : {j // j ∈ S}, b j * u j := by
      rw [← Finset.sum_coe_sort (f := fun j =>
        embedSide S b j * ((split S).symm (u, v)) j) (s := S)]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [embedSide_apply, merge_left]

/-- 每个子系统Pauli系数等于原始全系统振幅的真实有限和期望。 -/
theorem matrixCoefficient_reduced {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n)
    (a b : Side S) :
    matrixCoefficient (reduced S ψ) a b =
      pauliExpectation ψ (embedSide S a) (embedSide S b) 1 := by
  classical
  unfold pauliExpectation
  rw [← (split S).symm.sum_comp (fun z =>
    star (ψ (z + embedSide S a)) * 1 * character (embedSide S b) z * ψ z)]
  simp only [Fintype.sum_prod_type, merge_add_embedSide, character_embedSide_merge, mul_one]
  unfold matrixCoefficient finiteFourier
  apply Finset.sum_congr rfl
  intro u hu
  dsimp only
  simp only [Multipartite.reduced, Matrix.mul_apply, Matrix.conjTranspose_apply,
    reshape, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- 真实偏迹的Pauli Parseval；ψ无需预先归一化，S允许空集及全集。 -/
theorem cutPurity_pauli_side {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    (2 : ℂ) ^ S.card * cutPurity S ψ =
      ∑ a : Side S, ∑ b : Side S,
        star (pauliExpectation ψ (embedSide S a) (embedSide S b) 1) *
          pauliExpectation ψ (embedSide S a) (embedSide S b) 1 := by
  have hR : (reduced S ψ)ᴴ = reduced S ψ := by
    simp [Multipartite.reduced, Matrix.conjTranspose_mul]
  have hp := matrix_parseval (reduced S ψ) hR
  simp only [matrixCoefficient_reduced] at hp
  simpa only [Fintype.card_coe, cutPurity,
    PurityInvariant.purity, Multipartite.reduced] using hp

/-- 零延拓与全位串支持子类型之间的双射。 -/
def sideSupportedEquiv {n : ℕ} (S : Finset (Fin n)) :
    Side S ≃ {a : Bits n // Supported S a} where
  toFun a := ⟨embedSide S a, embedSide_supported S a⟩
  invFun a j := a.val j
  left_inv a := by funext j; simp
  right_inv a := by
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ S
    · simp [embedSide, hj]
    · simp [embedSide, hj, a.property j hj]

theorem sum_embedSide {n : ℕ} (S : Finset (Fin n)) (f : Bits n → ℂ) :
    (∑ a : Side S, f (embedSide S a)) =
      ∑ a : Bits n, if Supported S a then f a else 0 := by
  classical
  calc
    _ = ∑ a : {a : Bits n // Supported S a}, f a :=
      (sideSupportedEquiv S).sum_comp (fun a => f a)
    _ = _ := by
      symm
      exact Finset.sum_congr_set {a : Bits n | Supported S a}
        (fun a => if Supported S a then f a else 0) (fun a => f a)
        (by intro a ha; change Supported S a at ha; simp [ha])
        (by intro a ha; change ¬ Supported S a at ha; simp [ha])

/-- 全物理位串过滤形式，直接供图码支持约束使用。 -/
theorem cutPurity_pauli_supported {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    (2 : ℂ) ^ S.card * cutPurity S ψ =
      ∑ a : Bits n, ∑ b : Bits n,
        if Supported S a ∧ Supported S b then
          star (pauliExpectation ψ a b 1) * pauliExpectation ψ a b 1 else 0 := by
  classical
  rw [cutPurity_pauli_side]
  calc
    _ = ∑ a : Side S, ∑ b : Bits n,
        if Supported S b then
          star (pauliExpectation ψ (embedSide S a) b 1) *
            pauliExpectation ψ (embedSide S a) b 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_embedSide S (fun b =>
        star (pauliExpectation ψ (embedSide S a) b 1) *
          pauliExpectation ψ (embedSide S a) b 1)
    _ = ∑ a : Bits n, if Supported S a then
        (∑ b : Bits n, if Supported S b then
          star (pauliExpectation ψ a b 1) * pauliExpectation ψ a b 1 else 0) else 0 :=
      sum_embedSide S (fun a => ∑ b : Bits n, if Supported S b then
        star (pauliExpectation ψ a b 1) * pauliExpectation ψ a b 1 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : Supported S a <;> simp [h]

/-- 除以真实子系统维数，得到任意物理分割的完整纯度公式。 -/
theorem cutPurity_pauli_supported_div {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    cutPurity S ψ = ((2 : ℂ) ^ S.card)⁻¹ *
      ∑ a : Bits n, ∑ b : Bits n,
        if Supported S a ∧ Supported S b then
          star (pauliExpectation ψ a b 1) * pauliExpectation ψ a b 1 else 0 := by
  apply mul_left_cancel₀ (pow_ne_zero S.card (by norm_num : (2 : ℂ) ≠ 0))
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero S.card (by norm_num : (2 : ℂ) ≠ 0)), one_mul]
  exact cutPurity_pauli_supported S ψ

/-- 与通常的绝对值平方记法完全一致的实际分割纯度公式。 -/
theorem cutPurity_pauli_supported_norm {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    cutPurity S ψ = ((2 : ℂ) ^ S.card)⁻¹ *
      ∑ a : Bits n, ∑ b : Bits n,
        if Supported S a ∧ Supported S b then
          ((‖pauliExpectation ψ a b 1‖ ^ 2 : ℝ) : ℂ) else 0 := by
  rw [cutPurity_pauli_supported_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs
  · simpa only [Complex.star_def, Complex.ofReal_pow] using
      Complex.conj_mul' (pauliExpectation ψ a b 1)
  · rfl

end UnifiedEJM.CutPauliParseval

