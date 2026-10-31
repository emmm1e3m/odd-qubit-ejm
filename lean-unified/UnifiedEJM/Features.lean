import UnifiedEJM.Core
import OddEJM.Counting

namespace UnifiedEJM
open OddEJM
open scoped BigOperators

/-- 实际四个线性特征的逐坐标公式。 -/
theorem features_formula {n : ℕ} (z : Bits n) :
    features z = ![coord z 0 + coord z (n-2), blockParity z 1,
      blockParity z 0, coord z 0 + coord z (n-1)] := rfl

theorem project4_add (v w : Bits 5) : project4 (v+w) = project4 v + project4 w := by
  ext j
  fin_cases j <;> simp [project4] <;> ring

def featuresHom (n : ℕ) : Bits n →+ Bits 4 where
  toFun := features
  map_zero' := by simp [features, project4]
  map_add' v w := by rw [features, compress_add, project4_add]; rfl

theorem features_surjective {n : ℕ} (hn : 5 ≤ n) : Function.Surjective (featuresHom n) := by
  intro v
  obtain ⟨z, hz⟩ := compress_surjective hn ![0, v 1, v 2, v 0, v 3]
  refine ⟨z, ?_⟩
  change project4 (compress z) = v
  rw [hz]
  ext j
  fin_cases j <;> simp [project4]

/-- 四特征每条纤维的大小适用于任意 n≥5。 -/
theorem features_fiber_card {n : ℕ} (hn : 5 ≤ n) (v : Bits 4) :
    Nat.card {z : Bits n // features z = v} = 2^(n-4) := by
  have hs := features_surjective hn
  have hker := AddSubgroup.card_ker_mul_card_of_surjective hs
  have hcards : Nat.card (featuresHom n).ker * 16 = 2^n := by
    simpa [Nat.card_fun, Nat.card_zmod] using hker
  have hpower : 2^n = 2^(n-4) * 16 := by
    rw [show n = (n-4)+4 by omega, pow_add]
    norm_num
  have hk : Nat.card (featuresHom n).ker = 2^(n-4) := by omega
  exact (Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hs v)).trans hk

theorem F_support_card : Nat.card {v : Bits 4 // F v = 1} = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- 相位支持按四特征分纤维的显式双射。 -/
def supportEquiv (n : ℕ) : {z : Bits n // q z = 1} ≃
    (Σ v : {w : Bits 4 // F w = 1}, {z : Bits n // features z = v.val}) where
  toFun z := ⟨⟨features z.val, z.property⟩, ⟨z.val, rfl⟩⟩
  invFun v := ⟨v.2.val, by
    change F (features v.2.val) = 1
    rw [v.2.property]
    exact v.1.property⟩
  left_inv z := by rfl
  right_inv v := by
    rcases v with ⟨⟨w, hw⟩, ⟨z, hz⟩⟩
    dsimp at hz
    subst w
    rfl

/-- 新核的物理支持在删除物理零点之前的精确计数。 -/
theorem q_support_card {n : ℕ} (hn : 5 ≤ n) :
    Nat.card {z : Bits n // q z = 1} = 10 * 2^(n-4) := by
  rw [Nat.card_congr (supportEquiv n), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [← Nat.card_eq_fintype_card, features_fiber_card hn]
  have hF : Fintype.card {v : Bits 4 // F v = 1} = 10 := by
    simpa only [Nat.card_eq_fintype_card] using F_support_card
  simp [hF, mul_comm]


/-- 只删除唯一物理零串后的支持大小。 -/
theorem phaseSupport_card {n : ℕ} (hn : 5 ≤ n) :
    Nat.card {z : Bits n // phaseSupport z = 1} = 10 * 2^(n-4) - 1 := by
  have hc := q_support_card hn
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc ⊢
  have hset : Finset.univ.filter (fun z : Bits n => phaseSupport z = 1) =
      (Finset.univ.filter (fun z : Bits n => q z = 1)).erase 0 := by
    apply Finset.ext
    intro z
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hz : z = 0
    · subst z
      simp [phaseSupport]
    · simp [phaseSupport, hz]
  rw [hset, Finset.card_erase_of_mem, hc]
  simp only [Finset.mem_filter, Finset.mem_univ, q_zero, true_and]

end UnifiedEJM
