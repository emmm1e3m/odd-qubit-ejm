import UnifiedEJM.GraphLocalConstraints
import UnifiedEJM.CutPauliParseval

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

attribute [local instance] Classical.propDecidable

private theorem supported_iff {n : ℕ} (S : Finset (Fin n)) (a : Bits n) :
    CutPauliParseval.Supported S a ↔ SupportedOn S a := Iff.rfl

private theorem sum_via_injective {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (g : β → ℂ)
    (hz : ∀ b, (∀ a, f a≠b) → g b=0) :
    (∑ b, g b) = ∑ a, g (f a) := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image f, g b := by
      symm
      apply Finset.sum_subset (by simp)
      intro b _ hb
      apply hz b
      intro a he
      apply hb
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, he⟩
    _ = _ := Finset.sum_image (by intro a _ b _ he; exact hf he)

theorem physicalBackground_pauli_square {n : ℕ} (hn : 5≤n) (u : ℂ)
    (a : Bits n) (d : Bits 4) :
    star (pauliExpectation (physicalBackground n u) a (graphMask a+graphWord n d) 1) *
      pauliExpectation (physicalBackground n u) a (graphMask a+graphWord n d) 1 =
        (Complex.normSq (codeCorrelation (physicalCoefficients n u) d (graphFeature a)) : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  congr 1
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    physicalBackground_pauli_feasible_norm hn]

theorem supported_pauli_sum {n : ℕ} (hn : 5≤n) (S : Finset (Fin n)) (u : ℂ)
    (a : Bits n) (ha : SupportedOn S a) :
    (∑ b : Bits n, if SupportedOn S b then
      star (pauliExpectation (physicalBackground n u) a b 1) *
        pauliExpectation (physicalBackground n u) a b 1 else 0) =
      ∑ d : Bits 4, if LocalConstraints S d a then
        (Complex.normSq (codeCorrelation (physicalCoefficients n u) d (graphFeature a)) : ℂ)
        else 0 := by
  classical
  have hf : Function.Injective (fun d : Bits 4 => graphMask a+graphWord n d) := by
    intro d e he
    exact graphWord_injective hn (add_left_cancel he)
  rw [sum_via_injective (fun d => graphMask a+graphWord n d) hf]
  · apply Finset.sum_congr rfl
    intro d _
    have hs : SupportedOn S (graphMask a+graphWord n d) ↔ LocalConstraints S d a := by
      rw [support_graphMask_add_word_iff S a ha d]
      simp only [LocalConstraints, rowWord_dot, coord, Fin.isLt, dif_pos]
    rw [hs]
    split_ifs
    · exact physicalBackground_pauli_square hn u a d
    · rfl
  · intro b hb
    have he := physicalBackground_pauli_infeasible hn u a b (fun d => Ne.symm (hb d))
    simp [he]

/-- 真实物理偏迹经Pauli正交性压为(d,v_A)的静态全赋值和。 -/
theorem physicalBackground_purity_assignments {n : ℕ} (hn : 5≤n)
    (S : Finset (Fin n)) (u : ℂ) :
    Multipartite.cutPurity S (physicalBackground n u) =
      ((2:ℂ)^S.card)⁻¹ * ∑ d : Bits 4, ∑ a : Bits n,
        if SupportedOn S a ∧ LocalConstraints S d a then
          (Complex.normSq (codeCorrelation (physicalCoefficients n u) d (graphFeature a)) : ℂ)
        else 0 := by
  classical
  rw [CutPauliParseval.cutPurity_pauli_supported_div]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [supported_iff]
  by_cases ha : SupportedOn S a
  · simpa [ha] using supported_pauli_sum hn S u a ha
  · simp [ha]

private theorem group_charge {n : ℕ} (S : Finset (Fin n)) (d : Bits 4)
    (score : Bits 4 → ℂ) :
    (∑ a : Bits n, if SupportedOn S a ∧ LocalConstraints S d a then score (graphFeature a) else 0) =
      ∑ k : Bits 4, (∑ a : Bits n,
        if SupportedOn S a ∧ LocalConstraints S d a ∧ graphFeature a=k then (1:ℂ) else 0) * score k := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : SupportedOn S a ∧ LocalConstraints S d a
  · simp [ha.1, ha.2]
  · have hz : ∀k, ¬(SupportedOn S a ∧ LocalConstraints S d a ∧ graphFeature a=k) := by
      intro k hk
      exact ha ⟨hk.1,hk.2.1⟩
    simp [ha, hz]

/-- 从原始H/CNOT振幅到十六乘十六静态加权签名的完整纯度桥。 -/
theorem physicalBackground_purity_weighted {n : ℕ} (hn : 5≤n)
    (S : Finset (Fin n)) (u : ℂ) :
    Multipartite.cutPurity S (physicalBackground n u) =
      ∑ d : Bits 4, ∑ k : Bits 4, (physicalWeight S d k : ℂ) *
        (Complex.normSq (codeCorrelation (physicalCoefficients n u) d k) : ℂ) := by
  classical
  rw [physicalBackground_purity_assignments hn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [group_charge S d (fun k =>
    (Complex.normSq (codeCorrelation (physicalCoefficients n u) d k) : ℂ))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hw : (physicalWeight S d k : ℂ) =
      ((2:ℂ)^S.card)⁻¹ * ∑ a : Bits n,
        if SupportedOn S a ∧ LocalConstraints S d a ∧ graphFeature a=k then (1:ℂ) else 0 := by
    simp [physicalWeight, one_div, inv_pow]
  rw [hw]
  ring

end UnifiedEJM.GraphBackground
