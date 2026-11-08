import UnifiedEJM.Multipartite

noncomputable section
open OddEJM Complex
open scoped Matrix

namespace UnifiedEJM.Multipartite

/-- 非平凡切分在比特重标下仍非平凡。 -/
theorem map_mem_cuts_iff {n : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : S.map p.toEmbedding ∈ cuts n ↔ S ∈ cuts n := by
  classical
  simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
  have hempty : S.map p.toEmbedding = ∅ ↔ S = ∅ := Finset.map_eq_empty
  have huniv : S.map p.toEmbedding = Finset.univ ↔ S = Finset.univ := by
    constructor
    · intro h
      apply Finset.eq_univ_of_forall
      intro j
      have hj : p j ∈ S.map p.toEmbedding := by rw [h]; simp
      simpa using hj
    · intro h
      subst S
      ext j
      simp
  exact and_congr (not_congr hempty) (not_congr huniv)

/-- 全部物理切分的最小值不受比特置换影响。 -/
theorem gme_permute {n : ℕ} (hn : 2 ≤ n) (p : Equiv.Perm (Fin n))
    (ψ : Vec n) : gme hn (permute p ψ) = gme hn ψ := by
  classical
  unfold gme
  apply le_antisymm
  · apply Finset.le_min'
    intro r hr
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hr
    have hmap : (S.map p.symm.toEmbedding).map p.toEmbedding = S := by
      ext j
      simp
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨S.map p.symm.toEmbedding,
      (map_mem_cuts_iff p.symm S).2 hS, by rw [cutPurity_permute, hmap]⟩
  · apply Finset.le_min'
    intro r hr
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨S.map p.toEmbedding,
      (map_mem_cuts_iff p S).2 hS, by rw [cutPurity_permute]⟩

/-- 单位整体相位不改变真正多体 concurrence。 -/
theorem gme_phase {n : ℕ} (hn : 2 ≤ n) (c : ℂ) (hc : star c * c = 1)
    (ψ : Vec n) : gme hn (c • ψ) = gme hn ψ := by
  simp only [gme, cutPurity_phase _ c hc]

/-- 任一非平凡切分均给出 concurrence 上界。 -/
theorem gme_le_cut {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n)
    (S : Finset (Fin n)) (hS : S ∈ cuts n) :
    gme hn ψ ≤ Real.sqrt (2 * (1 - (cutPurity S ψ).re)) := by
  unfold gme
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩)

/-- 不同 concurrence 排除局域酉、比特置换和整体相位后的态等价。 -/
theorem not_LU_of_gme_ne {n : ℕ} (hn : 2 ≤ n) (ψ φ : Vec n)
    (h : gme hn ψ ≠ gme hn φ)
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin n)) (c : ℂ) (hc : star c * c = 1) :
    ψ ≠ c • localAction U (permute p φ) := by
  intro heq
  apply h
  rw [heq, gme_phase _ _ hc, gme_localAction _ U hU, gme_permute]

end UnifiedEJM.Multipartite
