import UnifiedEJM.PhysicsClosurePhysical
import UnifiedEJM.PrefixCertifiedBounds
import UnifiedEJM.PhysicsSmallAll7
import UnifiedEJM.PhysicsSmallAll8
import UnifiedEJM.CosineFinal
import UnifiedEJM.GMEInvariance

noncomputable section
open OddEJM Complex
open scoped Matrix
open UnifiedEJM.Multipartite UnifiedEJM.PhysicsEntanglement

namespace UnifiedEJM.AllNEntanglement

private theorem nonsingle_cut_cards {n : ℕ} (S : Finset (Fin n))
    (hS : S ∈ cuts n) (hns : ¬SingleCut S) : 2 ≤ S.card ∧ 2 ≤ Sᶜ.card := by
  simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and] at hS
  have hSc : Sᶜ ≠ ∅ := by
    intro hz
    apply hS.2
    have hh := congrArg (fun A : Finset (Fin n) => Aᶜ) hz
    simpa using hh
  have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS.1)
  have hposc := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSc)
  unfold SingleCut at hns
  omega

/-- 任意系统长度、任意实参数下全部非单体物理割的严格纯度界。 -/
theorem larger_cut_lt_half {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (S : Finset (Fin n)) (hS : S ∈ cuts n) (hns : ¬SingleCut S) :
    (cutPurity S (UnifiedEJM.seed n t)).re < 1/2 := by
  by_cases hsmall : n < 9
  · interval_cases n
    · exact new5_larger_cut_lt_half t S hS hns
    · exact new6_larger_cut_lt_half t S hS hns
    · exact PhysicsFinite.small7_nonSingleCut_lt_half t S hS hns
    · exact PhysicsFinite.small8_nonSingleCut_lt_half t S hS hns
  · have hn9 : 9 ≤ n := by omega
    obtain ⟨hcard, hcardc⟩ := nonsingle_cut_cards S hS hns
    rcases PathCutScore.physical_cut_cases S hcard hcardc with hscore | hprefix
    · exact GraphBackground.seed_score_two_lt_half hn9 S t hscore
    · obtain ⟨k, hk, hl, hpre | hpre⟩ := hprefix
      · rw [hpre]
        exact PrefixCounts.seed_prefix_strict (by omega) hk hl t
      · rw [← cutPurity_compl, hpre]
        exact PrefixCounts.seed_prefix_strict (by omega) hk hl t

/-- 论文的全长度精确GME公式，全部非单体割前提由前述完整分类关闭。 -/
theorem seed_gme {n : ℕ} (hn : 5 ≤ n) (t : ℝ) :
    gme (by omega : 2 ≤ n) (UnifiedEJM.seed n t) =
      Real.sqrt (1 - radius n t ^ 2) :=
  seed_gme_of_bounds hn t (larger_cut_lt_half hn t)

theorem measurement_gme {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (label : Bits n) :
    gme (by omega : 2 ≤ n) (UnifiedEJM.measurement n t label) =
      Real.sqrt (1 - radius n t ^ 2) := by
  change gme (by omega : 2 ≤ n)
    (Physical.measurement (UnifiedEJM.rawPhase (anglePhase t)) label) = _
  rw [gme_measurement]
  exact seed_gme hn t

theorem measurement_gme_pos {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (label : Bits n) :
    0 < gme (by omega : 2 ≤ n) (UnifiedEJM.measurement n t label) := by
  rw [measurement_gme hn]
  exact radius_concurrence_pos hn t

theorem seed_minimizers {n : ℕ} (hn : 5 ≤ n) (t : ℝ)
    (S : Finset (Fin n)) (hS : S ∈ cuts n) :
    Real.sqrt (2 * (1 - (cutPurity S (UnifiedEJM.seed n t)).re)) =
      gme (by omega : 2 ≤ n) (UnifiedEJM.seed n t) ↔ SingleCut S := by
  apply gme_minimizers_iff (by omega) _ ((1 + radius n t ^ 2) / 2)
  · nlinarith [sq_nonneg (radius n t)]
  · have := radius_sq_lt_one hn t
    linarith
  · exact seed_singleton_purity_re hn t
  · exact larger_cut_lt_half hn t
  · exact hS

theorem measurement_minimizers {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (label : Bits n)
    (S : Finset (Fin n)) (hS : S ∈ cuts n) :
    Real.sqrt (2 * (1 - (cutPurity S (UnifiedEJM.measurement n t label)).re)) =
      gme (by omega : 2 ≤ n) (UnifiedEJM.measurement n t label) ↔ SingleCut S := by
  have hp := cutPurity_measurement (by omega : 0 < n)
    (UnifiedEJM.rawPhase (anglePhase t)) label S
  have hg := gme_measurement (by omega : 2 ≤ n)
    (UnifiedEJM.rawPhase (anglePhase t)) label
  change cutPurity S (UnifiedEJM.measurement n t label) =
    cutPurity S (UnifiedEJM.seed n t) at hp
  change gme (by omega : 2 ≤ n) (UnifiedEJM.measurement n t label) =
    gme (by omega : 2 ≤ n) (UnifiedEJM.seed n t) at hg
  rw [hp, hg]
  exact seed_minimizers hn t S hS

/-- 包括增强端点在内，整条族在每个非平凡切分上均不能分解为纯态乘积。 -/
theorem measurement_entangled {n : ℕ} (hn : 5 ≤ n) (t : ℝ) (label : Bits n)
    (S : Finset (Fin n)) (hS : S ∈ cuts n) :
    ¬ProductAcross S (UnifiedEJM.measurement n t label) :=
  gme_pos_no_product (by omega) _ (measurement_gme_pos hn t label) S hS

theorem zero_measurement_gme {n : ℕ} (hn : 5 ≤ n) (label : Bits n) :
    gme (by omega : 2 ≤ n) (UnifiedEJM.measurement n (Real.pi / 2) label) = 1 := by
  rw [measurement_gme hn, radius_eq_geometry, Geometry.radius_at_right]
  norm_num

/-- 两个零局部半径端点的GME差排除局域酉、置换及整体相位等价。 -/
theorem zero_endpoints_not_LU {n : ℕ} (hn : 6 ≤ n) (hev : Even n)
    (label label' : Bits n) (U : Fin n → Matrix Bit Bit ℂ)
    (hU : ∀ j, (U j)ᴴ * U j = 1) (p : Equiv.Perm (Fin n))
    (c : ℂ) (hc : star c * c = 1) :
    UnifiedEJM.measurement n (Real.pi / 2) label ≠
      c • localAction U (permute p (EvenFamily.measurement n (Real.pi / 2) 0 label')) := by
  apply not_LU_of_gme_ne (by omega)
    (UnifiedEJM.measurement n (Real.pi / 2) label)
    (EvenFamily.measurement n (Real.pi / 2) 0 label') _ U hU p c hc
  rw [zero_measurement_gme (by omega)]
  exact ne_of_gt (CosineEndpoint.measurement_gme_lt_one (by omega) hev label')

end UnifiedEJM.AllNEntanglement
