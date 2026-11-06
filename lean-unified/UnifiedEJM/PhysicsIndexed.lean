import UnifiedEJM.PhysicsLaurent

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- 最高位对应第一个物理比特。 -/
def cutSet (n : ℕ) (mask : Fin (2^n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => mask.val.testBit (n-1-j.val))

/-- 位运算只用于可执行重排，其与真实物理拼接另外逐项证明。 -/
def fastMix (n : ℕ) (mask i j : Fin (2^n)) : Fin (2^n) :=
  ⟨((i.val &&& mask.val) ||| (j.val &&& (2^n-1-mask.val))) % 2^n,
    Nat.mod_lt _ (by positivity)⟩

def bitDecode (n : ℕ) (k : Fin (2^n)) : Bits n :=
  fun j => if k.val.testBit (n-1-j.val) then 1 else 0

theorem fastMix_bit (n : ℕ) (mask i j : Fin (2^n)) (k : ℕ) (hk : k < n) :
    (fastMix n mask i j).val.testBit k =
      if mask.val.testBit k then i.val.testBit k else j.val.testBit k := by
  simp only [fastMix, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_and,
    hk, decide_true, Bool.true_and]
  rw [show 2^n-1-mask.val = 2^n-(mask.val+1) by omega,
    Nat.testBit_two_pow_sub_succ mask.isLt]
  cases hm : mask.val.testBit k <;> simp [hm, hk]

theorem bitDecode_mix (n : ℕ) (mask i j : Fin (2^n)) :
    bitDecode n (fastMix n mask i j) =
      splice (cutSet n mask) (bitDecode n i) (bitDecode n j) := by
  funext k
  have hk : n-1-k.val < n := by have := k.isLt; omega
  simp only [bitDecode, fastMix_bit n mask i j _ hk, splice, cutSet,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases hm : mask.val.testBit (n-1-k.val) <;> simp [hm]

theorem decode5_bit : ∀ k : Fin 32, decode5 k = bitDecode 5 k := by decide +kernel
theorem decode6_bit : ∀ k : Fin 64, decode6 k = bitDecode 6 k := by decide +kernel

theorem mix5_checked (mask i j : Fin 32) :
    decode5 (fastMix 5 mask i j) = splice (cutSet 5 mask) (decode5 i) (decode5 j) := by
  simp_rw [decode5_bit]
  exact bitDecode_mix 5 mask i j

theorem mix6_checked (mask i j : Fin 64) :
    decode6 (fastMix 6 mask i j) = splice (cutSet 6 mask) (decode6 i) (decode6 j) := by
  simp_rw [decode6_bit]
  exact bitDecode_mix 6 mask i j

theorem seed5_index (u : ℂ) (k : Fin 32) :
    Physical.seed (UnifiedEJM.rawPhase u) (decode5 k) =
      scale 5 * ((new5A k : ℂ) + u * (new5B k : ℂ)) := by
  rw [physical_seed_affine, new5A_checked, new5B_checked]

theorem seed6_index (u : ℂ) (k : Fin 64) :
    Physical.seed (UnifiedEJM.rawPhase u) (decode6 k) =
      scale 6 * ((new6A k : ℂ) + u * (new6B k : ℂ)) := by
  rw [physical_seed_affine, new6A_checked, new6B_checked]

theorem cut5_laurent (mask : Fin 32) (u : ℂ) (hu : u * star u = 1) :
    Multipartite.cutPurity (cutSet 5 mask) (Physical.seed (UnifiedEJM.rawPhase u)) =
      (4096 : ℂ)⁻¹ * laurentEval (gCoefficients (fastMix 5 mask) new5A new5B) u := by
  rw [Multipartite.cutPurity_eq_swap_sum]
  change swapPurity (cutSet 5 mask) (Physical.seed (UnifiedEJM.rawPhase u)) = _
  unfold swapPurity
  rw [← indexEquiv5.sum_comp]
  simp_rw [← indexEquiv5.sum_comp]
  change (∑ i : Fin 32, ∑ j : Fin 32,
    Physical.seed (UnifiedEJM.rawPhase u) (decode5 i) *
    Physical.seed (UnifiedEJM.rawPhase u) (decode5 j) *
    star (Physical.seed (UnifiedEJM.rawPhase u) (splice (cutSet 5 mask) (decode5 i) (decode5 j))) *
    star (Physical.seed (UnifiedEJM.rawPhase u) (splice (cutSet 5 mask) (decode5 j) (decode5 i)))) = _
  simp_rw [show ∀ i j : Fin 32, splice (cutSet 5 mask) (decode5 i) (decode5 j) =
    decode5 (fastMix 5 mask i j) from fun i j => (mix5_checked mask i j).symm]
  simp_rw [seed5_index]
  have factor : ∀ i j : Fin 32,
      (scale 5 * ((new5A i : ℂ)+u*(new5B i : ℂ))) *
      (scale 5 * ((new5A j : ℂ)+u*(new5B j : ℂ))) *
      star (scale 5 * ((new5A (fastMix 5 mask i j) : ℂ)+u*(new5B (fastMix 5 mask i j) : ℂ))) *
      star (scale 5 * ((new5A (fastMix 5 mask j i) : ℂ)+u*(new5B (fastMix 5 mask j i) : ℂ))) =
      (scale 5 * star (scale 5))^2 *
      (((new5A i : ℂ)+u*(new5B i : ℂ))*((new5A j : ℂ)+u*(new5B j : ℂ))*
      star ((new5A (fastMix 5 mask i j) : ℂ)+u*(new5B (fastMix 5 mask i j) : ℂ))*
      star ((new5A (fastMix 5 mask j i) : ℂ)+u*(new5B (fastMix 5 mask j i) : ℂ))) := by
    intros; simp only [star_mul]; ring
  simp_rw [factor]
  simp_rw [← Finset.mul_sum]
  rw [affine_swap_sum _ _ _ _ hu, scale_norm]
  norm_num

theorem cut6_laurent (mask : Fin 64) (u : ℂ) (hu : u * star u = 1) :
    Multipartite.cutPurity (cutSet 6 mask) (Physical.seed (UnifiedEJM.rawPhase u)) =
      (16384 : ℂ)⁻¹ * laurentEval (gCoefficients (fastMix 6 mask) new6A new6B) u := by
  rw [Multipartite.cutPurity_eq_swap_sum]
  change swapPurity (cutSet 6 mask) (Physical.seed (UnifiedEJM.rawPhase u)) = _
  unfold swapPurity
  rw [← indexEquiv6.sum_comp]
  simp_rw [← indexEquiv6.sum_comp]
  change (∑ i : Fin 64, ∑ j : Fin 64,
    Physical.seed (UnifiedEJM.rawPhase u) (decode6 i) *
    Physical.seed (UnifiedEJM.rawPhase u) (decode6 j) *
    star (Physical.seed (UnifiedEJM.rawPhase u) (splice (cutSet 6 mask) (decode6 i) (decode6 j))) *
    star (Physical.seed (UnifiedEJM.rawPhase u) (splice (cutSet 6 mask) (decode6 j) (decode6 i)))) = _
  simp_rw [show ∀ i j : Fin 64, splice (cutSet 6 mask) (decode6 i) (decode6 j) =
    decode6 (fastMix 6 mask i j) from fun i j => (mix6_checked mask i j).symm]
  simp_rw [seed6_index]
  have factor : ∀ i j : Fin 64,
      (scale 6 * ((new6A i : ℂ)+u*(new6B i : ℂ))) *
      (scale 6 * ((new6A j : ℂ)+u*(new6B j : ℂ))) *
      star (scale 6 * ((new6A (fastMix 6 mask i j) : ℂ)+u*(new6B (fastMix 6 mask i j) : ℂ))) *
      star (scale 6 * ((new6A (fastMix 6 mask j i) : ℂ)+u*(new6B (fastMix 6 mask j i) : ℂ))) =
      (scale 6 * star (scale 6))^2 *
      (((new6A i : ℂ)+u*(new6B i : ℂ))*((new6A j : ℂ)+u*(new6B j : ℂ))*
      star ((new6A (fastMix 6 mask i j) : ℂ)+u*(new6B (fastMix 6 mask i j) : ℂ))*
      star ((new6A (fastMix 6 mask j i) : ℂ)+u*(new6B (fastMix 6 mask j i) : ℂ))) := by
    intros; simp only [star_mul]; ring
  simp_rw [factor]
  simp_rw [← Finset.mul_sum]
  rw [affine_swap_sum _ _ _ _ hu, scale_norm]
  norm_num


def indexedPurity {n : ℕ} (mask : Fin (2^n)) (v : Fin (2^n) → G) : G :=
  ∑ i, ∑ j, v i * v j * star (v (fastMix n mask i j)) * star (v (fastMix n mask j i))

theorem gpurity6_index (mask : Fin 64) (u : G) :
    gpurity (cutSet 6 mask) (gnumerator (gphase UnifiedEJM.q u)) =
      indexedPurity (n := 6) mask (fun i => new6A i + u * new6B i) := by
  unfold gpurity
  rw [← indexEquiv6.sum_comp]
  simp_rw [← indexEquiv6.sum_comp]
  change (∑ i : Fin 64, ∑ j : Fin 64,
    gnumerator (gphase UnifiedEJM.q u) (decode6 i) *
    gnumerator (gphase UnifiedEJM.q u) (decode6 j) *
    star (gnumerator (gphase UnifiedEJM.q u) (splice (cutSet 6 mask) (decode6 i) (decode6 j))) *
    star (gnumerator (gphase UnifiedEJM.q u) (splice (cutSet 6 mask) (decode6 j) (decode6 i)))) = _
  simp_rw [show ∀ i j : Fin 64, splice (cutSet 6 mask) (decode6 i) (decode6 j) =
    decode6 (fastMix 6 mask i j) from fun i j => (mix6_checked mask i j).symm]
  simp only [numerator_affine, new6A_checked, new6B_checked, indexedPurity]
  rfl

end UnifiedEJM.PhysicsFinite



