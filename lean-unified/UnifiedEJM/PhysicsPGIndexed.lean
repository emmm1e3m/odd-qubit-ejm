import UnifiedEJM.PhysicsIndexed

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

/-- 与PG余弦截面相同的原始相位。 -/
def pgRaw {n : ℕ} (u : ℂ) (z : Bits n) : ℂ :=
  if z = 0 then 1 else -I * I ^ weight z * u ^ (EvenWalsh.qA z).val

@[simp] theorem gphase_pg_complex {n : ℕ} (u : G) (z : Bits n) :
    ((gphase EvenWalsh.qA u z : G) : ℂ) = pgRaw (u : ℂ) z := by
  by_cases hz : z = 0 <;>
    simp [gphase, pgRaw, hz, map_mul, map_neg, map_pow, gi_complex]

theorem pg_raw_affine {n : ℕ} (u : ℂ) (z : Bits n) :
    pgRaw u z = ((gphase EvenWalsh.qA 0 z : G) : ℂ) +
      u * (((gphase EvenWalsh.qA 1 z : G) : ℂ) - ((gphase EvenWalsh.qA 0 z : G) : ℂ)) := by
  simp only [gphase_pg_complex, map_zero, map_one]
  by_cases hz : z = 0
  · simp [pgRaw, hz]
  · rcases bit_cases (EvenWalsh.qA z) with h | h <;>
      simp [pgRaw, hz, h, ZMod.val_one_eq_one_mod] <;> ring

theorem pg_physical_seed_affine {n : ℕ} (u : ℂ) (z : Bits n) :
    Physical.seed (pgRaw u) z = scale n *
      (((coeffA EvenWalsh.qA z : G) : ℂ) + u * ((coeffB EvenWalsh.qA z : G) : ℂ)) := by
  simp only [Physical.seed, circuit, chain, hadamardAt]
  rw [pg_raw_affine u, pg_raw_affine u]
  simp only [scale, coeffA, coeffB, gnumerator, map_add, map_sub, map_mul,
    gsign_complex]
  ring

theorem pg_seed_eq (n : ℕ) (t : ℝ) :
    EvenFamily.seed n t 0 = Physical.seed (pgRaw (anglePhase t)) := by
  change Physical.seed (EvenFamily.diagonal n t 0) = _
  apply congrArg Physical.seed
  funext z
  simp only [EvenFamily.diagonal, EvenRaw.raw, EvenRaw.background]
  simp [anglePhase, pgRaw, mul_assoc]

theorem pgseed6_index (u : ℂ) (k : Fin 64) :
    Physical.seed (pgRaw u) (decode6 k) =
      scale 6 * ((pg6A k : ℂ) + u * (pg6B k : ℂ)) := by
  rw [pg_physical_seed_affine, pg6A_checked, pg6B_checked]

theorem pgcut6_laurent (mask : Fin 64) (u : ℂ) (hu : u * star u = 1) :
    Multipartite.cutPurity (cutSet 6 mask) (Physical.seed (pgRaw u)) =
      (16384 : ℂ)⁻¹ * laurentEval (gCoefficients (fastMix 6 mask) pg6A pg6B) u := by
  rw [Multipartite.cutPurity_eq_swap_sum]
  change swapPurity (cutSet 6 mask) (Physical.seed (pgRaw u)) = _
  unfold swapPurity
  rw [← indexEquiv6.sum_comp]
  simp_rw [← indexEquiv6.sum_comp]
  change (∑ i : Fin 64, ∑ j : Fin 64,
    Physical.seed (pgRaw u) (decode6 i) *
    Physical.seed (pgRaw u) (decode6 j) *
    star (Physical.seed (pgRaw u) (splice (cutSet 6 mask) (decode6 i) (decode6 j))) *
    star (Physical.seed (pgRaw u) (splice (cutSet 6 mask) (decode6 j) (decode6 i)))) = _
  simp_rw [show ∀ i j : Fin 64, splice (cutSet 6 mask) (decode6 i) (decode6 j) =
    decode6 (fastMix 6 mask i j) from fun i j => (mix6_checked mask i j).symm]
  simp_rw [pgseed6_index]
  have factor : ∀ i j : Fin 64,
      (scale 6 * ((pg6A i : ℂ)+u*(pg6B i : ℂ))) *
      (scale 6 * ((pg6A j : ℂ)+u*(pg6B j : ℂ))) *
      star (scale 6 * ((pg6A (fastMix 6 mask i j) : ℂ)+u*(pg6B (fastMix 6 mask i j) : ℂ))) *
      star (scale 6 * ((pg6A (fastMix 6 mask j i) : ℂ)+u*(pg6B (fastMix 6 mask j i) : ℂ))) =
      (scale 6 * star (scale 6))^2 *
      (((pg6A i : ℂ)+u*(pg6B i : ℂ))*((pg6A j : ℂ)+u*(pg6B j : ℂ))*
      star ((pg6A (fastMix 6 mask i j) : ℂ)+u*(pg6B (fastMix 6 mask i j) : ℂ))*
      star ((pg6A (fastMix 6 mask j i) : ℂ)+u*(pg6B (fastMix 6 mask j i) : ℂ))) := by
    intros; simp only [star_mul]; ring
  simp_rw [factor]
  simp_rw [← Finset.mul_sum]
  rw [affine_swap_sum _ _ _ _ hu, scale_norm]
  norm_num


end UnifiedEJM.PhysicsFinite

