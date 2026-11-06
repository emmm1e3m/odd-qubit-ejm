import UnifiedEJM.PhaseImplementation
import UnifiedEJM.DiagonalExact

namespace UnifiedEJM.PhaseImplementation
open OddEJM DiagonalDifference
open scoped BigOperators

/-- 每个单比特P相位的实际模四指数深度至多2。 -/
theorem coordinatePhase_depth {n : ℕ} (j : Fin n) :
    Depth 2 (fun z : Bits n => ((z j).val : ZMod 4)) := by
  have he : (fun z : Bits n => ((z j).val : ZMod 4)) =
      (fun _ => 1) - subsetZero {j} := by
    funext z
    rcases bit_cases (z j) with hz | hz <;>
      simp [subsetZero, hz, ZMod.val_one_eq_one_mod]
  rw [he]
  apply depth_sub (depth_const 2 1)
  simpa using (subsetZero_depths ({j} : Finset (Fin n))).2

theorem depth_finset_sum {n : ℕ} {α : Type*} (S : Finset α)
    (f : α → Phase4 n) (k : ℕ) (hf : ∀ a ∈ S, Depth k (f a)) :
    Depth k (∑ a ∈ S, f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact depth_const (n := n) k 0
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact depth_add (hf a (Finset.mem_insert_self a S))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- 所有局部P门和整体相位只占差分深度2。 -/
theorem weightPhase_depth {n : ℕ} : Depth 2 (weightPhase (n := n)) := by
  have hs := depth_finset_sum (n := n) Finset.univ
    (fun j : Fin n => fun z : Bits n => ((z j).val : ZMod 4)) 2
    (fun j _ => coordinatePhase_depth j)
  have he : weightPhase (n := n) =
      (∑ j : Fin n, fun z : Bits n => ((z j).val : ZMod 4)) - (fun _ => 1) := by
    funext z
    simp [weightPhase, weight, Nat.cast_sum, Finset.sum_apply]
  rw [he]
  exact depth_sub hs (depth_const 2 1)

theorem zeroIndicator_eq_delta {n : ℕ} : zeroIndicator (n := n) = delta := by
  funext z
  have he : (∀ j : Fin n, z j = 0) ↔ z = 0 := by
    constructor
    · intro h; funext j; exact h j
    · intro h; simp [h]
  simp [zeroIndicator, delta, subsetZero, he]

theorem referenceExponent_depth {n : ℕ} (hn : 1 ≤ n) :
    Depth (n+1) (referenceExponent (n := n)) := by
  change Depth (n+1) (weightPhase + zeroIndicator)
  rw [zeroIndicator_eq_delta]
  exact depth_add (depth_mono (by omega) weightPhase_depth) delta_depth


theorem kernelPhase_depth {n : ℕ} : Depth 4 (kernelPhase (n := n)) := by
  exact depth_pullback (featuresHom n) DiagonalDifference.kernel_depth

theorem kernelPhase_not_depth {n : ℕ} (hn : 5 ≤ n) :
    ¬Depth 3 (kernelPhase (n := n)) := by
  intro h
  exact DiagonalDifference.kernel_not_depth
    ((depth_pullback_iff (featuresHom n) (features_surjective hn)
      DiagonalDifference.kernelPhase).mp h)

theorem referenceExponent_not_depth {n : ℕ} (hn : 5 ≤ n) :
    ¬Depth n (referenceExponent (n := n)) := by
  intro h
  have ha : Depth n (weightPhase (n := n)) := depth_mono (by omega) weightPhase_depth
  have hd := depth_sub h ha
  have he : referenceExponent (n := n) - weightPhase = zeroIndicator := by
    funext z
    simp [referenceExponent]
  rw [he, zeroIndicator_eq_delta] at hd
  exact delta_not_depth (by omega) hd

theorem plusExponent_depth {n : ℕ} : Depth 4 (plusExponent (n := n)) := by
  exact depth_add (depth_mono (by omega) weightPhase_depth) kernelPhase_depth

theorem plusExponent_not_depth {n : ℕ} (hn : 5 ≤ n) :
    ¬Depth 3 (plusExponent (n := n)) := by
  intro h
  have hd := depth_sub h (depth_mono (by omega : 2 ≤ 3) (weightPhase_depth (n := n)))
  have he : plusExponent (n := n) - weightPhase = kernelPhase := by
    funext z
    simp [plusExponent]
  rw [he] at hd
  exact kernelPhase_not_depth hn hd

theorem minusExponent_depth {n : ℕ} (hn : 5 ≤ n) :
    Depth n (minusExponent (n := n)) := by
  have hq : Depth n (weightPhase (n := n) - kernelPhase) :=
    depth_sub (depth_mono (by omega) weightPhase_depth)
      (depth_mono (by omega) kernelPhase_depth)
  have he : minusExponent (n := n) =
      (weightPhase - kernelPhase) + scale 2 delta := by
    rw [← zeroIndicator_eq_delta]
    rfl
  rw [he]
  exact depth_add hq twice_delta_depth

theorem minusExponent_not_depth {n : ℕ} (hn : 5 ≤ n) :
    ¬Depth (n-1) (minusExponent (n := n)) := by
  intro h
  have hq : Depth (n-1) (weightPhase (n := n) - kernelPhase) :=
    depth_sub (depth_mono (by omega) weightPhase_depth)
      (depth_mono (by omega) kernelPhase_depth)
  have hd := depth_sub h hq
  have he : minusExponent (n := n) - (weightPhase - kernelPhase) = scale 2 delta := by
    rw [← zeroIndicator_eq_delta]
    funext z
    simp [minusExponent, scale]
  rw [he] at hd
  exact twice_delta_not_depth (by omega) hd

end UnifiedEJM.PhaseImplementation
