import UnifiedEJM.GraphBackground

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

theorem bit_phase_affine (u : ℂ) (b : Bit) :
    u ^ b.val = (1+u)/2 + (1-u)/2 * bitSign b := by
  rcases OddEJM.bit_cases b with rfl | rfl <;>
    norm_num [bitSign, ZMod.val_one_eq_one_mod] <;> ring

/-- 原始四特征相位的Fourier系数就是delta与F的Walsh系数的线性组合。 -/
theorem fourier_phase (u : ℂ) (h : Bits 4) :
    fourier (fun x => u ^ (F x).val) h =
      (1+u)/2 * (if h=0 then 1 else 0) + (1-u)/2 * fourier (fun x => bitSign (F x)) h := by
  unfold fourier
  simp_rw [bit_phase_affine]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  have hs : (∑ x : Bits 4, (1-u)/2 * bitSign (F x) * character h x) =
      (1-u)/2 * ∑ x, bitSign (F x) * character h x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hs, character_sum]
  by_cases hh : h=0 <;> simp only [hh, if_true, if_false] <;> ring

theorem featureMask_last {n : ℕ} (hn : 5≤n) (h : Bits 4) :
    coord (featureMask n h) (n-1) = h 3 := by
  simp only [coord, dif_pos (show n-1<n by omega), featureMask, features,
    compress_last hn, project4, unitBit, dot, Fin.sum_univ_succ]
  norm_num

/-- 相对相位准确来自第四逻辑位h_s。 -/
theorem graphCoefficient_formula {n : ℕ} (hn : 5≤n) (u : ℂ) (h : Bits 4) :
    graphCoefficient n u h = (-I)^(h 3).val *
      ((1+u)/2 * (if h=0 then 1 else 0) +
        (1-u)/2 * fourier (fun x => bitSign (F x)) h) := by
  rw [graphCoefficient, featureMask_last hn, fourier_phase]
  ring

end UnifiedEJM.GraphBackground
