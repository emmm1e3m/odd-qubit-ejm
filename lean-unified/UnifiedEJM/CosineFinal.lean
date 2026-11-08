import UnifiedEJM.CosineReduced

noncomputable section
open scoped BigOperators Matrix
open Complex OddEJM
open UnifiedEJM.Multipartite UnifiedEJM.StabilizerMarginal

namespace UnifiedEJM.CosineEndpoint

theorem exponent_purity {n : ℕ} (hn : 4≤n) (hev : Even n) :
    (((2:ℂ)^(n/2-2))⁻¹)^2/2 = (2:ℂ)^((3:ℤ)-n) := by
  have he : 2*(n/2-2)+1 = n-3 := by have hp := Nat.even_iff.mp hev; omega
  have hz : (3:ℤ)-n = -((n-3:ℕ):ℤ) := by omega
  rw [hz,zpow_neg,zpow_natCast,← inv_pow,← pow_mul,div_eq_mul_inv,← pow_succ]
  rw [show (n/2-2)*2+1 = n-3 by omega]
  rw [inv_pow]

theorem exponent_gme {n : ℕ} (hn : 4≤n) (hev : Even n) :
    (((2:ℝ)^(n/2-2))⁻¹)^2 = (2:ℝ)^((4:ℤ)-n) := by
  have he : 2*(n/2-2) = n-4 := by have hp := Nat.even_iff.mp hev; omega
  have hz : (4:ℤ)-n = -((n-4:ℕ):ℤ) := by omega
  rw [hz,zpow_neg,zpow_natCast,← inv_pow,← pow_mul]
  rw [show (n/2-2)*2 = n-4 by omega]
  rw [inv_pow]

/-- 论文所述全部偶数n≥4的真实第一对偏迹纯度。 -/
theorem seed_purity_exact {n : ℕ} (hn : 4≤n) (hev : Even n) :
    cutPurity ({⟨0,by omega⟩,⟨1,by omega⟩}:Finset (Fin n))
      (EvenFamily.seed n (Real.pi/2) 0) = (1/2:ℂ)+(2:ℂ)^((3:ℤ)-n) := by
  rw [pair_purity hn hev,exponent_purity hn hev]

theorem measurement_purity_exact {n : ℕ} (hn : 4≤n) (hev : Even n) (label : Bits n) :
    cutPurity ({⟨0,by omega⟩,⟨1,by omega⟩}:Finset (Fin n))
      (EvenFamily.measurement n (Real.pi/2) 0 label) = (1/2:ℂ)+(2:ℂ)^((3:ℤ)-n) := by
  rw [measurement_purity hn hev,exponent_purity hn hev]

theorem measurement_gme_exact_bound {n : ℕ} (hn : 4≤n) (hev : Even n)
    (label : Bits n) :
    gme (by omega : 2≤n) (EvenFamily.measurement n (Real.pi/2) 0 label) ≤
      Real.sqrt (1-(2:ℝ)^((4:ℤ)-n)) := by
  simpa only [exponent_gme hn hev] using measurement_gme_bound hn hev label

theorem measurement_gme_lt_one {n : ℕ} (hn : 4≤n) (hev : Even n)
    (label : Bits n) :
    gme (by omega : 2≤n) (EvenFamily.measurement n (Real.pi/2) 0 label) < 1 := by
  rw [show EvenFamily.measurement n (Real.pi/2) 0 label =
    Physical.measurement (EvenFamily.diagonal n (Real.pi/2) 0) label from rfl,
    gme_measurement]
  exact seed_gme_lt_one hn hev

end UnifiedEJM.CosineEndpoint
