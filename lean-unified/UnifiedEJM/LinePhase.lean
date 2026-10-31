import UnifiedEJM.FourQubit

noncomputable section
open Complex
namespace UnifiedEJM.FiniteInvariants

/-- 前作附录的整数相位表，按0000到1111顺序。 -/
def f159 : Fin 16 → ℕ := ![0,0,0,3,0,0,1,0,0,0,0,2,0,1,3,3]

/-- a=π(1-τ)/3后的整数相位速率。 -/
def k159 : Fin 16 → ℤ := ![0,1,-1,-1,0,1,0,0,-1,2,0,1,3,3,1,0]

theorem phase159_table (x : ℂ) (k : Fin 16) :
    phase159 x k = I ^ f159 k * x ^ k159 k := by
  fin_cases k <;>
    norm_num [phase159,f159,k159,Complex.I_sq,Complex.I_pow_three,zpow_neg]

theorem phase159_unit (x : ℂ) (hu : x * star x = 1) (k : Fin 16) :
    star (phase159 x k) * phase159 x k = 1 := by
  have hI : star (I : ℂ) * I = 1 := by simp [Complex.star_def,Complex.I_mul_I]
  have hx : star x * x = 1 := by simpa only [mul_comm] using hu
  rw [phase159_table]
  simp only [star_mul,star_pow,star_zpow₀]
  calc
    _ = ((star I * I)^f159 k) * ((star x*x)^k159 k) := by
      rw [mul_pow,mul_zpow]
      ring
    _ = 1 := by rw [hI,hx]; simp

end UnifiedEJM.FiniteInvariants

