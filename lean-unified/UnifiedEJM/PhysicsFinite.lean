import UnifiedEJM.Physical
import UnifiedEJM.Phase
import UnifiedEJM.EvenSeed
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

open scoped BigOperators Matrix
open OddEJM Complex
namespace UnifiedEJM.PhysicsFinite

/-- 高斯整数用于不含浮点运算的原门证书。 -/
abbrev G := GaussianInt
def gi : G := ⟨0, 1⟩
def gsign (b : Bit) : G := if b = 0 then 1 else -1
def gphase {n : ℕ} (f : Bits n → Bit) (u : G) (z : Bits n) : G :=
  if z = 0 then 1 else -gi * gi ^ weight z * u ^ (f z).val
def gnumerator {n : ℕ} (p : Bits n → G) (z : Bits n) : G :=
  p (setBit (difference z) (n-1) 0) +
    gsign (coord (difference z) (n-1)) * p (setBit (difference z) (n-1) 1)

@[simp] theorem gi_complex : (gi : ℂ) = I := by
  simp [gi, GaussianInt.toComplex_def]
@[simp] theorem gsign_complex (b : Bit) : ((gsign b : G) : ℂ) = bitSign b := by
  by_cases hb : b = 0 <;> simp [gsign, bitSign, hb]
@[simp] theorem gphase_complex {n : ℕ} (u : G) (z : Bits n) :
    ((gphase UnifiedEJM.q u z : G) : ℂ) = UnifiedEJM.rawPhase (u : ℂ) z := by
  by_cases hz : z = 0 <;>
    simp [gphase, UnifiedEJM.rawPhase, hz, map_mul, map_neg, map_pow, gi_complex]

noncomputable def scale (n : ℕ) : ℂ := (Real.sqrt 2 : ℂ)⁻¹ * normFactor n

/-- 高斯整数振幅与原Hadamard/CNOT电路逐振幅相同。 -/
theorem numerator_seed {n : ℕ} (u : G) (z : Bits n) :
    Physical.seed (UnifiedEJM.rawPhase (u : ℂ)) z =
      scale n * ((gnumerator (gphase UnifiedEJM.q u) z : G) : ℂ) := by
  simp only [Physical.seed, circuit, chain, hadamardAt, gnumerator, scale,
    map_add, map_mul, gphase_complex, gsign_complex]
  ring

/-- 在物理子系统S上取第一份串，补系统取第二份串。 -/
def splice {n : ℕ} (S : Finset (Fin n)) (z w : Bits n) : Bits n :=
  fun j => if j ∈ S then z j else w j

/-- 纯态偏迹纯度的双副本求和，计算规模为4^n。 -/
def gpurity {n : ℕ} (S : Finset (Fin n)) (v : Bits n → G) : G :=
  ∑ z, ∑ w, v z * v w * star (v (splice S z w)) * star (v (splice S w z))

noncomputable def swapPurity {n : ℕ} (S : Finset (Fin n)) (v : Vec n) : ℂ :=
  ∑ z, ∑ w, v z * v w * star (v (splice S z w)) * star (v (splice S w z))

theorem gpurity_complex {n : ℕ} (S : Finset (Fin n)) (v : Bits n → G) :
    ((gpurity S v : G) : ℂ) = swapPurity S (fun z => (v z : ℂ)) := by
  simp [gpurity, swapPurity, map_sum, map_mul]

theorem swapPurity_smul {n : ℕ} (S : Finset (Fin n)) (v : Vec n) (a : ℂ) :
    swapPurity S (fun z => a * v z) = (a * star a)^2 * swapPurity S v := by
  simp only [swapPurity, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem physical_purity_certificate {n : ℕ} (S : Finset (Fin n)) (u : G) :
    swapPurity S (Physical.seed (UnifiedEJM.rawPhase (u : ℂ))) =
      (scale n * star (scale n))^2 *
        ((gpurity S (gnumerator (gphase UnifiedEJM.q u)) : G) : ℂ) := by
  conv_lhs => arg 2; ext z; rw [numerator_seed]
  rw [swapPurity_smul, gpurity_complex]

theorem phase_affine {n : ℕ} (f : Bits n → Bit) (u : G) (z : Bits n) :
    gphase f u z = gphase f 0 z + u * (gphase f 1 z - gphase f 0 z) := by
  by_cases hz : z = 0
  · simp [gphase, hz]
  · rcases bit_cases (f z) with h | h <;>
      simp [gphase, hz, h, ZMod.val_one_eq_one_mod] <;> ring

def coeffA {n : ℕ} (f : Bits n → Bit) : Bits n → G := gnumerator (gphase f 0)
def coeffB {n : ℕ} (f : Bits n → Bit) (z : Bits n) : G :=
  gnumerator (gphase f 1) z - coeffA f z

theorem numerator_affine {n : ℕ} (f : Bits n → Bit) (u : G) (z : Bits n) :
    gnumerator (gphase f u) z = coeffA f z + u * coeffB f z := by
  simp only [gnumerator, coeffA, coeffB]
  rw [phase_affine f u, phase_affine f u]
  ring

theorem raw_affine {n : ℕ} (u : ℂ) (z : Bits n) :
    UnifiedEJM.rawPhase u z = ((gphase UnifiedEJM.q 0 z : G) : ℂ) +
      u * (((gphase UnifiedEJM.q 1 z : G) : ℂ) - ((gphase UnifiedEJM.q 0 z : G) : ℂ)) := by
  simp only [gphase_complex, map_zero, map_one]
  by_cases hz : z = 0
  · simp [UnifiedEJM.rawPhase, hz]
  · rcases bit_cases (UnifiedEJM.q z) with h | h <;>
      simp [UnifiedEJM.rawPhase, hz, h, ZMod.val_one_eq_one_mod] <;> ring

/-- 原相位在每个输入只取常数项和一次项，因此实际种子是仿射振幅。 -/
theorem physical_seed_affine {n : ℕ} (u : ℂ) (z : Bits n) :
    Physical.seed (UnifiedEJM.rawPhase u) z = scale n *
      (((coeffA UnifiedEJM.q z : G) : ℂ) + u * ((coeffB UnifiedEJM.q z : G) : ℂ)) := by
  simp only [Physical.seed, circuit, chain, hadamardAt]
  rw [raw_affine u, raw_affine u]
  simp only [scale, coeffA, coeffB, gnumerator, map_add, map_sub, map_mul,
    gsign_complex]
  ring

theorem scale_norm (n : ℕ) : scale n * star (scale n) = ((2 : ℂ) ^ (n+1))⁻¹ := by
  have h2 : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    norm_num
  have hn : (Real.sqrt ((2:ℝ)^n) : ℂ)^2 = (2:ℂ)^n := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  simp only [scale, normFactor, star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = (((Real.sqrt 2 : ℂ)^2) * ((Real.sqrt ((2:ℝ)^n) : ℂ)^2))⁻¹ := by ring
    _ = _ := by rw [h2, hn, pow_succ]; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem n5plus_pair12 :
    gpurity ({0,1} : Finset (Fin 5)) (gnumerator (gphase UnifiedEJM.q gi)) = 1408 := by
  decide +kernel

end UnifiedEJM.PhysicsFinite
