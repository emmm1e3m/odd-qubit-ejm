import UnifiedEJM.Core
import OddEJM.Finite
import Mathlib.Tactic

namespace UnifiedEJM.EvenCertificate
open scoped BigOperators
open OddEJM

/-- 四位扇区变量次序为首位、奇内部块、倒数第二位、末位。 -/
def decode4 (k : ℕ) : Bits 4 :=
  ![((k / 8 : ℕ) : Bit), ((k / 4 : ℕ) : Bit), ((k / 2 : ℕ) : Bit), (k : Bit)]

def embedSector (e : Bit) (w : Bits 4) : Bits 5 := ![w 0, e, w 1, w 2, w 3]

def sectorDiff (A w : Bits 4) : ℤ :=
  ((Q20 (embedSector 0 w)).val : ℤ) - ((Q20 (embedSector 1 (w + A))).val : ℤ)

def sectorCoeff (A H : Bits 4) (k : ℤ) : ℤ :=
  ∑ w, if sectorDiff A w = k then intSign (dot H w) else 0

def sectorPairs : Finset (ℕ × ℕ) := {(8,8), (2,2), (9,15), (5,7), (5,3), (3,1)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- 任意偶数n≥8的六个剩余扇区：三个Laurent系数均为零。 -/
theorem sector_coeff_checked : ∀ p ∈ sectorPairs,
    ∀ k ∈ ({-1,0,1} : Finset ℤ), sectorCoeff (decode4 p.1) (decode4 p.2) k = 0 := by
  decide

/-- 六比特额外残留的精确系数，未使用浮点数。 -/
theorem six_extra_coefficients :
    sectorCoeff (decode4 4) (decode4 4) (-1) = 2 ∧
    sectorCoeff (decode4 4) (decode4 4) 0 = 0 ∧
    sectorCoeff (decode4 4) (decode4 4) 1 = -2 := by decide

lemma Q20_val_cases (w : Bits 5) : (Q20 w).val = 0 ∨ (Q20 w).val = 1 := by
  have := (Q20 w).val_lt
  omega

lemma sector_diff_cases (A w : Bits 4) :
    sectorDiff A w = -1 ∨ sectorDiff A w = 0 ∨ sectorDiff A w = 1 := by
  rcases Q20_val_cases (embedSector 0 w) with h | h <;>
    rcases Q20_val_cases (embedSector 1 (w + A)) with h' | h' <;>
      simp [sectorDiff, h, h']

lemma sector_coeff_cast (A H : Bits 4) (k : ℤ) :
    (sectorCoeff A H k : ℂ) =
      ∑ w, if sectorDiff A w = k then bitSign (dot H w) else 0 := by
  simp [sectorCoeff, Int.cast_sum]

/-- 任意差值权重按三个精确层系数分解。 -/
theorem sector_weighted_formula (A H : Bits 4) (f : ℤ → ℂ) :
    (∑ w : Bits 4, bitSign (dot H w) * f (sectorDiff A w)) =
      (sectorCoeff A H (-1) : ℂ) * f (-1) +
      (sectorCoeff A H 0 : ℂ) * f 0 + (sectorCoeff A H 1 : ℂ) * f 1 := by
  calc
    _ = ∑ w : Bits 4,
      ((if sectorDiff A w = -1 then bitSign (dot H w) else 0) * f (-1) +
       (if sectorDiff A w = 0 then bitSign (dot H w) else 0) * f 0 +
       (if sectorDiff A w = 1 then bitSign (dot H w) else 0) * f 1) := by
      apply Finset.sum_congr rfl
      intro w _
      rcases sector_diff_cases A w with h | h | h <;> simp [h]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.sum_mul, sector_coeff_cast]

theorem sector_weighted_zero {a h : ℕ} (hp : (a,h) ∈ sectorPairs) (f : ℤ → ℂ) :
    (∑ w : Bits 4, bitSign (dot (decode4 h) w) * f (sectorDiff (decode4 a) w)) = 0 := by
  rw [sector_weighted_formula]
  have hm := sector_coeff_checked (a,h) hp (-1) (by simp)
  have hz := sector_coeff_checked (a,h) hp 0 (by simp)
  have hp' := sector_coeff_checked (a,h) hp 1 (by simp)
  simp [hm, hz, hp']

theorem sector_phase_zero {a h : ℕ} (hp : (a,h) ∈ sectorPairs)
    (u : ℂ) (hu : u * star u = 1) :
    ∑ w : Bits 4, bitSign (dot (decode4 h) w) *
      (u ^ (Q20 (embedSector 0 w)).val *
        star (u ^ (Q20 (embedSector 1 (w + decode4 a))).val)) = 0 := by
  change u * (starRingEnd ℂ) u = 1 at hu
  let f : ℤ → ℂ := fun k => if k = -1 then star u else if k = 0 then 1 else u
  calc
    _ = ∑ w : Bits 4, bitSign (dot (decode4 h) w) * f (sectorDiff (decode4 a) w) := by
      apply Finset.sum_congr rfl
      intro w _
      rcases Q20_val_cases (embedSector 0 w) with hz | hz <;>
        rcases Q20_val_cases (embedSector 1 (w + decode4 a)) with ha | ha <;>
          simp [sectorDiff, f, hz, ha, hu]
    _ = 0 := sector_weighted_zero hp f

/-- n=6的额外16点扇区相位和为2u*−2u。 -/
theorem six_extra_phase (u : ℂ) (hu : u * star u = 1) :
    (∑ w : Bits 4, bitSign (dot (decode4 4) w) *
      (u ^ (Q20 (embedSector 0 w)).val *
        star (u ^ (Q20 (embedSector 1 (w + decode4 4))).val))) = 2 * star u - 2 * u := by
  change u * (starRingEnd ℂ) u = 1 at hu
  let f : ℤ → ℂ := fun k => if k = -1 then star u else if k = 0 then 1 else u
  calc
    _ = ∑ w : Bits 4, bitSign (dot (decode4 4) w) * f (sectorDiff (decode4 4) w) := by
      apply Finset.sum_congr rfl
      intro w _
      rcases Q20_val_cases (embedSector 0 w) with hz | hz <;>
        rcases Q20_val_cases (embedSector 1 (w + decode4 4)) with ha | ha <;>
          simp [sectorDiff, f, hz, ha, hu]
    _ = _ := by
      rw [sector_weighted_formula]
      rw [six_extra_coefficients.1, six_extra_coefficients.2.1, six_extra_coefficients.2.2]
      simp [f]
      ring

end UnifiedEJM.EvenCertificate

