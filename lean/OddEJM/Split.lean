import OddEJM.Core
import Mathlib.Algebra.BigOperators.Fin
namespace OddEJM
open scoped BigOperators

abbrev BitRest {n : ℕ} (j : Fin n) := {k : Fin n // k ≠ j} → Bit

def joinBit {n : ℕ} (j : Fin n) (b : Bit) (r : BitRest j) : Bits n :=
  (Equiv.piSplitAt j (fun _ : Fin n => Bit)).symm (b, r)

@[simp] theorem joinBit_self {n : ℕ} (j : Fin n) (b : Bit) (r : BitRest j) :
    joinBit j b r j = b := by simp [joinBit, Equiv.piSplitAt]

@[simp] theorem joinBit_ne {n : ℕ} (j : Fin n) (b : Bit) (r : BitRest j)
    (k : Fin n) (hk : k ≠ j) : joinBit j b r k = r ⟨k, hk⟩ := by
  simp [joinBit, Equiv.piSplitAt, hk]

@[simp] theorem coord_joinBit {n : ℕ} (j : Fin n) (b : Bit) (r : BitRest j) :
    coord (joinBit j b r) j.val = b := by simp [coord]

@[simp] theorem setBit_joinBit {n : ℕ} (j : Fin n) (b c : Bit) (r : BitRest j) :
    setBit (joinBit j b r) j.val c = joinBit j c r := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [setBit]
  · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp [setBit, hk, hv]

theorem sum_bit (f : Bit → ℂ) : (∑ b, f b) = f 0 + f 1 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 2).toEquiv f, Fin.sum_univ_two]
  rfl

/-- 任意振幅函数按指定物理比特精确拆成两个切片。 -/
theorem sum_split_bit {n : ℕ} (j : Fin n) (F : Bits n → ℂ) :
    (∑ z, F z) = ∑ r : BitRest j, (F (joinBit j 0 r) + F (joinBit j 1 r)) := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt j (fun _ : Fin n => Bit)).symm F]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact sum_bit (fun b => F (joinBit j b r))

end OddEJM
