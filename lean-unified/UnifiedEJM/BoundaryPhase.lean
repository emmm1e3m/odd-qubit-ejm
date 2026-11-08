import UnifiedEJM.BoundaryAmplitude

open OddEJM OddEJM.CircuitPauli Complex
open UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.BoundaryAmplitude

/-- 不存在的末条边贡献单位相位。 -/
def edgePhase {n : ℕ} (y : Bits n) (j : Fin n) : ℂ :=
  if j.val = n-1 then 1 else I ^ (y j + coord y (j.val+1)).val

theorem pathPhase_product {n : ℕ} (y : Bits n) :
    pathPhase y = -I * ∏ j : Fin n, edgePhase y j := by
  unfold pathPhase weight
  rw [← Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j.val = n-1 <;> simp [edgePhase, inputBranch, setBit, difference, hj]

/-- 每条边的四副本相位仅保留跨割边符号。 -/
theorem edge_phase_four (a b c d : Bit) (s t : Prop) [Decidable s] [Decidable t] :
    I ^ (a+b).val * I ^ (c+d).val *
      star (I ^ ((if s then a else c) + (if t then b else d)).val) *
      star (I ^ ((if s then c else a) + (if t then d else b)).val) =
      bitSign (if (s ↔ t) then 0 else (a+c)*(b+d)) := by
  rcases OddEJM.bit_cases a with rfl | rfl <;>
    rcases OddEJM.bit_cases b with rfl | rfl <;>
    rcases OddEJM.bit_cases c with rfl | rfl <;>
    rcases OddEJM.bit_cases d with rfl | rfl <;>
    by_cases hs : s <;> by_cases ht : t <;>
    norm_num [hs, ht, bitSign, Complex.star_def, OddEJM.Bit,
      ZMod.val_ofNat, ZMod.val_one_eq_one_mod] <;> decide +kernel

/-- 末端补零，内部只计割两侧的相邻坐标差积。 -/
def crossingTerm {n : ℕ} (S : Finset (Fin n)) (y v : Bits n) (j : Fin n) : Bit :=
  if hj : j.val+1 < n then
    if (j ∈ S ↔ (⟨j.val+1,hj⟩ : Fin n) ∈ S) then 0
    else (y j+v j)*(coord y (j.val+1)+coord v (j.val+1))
  else 0

theorem edgePhase_four_splice {n : ℕ} (S : Finset (Fin n)) (y v : Bits n) (j : Fin n) :
    edgePhase y j * edgePhase v j *
      star (edgePhase (splice S y v) j) * star (edgePhase (splice S v y) j) =
      bitSign (crossingTerm S y v j) := by
  by_cases hj : j.val = n-1
  · have hnxt : ¬ j.val+1 < n := by omega
    have hnxt' : ¬ n-1+1 < n := by omega
    simp [edgePhase, crossingTerm, hj, hnxt', bitSign]
  · have hnxt : j.val+1 < n := by omega
    simpa [edgePhase, crossingTerm, hj, hnxt, splice, coord] using
      edge_phase_four (y j) (coord y (j.val+1)) (v j) (coord v (j.val+1))
        (j ∈ S) ((⟨j.val+1,hnxt⟩ : Fin n) ∈ S)

/-- Q的四副本恒等式：全部同侧和局域相位严格抵消。 -/
theorem pathPhase_four_splice {n : ℕ} (S : Finset (Fin n)) (y v : Bits n) :
    pathPhase y * pathPhase v *
      star (pathPhase (splice S y v)) * star (pathPhase (splice S v y)) =
      bitSign (∑ j : Fin n, crossingTerm S y v j) := by
  calc
    _ = ∏ j : Fin n, edgePhase y j * edgePhase v j *
        star (edgePhase (splice S y v) j) * star (edgePhase (splice S v y) j) := by
      simp only [pathPhase_product, star_mul, star_neg, star_prod,
        Finset.prod_mul_distrib, Complex.star_def, Complex.conj_I]
      ring_nf <;> norm_num
    _ = ∏ j : Fin n, bitSign (crossingTerm S y v j) := by
      apply Finset.prod_congr rfl
      intro j _
      exact edgePhase_four_splice S y v j
    _ = _ := (OddEJM.bitSign_sum Finset.univ (crossingTerm S y v)).symm

/-- 一条边的相位拆成两端局域相位及路径图CZ符号。 -/
theorem edge_phase_graph (a b : Bit) :
    I ^ (a+b).val = I^a.val * I^b.val * bitSign (a*b) := by
  rcases OddEJM.bit_cases a with rfl | rfl <;>
    rcases OddEJM.bit_cases b with rfl | rfl <;>
      norm_num [bitSign, OddEJM.Bit, ZMod.val_ofNat, ZMod.val_one_eq_one_mod]

end UnifiedEJM.BoundaryAmplitude


