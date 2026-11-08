import UnifiedEJM.LocalExpectation
import UnifiedEJM.GraphBackground

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

private theorem bits_add_eq_zero {n : ℕ} (a b : Bits n) : a+b=0 ↔ a=b := by
  constructor
  · intro h
    have hh := congrArg (fun z : Bits n => z+b) h
    simpa only [add_assoc, bits_add_self, add_zero, zero_add] using hh
  · rintro rfl
    exact bits_add_self _

/-- Y乘积态的全部真实Pauli期望，不假设任何稳定子公式。 -/
theorem yColumn_zero_pauli {n : ℕ} (a b : Bits n) (c : ℂ) :
    pauliExpectation (yColumn (0 : Bits n)) a b c =
      if a=b then c * star (I ^ weight a) else 0 := by
  have hcol : yColumn (0 : Bits n) =
      fun z => normFactor n * UnifiedEJM.background (1:ℂ) z := by
    funext z
    simp [yColumn, UnifiedEJM.background, character, dot]
  rw [hcol, pauliExpectation_scale, UnifiedEJM.background_pauli_sum]
  simp only [one_pow, star_one, mul_one, character_sum, bits_add_eq_zero]
  by_cases hab : a=b
  · subst b
    simp only [ite_true]
    calc
      _ = (star (normFactor n) * normFactor n * (2:ℂ)^n) *
          (c * star (I ^ weight a)) := by ring
      _ = _ := by rw [normFactor_card]; ring
  · simp [hab]

private theorem swapped_setBit_eq_iff {n : ℕ} (x y : Bits n) (j : ℕ) :
    setBit x j (coord y j) = setBit y j (coord x j) ↔ x=y := by
  constructor
  · intro h
    funext k
    have hk := congrFun h k
    by_cases hj : k.val=j
    · have hjn : j<n := by omega
      have hk0 : (⟨j,hjn⟩ : Fin n)=k := Fin.ext hj.symm
      simpa [setBit, hj, coord, hjn, hk0] using hk.symm
    · simpa [setBit, hj] using hk
  · rintro rfl
    rfl

/-- 参考态对应的二进制Pauli图掩码；首位对角元只反映局域S相位。 -/
def graphMask {n : ℕ} (a : Bits n) : Bits n :=
  CircuitPauli.edgeMask (difference a)

def graphPauliPhase {n : ℕ} (a : Bits n) : ℂ :=
  bitSign (coord (difference a) (n-1) * coord (difference a) (n-1)) *
    star (I ^ weight (difference a))

/-- 真实原门参考态的完整Pauli期望表，直接由电路拉回证明。 -/
theorem baseGraph_pauli {n : ℕ} (hn : 0<n) (a b : Bits n) :
    pauliExpectation (baseGraph n) a b 1 =
      if b=graphMask a then graphPauliPhase a else 0 := by
  let B := PhysicsCircuit.prefixMask b
  have hB : ∀ z : Bits n, character b z = character B (difference z) := by
    intro z
    simp only [B, character, PhysicsCircuit.dot_prefix, suffix_difference]
  have hp := CircuitPauli.circuit_pauli hn a b B 1 (yColumn (0 : Bits n)) hB
  have he := CircuitPauli.circuit_expectation hn (yColumn (0 : Bits n))
    a b _ _ 1 _ hp
  change pauliExpectation (baseGraph n) a b 1 = _ at he
  rw [he, yColumn_zero_pauli]
  have heq : setBit (difference a) (n-1) (coord B (n-1)) =
      setBit B (n-1) (coord (difference a) (n-1)) ↔ b=graphMask a := by
    rw [swapped_setBit_eq_iff]
    constructor
    · intro h
      have hh := congrArg CircuitPauli.edgeMask h
      simpa only [B, PhysicsCircuit.edgeMask_prefix, graphMask] using hh.symm
    · intro h
      dsimp [B]
      rw [h]
      exact (PhysicsCircuit.prefix_edgeMask (difference a)).symm
  by_cases hbg : b=graphMask a
  · rw [if_pos (heq.mpr hbg), if_pos hbg]
    have hBd : B=difference a := by
      dsimp [B]
      rw [hbg]
      exact PhysicsCircuit.prefix_edgeMask (difference a)
    rw [hBd, PhysicsCircuit.setBit_coord]
    simp [graphPauliPhase]
  · rw [if_neg (fun h => hbg (heq.mp h)), if_neg hbg]

/-- 单个Z字符给Pauli矩阵元的真实相移。 -/
theorem character_twist_pauli_matrix_element {n : ℕ}
    (g : Vec n) (v w a b : Bits n) :
    (∑ z, star (character v (z+a) * g (z+a)) * character b z *
      (character w z * g z)) =
      character v a * pauliExpectation g a (v+b+w) 1 := by
  simp only [star_mul, character_star, character_add, character_add_left,
    pauliExpectation, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- 十六图字叠加的Pauli期望；图字及物理掩码仍是完整n位串。 -/
theorem graph_superposition_pauli {n : ℕ} (hn : 0<n)
    (c : Bits 4 → ℂ) (W : Bits 4 → Bits n) (a b : Bits n) :
    pauliExpectation (fun z => ∑ h, c h * character (W h) z * baseGraph n z) a b 1 =
      ∑ h : Bits 4, ∑ l : Bits 4,
        star (c h) * c l * character (W h) a *
          (if W h+b+W l=graphMask a then graphPauliPhase a else 0) := by
  unfold pauliExpectation
  simp only [star_sum, star_mul, character_star, one_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = star (c h) * c l *
        (∑ z, star (character (W h) (z+a) * baseGraph n (z+a)) * character b z *
          (character (W l) z * baseGraph n z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [star_mul, character_star]
      ring
    _ = _ := by
      rw [character_twist_pauli_matrix_element, baseGraph_pauli hn]
      ring

end UnifiedEJM.GraphBackground
