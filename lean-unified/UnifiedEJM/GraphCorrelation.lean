import UnifiedEJM.GraphPauli
import UnifiedEJM.GraphWords

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

def graphFeature {n : ℕ} (a : Bits n) : Bits 4 :=
  ![coord a 1, coord a (n-2), coord a 0+coord a (n-1),
    BoundaryAmplitude.middleParity a]

theorem character_graphWord {n : ℕ} (d : Bits 4) (a : Bits n) :
    character (graphWord n d) a = character d (graphFeature a) := by
  unfold character
  rw [graphWord_dot]
  congr 1
  simp [graphFeature, dot, Fin.sum_univ_succ]
  ring

/-- Appendix E 的S(d,k)，保留共轭索引l+d上的字符。 -/
def codeCorrelation (c : Bits 4 → ℂ) (d k : Bits 4) : ℂ :=
  ∑ l, c l * star (c (l+d)) * character (l+d) k

def codeState (n : ℕ) (c : Bits 4 → ℂ) : Vec n :=
  fun z => ∑ d, c d * character (graphWord n d) z * baseGraph n z

def physicalCoefficients (n : ℕ) (u : ℂ) (d : Bits 4) : ℂ :=
  graphCoefficient n u (featureCoordinates n d)

/-- 原始物理背景与固定行W=(4,1,8,...,8,2,4)的码态逐振幅相同。 -/
theorem physicalBackground_codeState {n : ℕ} (hn : 5≤n) (u : ℂ) (y : Bits n) :
    physicalBackground n u y = -I * codeState n (physicalCoefficients n u) y := by
  rw [physicalBackground_graph_words (by omega)]
  simp_rw [edge_featureMask_eq_graphWord hn]
  unfold codeState
  rw [← (coordinatesEquiv n).sum_comp
    (fun d => physicalCoefficients n u d * character (graphWord n d) y * baseGraph n y)]
  simp only [coordinatesEquiv, physicalCoefficients, Equiv.coe_fn_mk,
    coordinates_left_inverse]

theorem graphPauliPhase_norm {n : ℕ} (a : Bits n) : ‖graphPauliPhase a‖=1 := by
  unfold graphPauliPhase
  rw [norm_mul]
  have hs : ∀ b : Bit, ‖bitSign b‖=1 := by
    intro b
    rcases OddEJM.bit_cases b with rfl | rfl <;> norm_num [bitSign]
  simp [hs, norm_pow]

private theorem graphWord_constraint {n : ℕ} (hn : 5≤n)
    (h l d : Bits 4) (a : Bits n) :
    graphWord n h+(graphMask a+graphWord n d)+graphWord n l=graphMask a ↔ h=l+d := by
  constructor
  · intro hEq
    apply graphWord_injective hn
    rw [graphWord_add]
    funext j
    have ht := congrFun hEq j
    dsimp only [Pi.add_apply] at ht ⊢
    linear_combination (norm := (ring_nf; simp [show (2 : Bit) = 0 by decide])) ht
  · intro heq
    rw [heq, graphWord_add]
    funext j
    simp only [Pi.add_apply]
    ring_nf
    simp [show (2 : Bit) = 0 by decide]

/-- 任意物理Pauli掩码的可行图字部分直接压成S(d,Wᵀa)。 -/
theorem codeState_pauli_feasible {n : ℕ} (hn : 5≤n) (c : Bits 4 → ℂ)
    (a : Bits n) (d : Bits 4) :
    pauliExpectation (codeState n c) a (graphMask a+graphWord n d) 1 =
      graphPauliPhase a * codeCorrelation c d (graphFeature a) := by
  unfold codeState
  rw [graph_superposition_pauli (by omega)]
  rw [Finset.sum_comm]
  simp_rw [graphWord_constraint hn]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [codeCorrelation, Finset.mul_sum, character_graphWord]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem codeState_pauli_feasible_norm {n : ℕ} (hn : 5≤n) (c : Bits 4 → ℂ)
    (a : Bits n) (d : Bits 4) :
    ‖pauliExpectation (codeState n c) a (graphMask a+graphWord n d) 1‖ =
      ‖codeCorrelation c d (graphFeature a)‖ := by
  rw [codeState_pauli_feasible hn, norm_mul, graphPauliPhase_norm, one_mul]

/-- 不属于图码Pauli支持的掩码给出严格零期望。 -/
theorem codeState_pauli_infeasible {n : ℕ} (hn : 0<n) (c : Bits 4 → ℂ)
    (a b : Bits n) (hb : ∀ d, b≠graphMask a+graphWord n d) :
    pauliExpectation (codeState n c) a b 1 = 0 := by
  unfold codeState
  rw [graph_superposition_pauli hn]
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro l _
  have hne : graphWord n h+b+graphWord n l ≠ graphMask a := by
    intro he
    apply hb (h+l)
    rw [graphWord_add]
    funext j
    have ht := congrFun he j
    dsimp only [Pi.add_apply] at ht ⊢
    linear_combination (norm := (ring_nf; simp [show (2 : Bit) = 0 by decide])) ht
  simp [hne]

theorem physicalBackground_pauli {n : ℕ} (hn : 5≤n) (u : ℂ) (a b : Bits n) :
    pauliExpectation (physicalBackground n u) a b 1 =
      pauliExpectation (codeState n (physicalCoefficients n u)) a b 1 := by
  have hstate := funext (physicalBackground_codeState hn u)
  rw [hstate, pauliExpectation_scale]
  simp

/-- 包含原门、末位Hadamard和整体相位的真实背景之可行Pauli模。 -/
theorem physicalBackground_pauli_feasible_norm {n : ℕ} (hn : 5≤n) (u : ℂ)
    (a : Bits n) (d : Bits 4) :
    ‖pauliExpectation (physicalBackground n u) a (graphMask a+graphWord n d) 1‖ =
      ‖codeCorrelation (physicalCoefficients n u) d (graphFeature a)‖ := by
  rw [physicalBackground_pauli hn, codeState_pauli_feasible_norm hn]

theorem physicalBackground_pauli_infeasible {n : ℕ} (hn : 5≤n) (u : ℂ)
    (a b : Bits n) (hb : ∀d, b≠graphMask a+graphWord n d) :
    pauliExpectation (physicalBackground n u) a b 1 = 0 := by
  rw [physicalBackground_pauli hn]
  exact codeState_pauli_infeasible (by omega) _ a b hb

end UnifiedEJM.GraphBackground
