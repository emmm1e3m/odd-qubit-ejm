import UnifiedEJM.GraphCorrelation

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

set_option maxRecDepth 10000

def SupportedOn {n : ℕ} (S : Finset (Fin n)) (a : Bits n) : Prop :=
  ∀ j, j∉S → a j=0

def leftNeighbor {n : ℕ} (a : Bits n) (j : ℕ) : Bit :=
  if j=0 then 0 else coord a (j-1)

theorem coord_difference {n : ℕ} (a : Bits n) (j : ℕ) (hj : j<n) :
    coord (difference a) j = coord a j+coord a (j+1) := by
  simp [coord, difference, hj]

/-- 零支撑位的Pauli图掩码只有左右邻位，首位局域S项严格消失。 -/
theorem graphMask_coord_of_zero {n : ℕ} (a : Bits n) (j : ℕ) (hj : j<n)
    (hz : coord a j=0) :
    coord (graphMask a) j = leftNeighbor a j+coord a (j+1) := by
  rw [graphMask, CircuitPauli.coord_edgeMask _ j hj, coord_difference a j hj]
  by_cases hj0 : j=0
  · subst j
    simp [hz, leftNeighbor]
  · rw [if_neg hj0, coord_difference a (j-1) (by omega)]
    have hs : j-1+1=j := by omega
    simp [leftNeighbor, hj0, hs, hz, add_comm]

/-- 在物理B侧为零等价于178.10的每站局域约束。 -/
theorem support_graphMask_add_word_iff {n : ℕ}
    (S : Finset (Fin n)) (a : Bits n) (ha : SupportedOn S a) (d : Bits 4) :
    SupportedOn S (graphMask a+graphWord n d) ↔
      ∀ j : Fin n, j∉S →
        leftNeighbor a j.val+coord a (j.val+1)=coord (graphWord n d) j.val := by
  constructor
  · intro hs j hj
    have hzero : coord a j.val=0 := by simpa [coord, j.isLt] using ha j hj
    have hh := hs j hj
    have hmask := graphMask_coord_of_zero a j.val j.isLt hzero
    have hc : coord (graphMask a) j.val+coord (graphWord n d) j.val=0 := by
      simpa [coord, j.isLt] using hh
    rw [hmask] at hc
    have ht := congrArg (fun x : Bit => x+coord (graphWord n d) j.val) hc
    simpa [add_assoc, CharTwo.add_self_eq_zero] using ht
  · intro hs j hj
    have hzero : coord a j.val=0 := by simpa [coord, j.isLt] using ha j hj
    have hmask := graphMask_coord_of_zero a j.val j.isLt hzero
    have hh := hs j hj
    have hc : coord (graphMask a) j.val+coord (graphWord n d) j.val=0 := by
      rw [hmask, hh]
      exact CharTwo.add_self_eq_zero _
    simpa [coord, j.isLt] using hc

/-- Wᵀv的四个物理奇偶就是Pauli相关函数中的k。 -/
theorem graphFeature_charge {n : ℕ} (a : Bits n) (i : Fin 4) :
    graphFeature a i = ∑ j : Fin n, graphWord n (unitBit 4 i.val) j * a j := by
  have hdot : dot (unitBit 4 i.val) (graphFeature a) =
      dot (graphWord n (unitBit 4 i.val)) a := by
    rw [graphWord_dot]
    simp [dot, Fin.sum_univ_succ, graphFeature]
    ring
  rw [unitBit_dot] at hdot
  exact hdot

/-- 逐物理位读取W的行，坐标序与加权转移完全相同。 -/
def rowWord (n : ℕ) (j : Fin n) : Bits 4 :=
  fun i => graphWord n (unitBit 4 i.val) j

theorem rowWord_dot {n : ℕ} (d : Bits 4) (j : Fin n) :
    dot (rowWord n j) d = graphWord n d j := by
  simp [rowWord, graphWord, dot, unitBit, Fin.sum_univ_succ]
  split_ifs <;> ring

theorem graphWord_apply {n : ℕ} (hn : 5≤n) (d : Bits 4) (j : Fin n) :
    graphWord n d j =
      if j.val=0 then d 2 else if j.val=1 then d 0 else
      if j.val=n-2 then d 1 else if j.val=n-1 then d 2 else d 3 := by
  have hj := j.isLt
  simp only [graphWord, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    unitBit, BoundaryAmplitude.middleMask]
  split_ifs <;>
    simp_all only [mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero] <;> omega

/-- 逐站行向量严格是4,1,8,...,8,2,4。 -/
theorem rowWord_formula {n : ℕ} (hn : 5≤n) (j : Fin n) :
    rowWord n j =
      if j.val=0 then ![0,0,1,0] else if j.val=1 then ![1,0,0,0] else
      if j.val=n-2 then ![0,1,0,0] else if j.val=n-1 then ![0,0,1,0]
      else ![0,0,0,1] := by
  funext i
  simp only [rowWord, graphWord_apply hn]
  split_ifs <;> fin_cases i <;> norm_num [unitBit]

theorem graphFeature_sum_charge {n : ℕ} (a : Bits n) :
    graphFeature a = ∑ j : Fin n, (fun i : Fin 4 => rowWord n j i * a j) := by
  funext i
  simpa only [Finset.sum_apply, rowWord] using graphFeature_charge a i

/-- B站点的真实邻位约束，不含任何秩或线性消元假设。 -/
def LocalConstraints {n : ℕ} (S : Finset (Fin n)) (d : Bits 4) (a : Bits n) : Prop :=
  ∀ j : Fin n, j∉S →
    leftNeighbor a j.val+coord a (j.val+1)=dot (rowWord n j) d

/-- 独立静态全赋值计数；227将其与211的递归pathSum连接。 -/
def physicalWeight {n : ℕ} (S : Finset (Fin n)) (d k : Bits 4) : ℚ := by
  classical
  exact (1/2:ℚ)^S.card * ∑ a : Bits n,
    if SupportedOn S a ∧ LocalConstraints S d a ∧ graphFeature a=k then 1 else 0

end UnifiedEJM.GraphBackground
