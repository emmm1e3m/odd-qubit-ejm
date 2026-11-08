import UnifiedEJM.GraphBackground
import UnifiedEJM.BoundaryFeatures

noncomputable section
open scoped BigOperators
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

theorem dot_featureMask {n : ℕ} (h : Bits 4) (z : Bits n) :
    dot (featureMask n h) z = dot h (features z) := by
  rw [features_basis]
  simp only [dot, featureMask, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- 四个固定图字的坐标，采用178.3的低位顺序。 -/
def graphWord (n : ℕ) (d : Bits 4) : Bits n :=
  d 0 • unitBit n 1 + d 1 • unitBit n (n-2) +
    d 2 • (unitBit n 0 + unitBit n (n-1)) +
    d 3 • BoundaryAmplitude.middleMask n

def graphCoordinates (n : ℕ) (h : Bits 4) : Bits 4 :=
  ![h 0+h 1+h 3,
    h 0+(if n%2=0 then h 1 else h 2),
    h 0+h 3,
    h 1+h 2]

def featureCoordinates (n : ℕ) (d : Bits 4) : Bits 4 :=
  let x := d 1+(if n%2=0 then d 0+d 2 else d 3+d 0+d 2)
  ![x, d 0+d 2, d 3+d 0+d 2, d 2+x]

theorem coordinates_left_inverse (n : ℕ) (h : Bits 4) :
    featureCoordinates n (graphCoordinates n h) = h := by
  funext j
  fin_cases j <;> by_cases hp : n%2=0 <;>
    simp [featureCoordinates, graphCoordinates, hp] <;> ring_nf <;>
      simp [show (2:Bit)=0 by decide, show (3:Bit)=1 by decide, show (4:Bit)=0 by decide]

theorem coordinates_right_inverse (n : ℕ) (d : Bits 4) :
    graphCoordinates n (featureCoordinates n d) = d := by
  funext j
  fin_cases j <;> by_cases hp : n%2=0 <;>
    simp [featureCoordinates, graphCoordinates, hp] <;> ring_nf <;>
      simp [show (2:Bit)=0 by decide, show (3:Bit)=1 by decide, show (4:Bit)=0 by decide]

def coordinatesEquiv (n : ℕ) : Bits 4 ≃ Bits 4 where
  toFun := graphCoordinates n
  invFun := featureCoordinates n
  left_inv := coordinates_left_inverse n
  right_inv := coordinates_right_inverse n

private theorem dot_smul_left {n : ℕ} (b : Bit) (v z : Bits n) :
    dot (b • v) z = b * dot v z := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem graphWord_dot {n : ℕ} (d : Bits 4) (y : Bits n) :
    dot (graphWord n d) y =
      d 0 * coord y 1 + d 1 * coord y (n-2) +
        d 2 * (coord y 0 + coord y (n-1)) + d 3 * BoundaryAmplitude.middleParity y := by
  simp only [graphWord, OddEJM.dot_add_left, dot_smul_left,
    CircuitPauli.dot_unit_left, BoundaryAmplitude.dot_middleMask]

theorem features_difference {n : ℕ} (hn : 5≤n) (y : Bits n) :
    features (difference y) =
      ![coord y 0+coord y 1+coord y (n-2)+coord y (n-1),
        coord y 1+BoundaryAmplitude.middleParity y+
          (if n%2=0 then coord y (n-2) else 0),
        BoundaryAmplitude.middleParity y+(if n%2=0 then 0 else coord y (n-2)),
        coord y 0+coord y 1+coord y (n-1)] := by
  have hb : BoundaryAmplitude.inputBranch y (coord y (n-1)) = difference y := by
    apply CircuitPauli.setBit_eq_self
    simp [coord, difference, show n-1<n by omega, show ¬ n-1+1<n by omega]
  rw [← hb, BoundaryAmplitude.features_inputBranch hn]

/-- 原特征字经过真实CNOT差分后正是固定四列图码W。 -/
theorem edge_featureMask_eq_graphWord {n : ℕ} (hn : 5≤n) (h : Bits 4) :
    CircuitPauli.edgeMask (featureMask n h) = graphWord n (graphCoordinates n h) := by
  have hd (y : Bits n) :
      dot (CircuitPauli.edgeMask (featureMask n h)) y =
        dot (graphWord n (graphCoordinates n h)) y := by
    rw [CircuitPauli.dot_edgeMask, dot_featureMask, features_difference hn,
      graphWord_dot]
    by_cases hp : n%2=0 <;>
      simp [dot, Fin.sum_univ_succ, graphCoordinates, hp] <;> ring
  funext j
  simpa only [dot_unitBit] using hd (unitBit n j.val)

theorem graphWord_first {n : ℕ} (hn : 5≤n) (d : Bits 4) :
    coord (graphWord n d) 0 = d 2 := by
  simp [coord, graphWord, unitBit, BoundaryAmplitude.middleMask,
    show 0<n by omega, show ¬ (0:ℕ)=n-2 by omega, show ¬ (0:ℕ)=n-1 by omega]

theorem graphWord_second {n : ℕ} (hn : 5≤n) (d : Bits 4) :
    coord (graphWord n d) 1 = d 0 := by
  simp [coord, graphWord, unitBit, BoundaryAmplitude.middleMask,
    show 1<n by omega, show ¬ (1:ℕ)=n-2 by omega, show ¬ (1:ℕ)=n-1 by omega]

theorem graphWord_middle {n : ℕ} (hn : 5≤n) (d : Bits 4) :
    coord (graphWord n d) 2 = d 3 := by
  simp [coord, graphWord, unitBit, BoundaryAmplitude.middleMask,
    show 2<n by omega, show 2<n-2 by omega,
    show ¬ (2:ℕ)=n-2 by omega, show ¬ (2:ℕ)=n-1 by omega]

theorem graphWord_penultimate {n : ℕ} (hn : 5≤n) (d : Bits 4) :
    coord (graphWord n d) (n-2) = d 1 := by
  simp [coord, graphWord, unitBit, BoundaryAmplitude.middleMask,
    show n-2<n by omega, show ¬ n-2=0 by omega,
    show ¬ n-2=1 by omega, show ¬ n-2=n-1 by omega]

theorem graphWord_injective {n : ℕ} (hn : 5≤n) :
    Function.Injective (graphWord n) := by
  intro d e hde
  have h0 := congrArg (fun z => coord z 1) hde
  have h1 := congrArg (fun z => coord z (n-2)) hde
  have h2 := congrArg (fun z => coord z 0) hde
  have h3 := congrArg (fun z => coord z 2) hde
  rw [graphWord_second hn, graphWord_second hn] at h0
  rw [graphWord_penultimate hn, graphWord_penultimate hn] at h1
  rw [graphWord_first hn, graphWord_first hn] at h2
  rw [graphWord_middle hn, graphWord_middle hn] at h3
  funext j
  fin_cases j <;> assumption

theorem graphWord_add (n : ℕ) (d e : Bits 4) :
    graphWord n (d+e) = graphWord n d+graphWord n e := by
  funext j
  simp [graphWord, add_smul]
  ring

end UnifiedEJM.GraphBackground
