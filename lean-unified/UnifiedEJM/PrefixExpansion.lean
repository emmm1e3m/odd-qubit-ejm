import UnifiedEJM.PrefixKernel

open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

/-- 任意整数长度变量的二次展开，与参数值取样无关。 -/
theorem p12Sum_expansion (nu : Bit) (suffix : Bool) (K : ℤ) (k : Fin 5) :
    p12Sum nu suffix K k = p12Coeff nu suffix 0 k +
      (K : G) * p12Coeff nu suffix 1 k + (K : G)^2 * p12Coeff nu suffix 2 k := by
  unfold p12Sum p12Coeff
  simp_rw [pairWeight_eval, Int.cast_add, Int.cast_mul, Int.cast_pow, add_mul,
    Finset.sum_add_distrib]
  simp only [Finset.mul_sum, mul_assoc]

theorem long_weight_expansion (la lb : Option Bit) (X Y : ℤ)
    (ca da cb db : Fin 4) (T : G) :
    ((runWeight X la ca * runWeight X la da *
      runWeight Y lb cb * runWeight Y lb db : ℤ) : G) * T =
      ∑ i : Fin 3, ∑ j : Fin 3, (X : G)^i.val * (Y : G)^j.val *
        ((runPairWeight la ca da i * runPairWeight lb cb db j : ℤ) : G) * T := by
  have hw : runWeight X la ca * runWeight X la da *
      runWeight Y lb cb * runWeight Y lb db =
      (runWeight X la ca * runWeight X la da) *
      (runWeight Y lb cb * runWeight Y lb db) := by ring
  rw [hw, runPairWeight_eval, runPairWeight_eval]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  norm_num
  ring

def biEval (C : Fin 3 → Fin 3 → G) (X Y : ℤ) : G :=
  C 0 0 + (Y : G) * C 0 1 + (Y : G)^2 * C 0 2 +
    (X : G) * C 1 0 + (X : G) * (Y : G) * C 1 1 +
    (X : G) * (Y : G)^2 * C 1 2 + (X : G)^2 * C 2 0 +
    (X : G)^2 * (Y : G) * C 2 1 + (X : G)^2 * (Y : G)^2 * C 2 2

theorem long_weight_expansion_explicit (la lb : Option Bit) (X Y : ℤ)
    (ca da cb db : Fin 4) (T : G) :
    ((runWeight X la ca * runWeight X la da *
      runWeight Y lb cb * runWeight Y lb db : ℤ) : G) * T =
      biEval (fun i j => ((runPairWeight la ca da i *
        runPairWeight lb cb db j : ℤ) : G) * T) X Y := by
  rw [long_weight_expansion]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, biEval]
  norm_num
  ring

/-- 先对抽象被积项证明线性性，避免展开大规模四副本核。 -/
theorem biEval_sum {ι : Type*} [Fintype ι] (C : ι → Fin 3 → Fin 3 → G) (X Y : ℤ) :
    (∑ a, biEval (C a) X Y) = biEval (fun i j => ∑ a, C a i j) X Y := by
  simp only [biEval, Finset.sum_add_distrib, Finset.mul_sum]

/-- 真正的双变量恒等式：全部长度依赖由九个有限高斯整数系数决定。 -/
theorem longSum_expansion (la lb : Option Bit) (X Y : ℤ) (k : Fin 5) :
    longSum la lb X Y k = biEval (fun i j => longCoeff la lb i j k) X Y := by
  calc
    _ = ∑ f : Fin 4, ∑ s : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
        ∑ p : Fin 4, ∑ l : Fin 4, ∑ ca : Fin 4, ∑ da : Fin 4,
          ∑ cb : Fin 4, ∑ db : Fin 4,
            biEval (fun i j => ((runPairWeight la ca da i *
              runPairWeight lb cb db j : ℤ) : G) *
                longTerm la lb f s a b p l ca da cb db k) X Y := by
      unfold longSum
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro ca _
      apply Finset.sum_congr rfl
      intro da _
      apply Finset.sum_congr rfl
      intro cb _
      apply Finset.sum_congr rfl
      intro db _
      exact long_weight_expansion_explicit la lb X Y ca da cb db
        (longTerm la lb f s a b p l ca da cb db k)
    _ = _ := by simp only [biEval_sum] <;> rfl

end UnifiedEJM.PrefixKernel
