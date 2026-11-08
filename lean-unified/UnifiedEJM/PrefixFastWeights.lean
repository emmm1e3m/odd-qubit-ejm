import UnifiedEJM.PrefixGroupedKernel

open OddEJM UnifiedEJM.PhysicsFinite

namespace UnifiedEJM.PrefixKernel

/-- 显式高斯整数乘法，并保留零权重的提前删除；不使用线性递归zsmul。 -/
def fastScale5 (w : ℤ) (q : Data5) : Data5 :=
  if w = 0 then 0 else scale5 (w : G) q

theorem pick5_fastScale5 (w : ℤ) (q : Data5) (k : Fin 5) :
    pick5Hom k (fastScale5 w q) = (w : G) * pick5Hom k q := by
  by_cases h : w = 0
  · simp only [fastScale5, h, ite_true, map_zero, Int.cast_zero, zero_mul]
  · simp only [fastScale5, h, ite_false, pick5_scale5]

theorem fastScale5_eq (w : ℤ) (q : Data5) : fastScale5 w q = w • q := by
  apply data5_ext
  intro k
  rw [pick5_fastScale5, map_zsmul, zsmul_eq_mul]

def fastWeightDataHom (q : Data5) : WeightData →+ Data45 where
  toFun w :=
    ((fastScale5 w.1.1 q, fastScale5 w.1.2.1 q, fastScale5 w.1.2.2 q),
     (fastScale5 w.2.1.1 q, fastScale5 w.2.1.2.1 q, fastScale5 w.2.1.2.2 q),
     (fastScale5 w.2.2.1 q, fastScale5 w.2.2.2.1 q, fastScale5 w.2.2.2.2 q))
  map_zero' := by simp [fastScale5]
  map_add' w v := by
    simp only [fastScale5_eq]
    exact (weightDataHom q).map_add w v

theorem fastWeightDataHom_spec (q : Data5) (w : WeightData)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (fastWeightDataHom q w) i j k =
      ((pick3Hom j (pick3Hom i w) : ℤ) : G) * pick5Hom k q := by
  fin_cases i <;> fin_cases j <;> exact pick5_fastScale5 _ q k

/-- 新计算实现与已核验的加法同态完全相等，可直接沿用保和证明。 -/
theorem fastWeightDataHom_eq (q : Data5) : fastWeightDataHom q = weightDataHom q := by
  apply AddMonoidHom.ext
  intro w
  apply data45_ext
  intro i j k
  rw [fastWeightDataHom_spec, weightDataHom_spec]

end UnifiedEJM.PrefixKernel
