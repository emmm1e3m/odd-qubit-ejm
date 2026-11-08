import UnifiedEJM.PrefixFastWeights

open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

/-- 把跨割相位作为整数权重，避免它阻碍相同H状态的合并。 -/
def crossSign (a b : Fin 4) : ℤ :=
  if (pair a).1 = (pair a).2 ∨ (pair b).1 = (pair b).2 then 1 else -1

theorem crossSign_eq (a b : Fin 4) :
    gsign ((pair a).1 + (pair a).2) ^
      (if (pair b).1 = (pair b).2 then 0 else 1) = (crossSign a b : G) := by
  revert a b
  decide +kernel

def stateKernelData (nu : Bit) (f s p l : Fin 4) (st : LongState) : Data5 :=
  let rf := rep true f
  let rs := rep true s
  let rp := rep false p
  let rl := rep false l
  quartetData (fun r => H ![rf r, rs r, rp r, rl r] (st.1 r) (st.2 r) nu)

theorem stateTermData_unscaled (nu : Bit) (f s a b p l : Fin 4) (st : LongState) :
    stateTermData nu f s a b p l st =
      scale5 (crossSign a b : G) (stateKernelData nu f s p l st) := by
  simp only [stateTermData, stateKernelData, crossSign_eq]

theorem weightDataHom_scale5 (q : Data5) (w : WeightData) (z : ℤ) :
    weightDataHom (scale5 (z : G) q) w = weightDataHom q (z • w) := by
  apply data45_ext
  intro i j k
  rw [weightDataHom_spec, weightDataHom_spec, pick5_scale5]
  simp only [map_zsmul]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_id]
  ring

def wholeStateWeightHom (la lb : Option Bit) (f s p l : Fin 4)
    (st : LongState) : WeightData →+ Data45 :=
  fastWeightDataHom (stateKernelData (la.getD 0 + lb.getD 0) f s p l st)

theorem wholeState_weight_atom (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) :
    wholeStateWeightHom la lb f s p l (longState la lb f s a b p l ca da cb db)
      (crossSign a b • outerWeights (runPairWeight la ca da) (runPairWeight lb cb db)) =
        weighted45 (runPairWeight la ca da) (runPairWeight lb cb db)
          (longTermData la lb f s a b p l ca da cb db) := by
  unfold wholeStateWeightHom
  rw [fastWeightDataHom_eq, ← weightDataHom_scale5, ← stateTermData_unscaled, stateTermData_spec,
    weightDataHom_outer]

/-- 固定(p,l)后同时合并两个跨割位对及四个类别，共4096个便宜的状态项。 -/
def longBlockClassList (la lb : Option Bit) (f s p l : Fin 4) :
    List (LongState × WeightData) :=
  bindFin 4 fun a => bindFin 4 fun b =>
    bindFin 4 fun ca => bindFin 4 fun da => bindFin 4 fun cb => bindFin 4 fun db =>
      [(longState la lb f s a b p l ca da cb db,
        crossSign a b • outerWeights (runPairWeight la ca da) (runPairWeight lb cb db))]

theorem longBlockClassList_eval (la lb : Option Bit) (f s p l : Fin 4) :
    weightedListEval (wholeStateWeightHom la lb f s p l) (longBlockClassList la lb f s p l) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        ∑ ca : Fin 4, ∑ da : Fin 4, ∑ cb : Fin 4, ∑ db : Fin 4,
          weighted45 (runPairWeight la ca da) (runPairWeight lb cb db)
            (longTermData la lb f s a b p l ca da cb db) := by
  simp only [longBlockClassList, weightedListEval_bindFin, weightedListEval,
    add_zero, wholeState_weight_atom]

theorem sum_swap_pairs {I J K L R : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] [AddCommMonoid R]
    (F : I → J → K → L → R) :
    (∑ p : I, ∑ l : J, ∑ a : K, ∑ b : L, F p l a b) =
      ∑ a : K, ∑ b : L, ∑ p : I, ∑ l : J, F p l a b := by
  calc
    _ = ∑ p : I, ∑ a : K, ∑ b : L, ∑ l : J, F p l a b := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

/-- 整个原LongBlock一次返回45分量；最终144个模块接口无需改变。 -/
def longBlockCollectedData (la lb : Option Bit) (f s : Fin 4) : Data45 :=
  ∑ p : Fin 4, ∑ l : Fin 4,
    weightedListEval (wholeStateWeightHom la lb f s p l)
      (collectWeights (longBlockClassList la lb f s p l))

theorem longBlockCollectedData_eq (la lb : Option Bit) (f s : Fin 4) :
    longBlockCollectedData la lb f s =
      ∑ a : Fin 4, ∑ b : Fin 4, longCrossBlockData la lb f s a b := by
  simp only [longBlockCollectedData, weightedListEval_collect, longBlockClassList_eval,
    longCrossBlockData]
  exact sum_swap_pairs (fun p l a b =>
    ∑ ca : Fin 4, ∑ da : Fin 4, ∑ cb : Fin 4, ∑ db : Fin 4,
      weighted45 (runPairWeight la ca da) (runPairWeight lb cb db)
        (longTermData la lb f s a b p l ca da cb db))

theorem longBlockCollectedData_spec (la lb : Option Bit) (f s : Fin 4)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (longBlockCollectedData la lb f s) i j k =
      longBlock la lb f s i j k := by
  rw [longBlockCollectedData_eq]
  simp only [coefficient45_sum, longCrossBlockData_spec]
  exact (longBlock_crossBlocks la lb f s i j k).symm

end UnifiedEJM.PrefixKernel
