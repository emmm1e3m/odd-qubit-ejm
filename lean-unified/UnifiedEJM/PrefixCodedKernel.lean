import UnifiedEJM.PrefixWholeGroupedKernel

open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

/-- 八位状态在产生原项时编码；收集算法只比较自然数，不比较函数。 -/
def encodeLongState (st : LongState) : ℕ :=
  (st.1 0).val + 2 * (st.1 1).val + 4 * (st.1 2).val + 8 * (st.1 3).val +
    (if st.2 0 then 16 else 0) + (if st.2 1 then 32 else 0) +
    (if st.2 2 then 64 else 0) + (if st.2 3 then 128 else 0)

/-- 仅对收集后留下的状态恢复H所需的四副本奇偶与常量标志。 -/
def decodeLongState (code : ℕ) : LongState :=
  (fun r => ((code / 2 ^ r.val : ℕ) : Bit), fun r => code.testBit (4 + r.val))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decode_encodeLongState (st : LongState) :
    decodeLongState (encodeLongState st) = st := by
  revert st
  decide +kernel

def codeStateWeightHom (la lb : Option Bit) (f s p l : Fin 4)
    (code : ℕ) : WeightData →+ Data45 :=
  wholeStateWeightHom la lb f s p l (decodeLongState code)

theorem codeState_weight_atom (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) :
    codeStateWeightHom la lb f s p l
      (encodeLongState (longState la lb f s a b p l ca da cb db))
      (crossSign a b • outerWeights (runPairWeight la ca da) (runPairWeight lb cb db)) =
        weighted45 (runPairWeight la ca da) (runPairWeight lb cb db)
          (longTermData la lb f s a b p l ca da cb db) := by
  unfold codeStateWeightHom
  rw [decode_encodeLongState]
  exact wholeState_weight_atom la lb f s a b p l ca da cb db

/-- 与原4096项同序构造，每个列表键已经是整数码。 -/
def longBlockCodeClassList (la lb : Option Bit) (f s p l : Fin 4) :
    List (ℕ × WeightData) :=
  bindFin 4 fun a => bindFin 4 fun b =>
    bindFin 4 fun ca => bindFin 4 fun da => bindFin 4 fun cb => bindFin 4 fun db =>
      [(encodeLongState (longState la lb f s a b p l ca da cb db),
        crossSign a b • outerWeights (runPairWeight la ca da) (runPairWeight lb cb db))]

theorem longBlockCodeClassList_eval (la lb : Option Bit) (f s p l : Fin 4) :
    weightedListEval (codeStateWeightHom la lb f s p l)
      (longBlockCodeClassList la lb f s p l) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        ∑ ca : Fin 4, ∑ da : Fin 4, ∑ cb : Fin 4, ∑ db : Fin 4,
          weighted45 (runPairWeight la ca da) (runPairWeight lb cb db)
            (longTermData la lb f s a b p l ca da cb db) := by
  simp only [longBlockCodeClassList, weightedListEval_bindFin, weightedListEval,
    add_zero, codeState_weight_atom]

def longBlockCodeData (la lb : Option Bit) (f s : Fin 4) : Data45 :=
  ∑ p : Fin 4, ∑ l : Fin 4,
    weightedListEval (codeStateWeightHom la lb f s p l)
      (collectWeights (longBlockCodeClassList la lb f s p l))

/-- 编码只改变收集的实现，精确返回已证的整个原LongBlock数据。 -/
theorem longBlockCodeData_eq (la lb : Option Bit) (f s : Fin 4) :
    longBlockCodeData la lb f s = longBlockCollectedData la lb f s := by
  simp only [longBlockCodeData, longBlockCollectedData, weightedListEval_collect,
    longBlockCodeClassList_eval, longBlockClassList_eval]

theorem longBlockCodeData_spec (la lb : Option Bit) (f s : Fin 4)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (longBlockCodeData la lb f s) i j k =
      longBlock la lb f s i j k := by
  rw [longBlockCodeData_eq, longBlockCollectedData_spec]

end UnifiedEJM.PrefixKernel
