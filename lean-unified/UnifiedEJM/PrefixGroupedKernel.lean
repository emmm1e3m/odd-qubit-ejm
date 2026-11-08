import UnifiedEJM.PrefixDataKernel
import UnifiedEJM.PrefixCollect
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

abbrev WeightData := Data3 (Data3 ℤ)
abbrev LongState := Bits 4 × (Fin 4 → Bool)

theorem data3_ext {A : Type*} [AddCommMonoid A] {x y : Data3 A}
    (h : ∀ i : Fin 3, pick3Hom i x = pick3Hom i y) : x = y :=
  Prod.ext (h 0) (Prod.ext (h 1) (h 2))

theorem data5_ext {x y : Data5}
    (h : ∀ k : Fin 5, pick5Hom k x = pick5Hom k y) : x = y :=
  Prod.ext (h 0) (Prod.ext (h 1) (Prod.ext (h 2) (Prod.ext (h 3) (h 4))))

theorem data45_ext {x y : Data45}
    (h : ∀ i j : Fin 3, ∀ k : Fin 5, coefficient45 x i j k = coefficient45 y i j k) :
    x = y := by
  apply data3_ext
  intro i
  apply data3_ext
  intro j
  apply data5_ext
  intro k
  exact h i j k

/-- 固定五个Laurent分量后，对九个长度权重的评价是加法同态。 -/
def weightDataHom (q : Data5) : WeightData →+ Data45 where
  toFun w :=
    ((w.1.1 • q, w.1.2.1 • q, w.1.2.2 • q),
     (w.2.1.1 • q, w.2.1.2.1 • q, w.2.1.2.2 • q),
     (w.2.2.1 • q, w.2.2.2.1 • q, w.2.2.2.2 • q))
  map_zero' := by simp
  map_add' w v := by simp [add_zsmul, add_mul]

theorem weightDataHom_spec (q : Data5) (w : WeightData)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (weightDataHom q w) i j k =
      ((pick3Hom j (pick3Hom i w) : ℤ) : G) * pick5Hom k q := by
  have hs (a : ℤ) : pick5Hom k (a • q) = (a : G) * pick5Hom k q := by
    rw [map_zsmul, zsmul_eq_mul]
  fin_cases i <;> fin_cases j <;> exact hs _

def outerWeights (a b : Fin 3 → ℤ) : WeightData :=
  ((a 0*b 0, a 0*b 1, a 0*b 2),
   (a 1*b 0, a 1*b 1, a 1*b 2),
   (a 2*b 0, a 2*b 1, a 2*b 2))

theorem outerWeights_spec (a b : Fin 3 → ℤ) (i j : Fin 3) :
    pick3Hom j (pick3Hom i (outerWeights a b)) = a i * b j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem weightDataHom_outer (a b : Fin 3 → ℤ) (q : Data5) :
    weightDataHom q (outerWeights a b) = weighted45 a b q := by
  apply data45_ext
  intro i j k
  rw [weightDataHom_spec, outerWeights_spec, weighted45_spec]
  by_cases h : a i * b j = 0
  · simp only [h, ite_true, Int.cast_zero, zero_mul]
  · simp only [h, ite_false]

/-- 类别进入H所需的全部信息：四副本的奇偶与常量串标志。 -/
def longState (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) : LongState :=
  let rf := rep true f
  let rs := rep true s
  let ra := rep true a
  let rb := rep false b
  let rp := rep false p
  let rl := rep false l
  let pa := replica true (runParity la ca) (runParity la da)
  let pb := replica false (runParity lb cb) (runParity lb db)
  let ac := catRep true ca da
  let bc := catRep false cb db
  (fun r => ra r + rb r + pa r + pb r,
   fun r => decide (rs r = rf r ∧ ra r = rf r ∧ rb r = rf r ∧
       rp r = rf r ∧ rl r = rf r) &&
     runMatches la (ac r) (rf r) && runMatches lb (bc r) (rf r))

def stateTermData (nu : Bit) (f s a b p l : Fin 4) (st : LongState) : Data5 :=
  let rf := rep true f
  let rs := rep true s
  let rp := rep false p
  let rl := rep false l
  let sg := gsign ((pair a).1 + (pair a).2) ^
    (if (pair b).1 = (pair b).2 then 0 else 1)
  scale5 sg (quartetData (fun r => H ![rf r, rs r, rp r, rl r] (st.1 r) (st.2 r) nu))

theorem stateTermData_spec (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) :
    stateTermData (la.getD 0 + lb.getD 0) f s a b p l
      (longState la lb f s a b p l ca da cb db) =
        longTermData la lb f s a b p l ca da cb db := rfl

def stateWeightHom (la lb : Option Bit) (f s a b p l : Fin 4)
    (st : LongState) : WeightData →+ Data45 :=
  weightDataHom (stateTermData (la.getD 0 + lb.getD 0) f s a b p l st)

def bindFin {A : Type*} (n : ℕ) (f : Fin n → List A) : List A :=
  (List.ofFn (fun i : Fin n => i)).flatMap f

theorem weightedListEval_append {A W R : Type*} [AddCommMonoid W] [AddCommMonoid R]
    (h : A → W →+ R) (xs ys : List (A × W)) :
    weightedListEval h (xs ++ ys) = weightedListEval h xs + weightedListEval h ys := by
  induction xs with
  | nil => simp [weightedListEval]
  | cons p xs ih =>
    obtain ⟨a,w⟩ := p
    simp [weightedListEval, ih, add_assoc]

theorem weightedListEval_flatMap {A B W R : Type*}
    [AddCommMonoid W] [AddCommMonoid R] (h : A → W →+ R)
    (g : B → List (A × W)) (xs : List B) :
    weightedListEval h (xs.flatMap g) = (xs.map (fun b => weightedListEval h (g b))).sum := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.flatMap_cons, weightedListEval_append, List.map_cons, List.sum_cons, ih]

theorem weightedListEval_bindFin {A W R : Type*} [AddCommMonoid W] [AddCommMonoid R]
    (h : A → W →+ R) (n : ℕ) (g : Fin n → List (A × W)) :
    weightedListEval h (bindFin n g) = ∑ i : Fin n, weightedListEval h (g i) := by
  rw [bindFin, weightedListEval_flatMap]
  simp only [List.map_ofFn, Function.comp_apply, List.sum_ofFn]

/-- 256个原类别组合只生成便宜的状态和九维整数权重，不计算H。 -/
def longClassList (la lb : Option Bit) (f s a b p l : Fin 4) : List (LongState × WeightData) :=
  bindFin 4 fun ca => bindFin 4 fun da => bindFin 4 fun cb => bindFin 4 fun db =>
    [(longState la lb f s a b p l ca da cb db,
      outerWeights (runPairWeight la ca da) (runPairWeight lb cb db))]

theorem longClassList_eval (la lb : Option Bit) (f s a b p l : Fin 4) :
    weightedListEval (stateWeightHom la lb f s a b p l) (longClassList la lb f s a b p l) =
      ∑ ca : Fin 4, ∑ da : Fin 4, ∑ cb : Fin 4, ∑ db : Fin 4,
        weighted45 (runPairWeight la ca da) (runPairWeight lb cb db)
          (longTermData la lb f s a b p l ca da cb db) := by
  simp only [longClassList, weightedListEval_bindFin, weightedListEval, add_zero,
    stateWeightHom, stateTermData_spec, weightDataHom_outer]

/-- 先合并状态，再一次返回全部45分量；原核接口保留。 -/
def longCrossBlockCollectedData (la lb : Option Bit) (f s a b : Fin 4) : Data45 :=
  ∑ p : Fin 4, ∑ l : Fin 4,
    weightedListEval (stateWeightHom la lb f s a b p l)
      (collectWeights (longClassList la lb f s a b p l))

theorem longCrossBlockCollectedData_eq (la lb : Option Bit) (f s a b : Fin 4) :
    longCrossBlockCollectedData la lb f s a b = longCrossBlockData la lb f s a b := by
  simp only [longCrossBlockCollectedData, weightedListEval_collect, longClassList_eval,
    longCrossBlockData]

theorem longCrossBlockCollectedData_spec (la lb : Option Bit) (f s a b : Fin 4)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (longCrossBlockCollectedData la lb f s a b) i j k =
      longCrossBlock la lb f s a b i j k := by
  rw [longCrossBlockCollectedData_eq, longCrossBlockData_spec]

end UnifiedEJM.PrefixKernel
