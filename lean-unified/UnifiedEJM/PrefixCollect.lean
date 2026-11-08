import Mathlib.Tactic

namespace UnifiedEJM.PrefixKernel

/-- 在评价昂贵的振幅前，先把相同有限状态的权重相加。 -/
def collectInsert {A W : Type*} [DecidableEq A] [AddCommMonoid W]
    (a : A) (w : W) : List (A × W) → List (A × W)
  | [] => [(a,w)]
  | (b,v)::xs => if a = b then (b,w+v)::xs else (b,v)::collectInsert a w xs

def collectWeights {A W : Type*} [DecidableEq A] [AddCommMonoid W] :
    List (A × W) → List (A × W)
  | [] => []
  | (a,w)::xs => collectInsert a w (collectWeights xs)

def weightedListEval {A W R : Type*} [AddCommMonoid W] [AddCommMonoid R]
    (h : A → W →+ R) : List (A × W) → R
  | [] => 0
  | (a,w)::xs => h a w + weightedListEval h xs

/-- 只要求评价对权重可加，适用于全部系数的数据积。 -/
theorem weightedListEval_insert {A W R : Type*} [DecidableEq A]
    [AddCommMonoid W] [AddCommMonoid R] (h : A → W →+ R)
    (a : A) (w : W) (xs : List (A × W)) :
    weightedListEval h (collectInsert a w xs) = h a w + weightedListEval h xs := by
  induction xs with
  | nil => simp [collectInsert, weightedListEval]
  | cons p xs ih =>
    obtain ⟨b,v⟩ := p
    by_cases hab : a = b
    · subst b
      simp [collectInsert, weightedListEval, map_add, add_assoc]
    · simp [collectInsert, weightedListEval, hab, ih, add_assoc, add_left_comm, add_comm]

/-- 合并状态的算法严格保持原求和，对任意振幅评价成立，无计算证书前提。 -/
theorem weightedListEval_collect {A W R : Type*} [DecidableEq A]
    [AddCommMonoid W] [AddCommMonoid R] (h : A → W →+ R)
    (xs : List (A × W)) :
    weightedListEval h (collectWeights xs) = weightedListEval h xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨a,w⟩ := p
    simp only [collectWeights, weightedListEval_insert, ih, weightedListEval]

end UnifiedEJM.PrefixKernel
