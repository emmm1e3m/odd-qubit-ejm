import Mathlib.Tactic

namespace UnifiedEJM.ClosureAggregation

/-- 按自然数偏移表示一小段索引；边界证明不参与有限表计算。 -/
def FinSlice {n : ℕ} (P : Fin n → Prop) (lo len : ℕ) : Prop :=
  ∀ i : Fin len, ∀ h : lo + i.val < n, P ⟨lo + i.val, h⟩

/-- 合并相邻两段，仅按索引所在半段选择已证明的结论。 -/
theorem finSlice_append {n lo left right : ℕ} {P : Fin n → Prop}
    (hleft : FinSlice P lo left)
    (hright : FinSlice P (lo + left) right) :
    FinSlice P lo (left + right) := by
  intro i hi
  by_cases h : i.val < left
  · exact hleft ⟨i.val, h⟩ hi
  · have hr : i.val - left < right := by omega
    have he : lo + left + (i.val - left) = lo + i.val := by omega
    have hb : lo + left + (i.val - left) < n := by omega
    have hh : P ⟨lo + left + (i.val - left), hb⟩ :=
      hright ⟨i.val - left, hr⟩ hb
    simpa only [he] using hh

/-- 从零开始的完整段恢复原来的全称接口。 -/
theorem finSlice_all {n : ℕ} {P : Fin n → Prop}
    (h : FinSlice P 0 n) : ∀ i : Fin n, P i := by
  intro i
  have hb : 0 + i.val < n := by omega
  have hh : P ⟨0 + i.val, hb⟩ := h i hb
  simpa only [Nat.zero_add] using hh

end UnifiedEJM.ClosureAggregation
