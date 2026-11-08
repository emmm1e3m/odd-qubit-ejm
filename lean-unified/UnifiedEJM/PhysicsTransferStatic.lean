import UnifiedEJM.PhysicsWeightedTransfer
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open OddEJM
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer

attribute [local instance] Classical.propDecidable

/-- 左边界值单独给出；右端越界由原始coord取零。 -/
def previous {n : ℕ} (p : Bit) (v : Bits n) (j : ℕ) : Bit :=
  if j = 0 then p else coord v (j - 1)

/-- 独立静态语义：一次选出所有物理位，逐位施加B侧零支撑。 -/
def supported {n : ℕ} (sites : Fin n → Site) (v : Bits n) : Prop :=
  ∀ j, allowed (sites j) (v j)

/-- 独立静态语义：每一个物理站点的左右邻位约束。 -/
def localValid {n : ℕ} (d : Logical) (sites : Fin n → Site)
    (p : Bit) (v : Bits n) : Prop :=
  ∀ j, constraint (sites j) d (previous p v j.val) (coord v (j.val + 1))

def totalCharge {n : ℕ} (sites : Fin n → Site) (v : Bits n) : Logical :=
  ∑ j, charge (sites j).word (v j)

def siteFactor {n : ℕ} (sites : Fin n → Site) : ℚ :=
  ∏ j, siteWeight (sites j)

/-- 全部Fin n赋值上的单一有限和；没有递归定义或消元假设。
    headGuard只为从任意转移前缀继续计算而保留，完整物理计数取True。 -/
def staticSum {n : ℕ} (d : Logical) (sites : Fin n → Site)
    (p : Bit) (acc k : Logical) (headGuard : Bit → Prop) : ℚ := by
  classical
  exact ∑ v : Bits n,
    if headGuard (coord v 0) ∧ supported sites v ∧ localValid d sites p v ∧
        acc + totalCharge sites v = k
    then siteFactor sites else 0

@[simp] theorem coord_cons_zero {n : ℕ} (q : Bit) (v : Bits n) :
    coord (Fin.cons q v) 0 = q := by
  simp [coord]

@[simp] theorem coord_cons_succ {n : ℕ} (q : Bit) (v : Bits n) (j : ℕ) :
    coord (Fin.cons q v) (j + 1) = coord v j := by
  by_cases hj : j < n
  · simp only [coord, dif_pos hj, dif_pos (show j + 1 < n + 1 by omega)]
    change Fin.cons (α := fun _ => Bit) q v (Fin.succ ⟨j, hj⟩) = v ⟨j, hj⟩
    exact Fin.cons_succ (α := fun _ => Bit) q v ⟨j, hj⟩
  · simp [coord, hj, show ¬j + 1 < n + 1 by omega]

@[simp] theorem previous_cons_zero {n : ℕ} (p q : Bit) (v : Bits n) :
    previous p (Fin.cons q v) 0 = p := by simp [previous]

@[simp] theorem previous_cons_succ {n : ℕ} (p q : Bit) (v : Bits n) (j : ℕ) :
    previous p (Fin.cons q v) (j + 1) = previous q v j := by
  cases j with
  | zero => simp [previous]
  | succ j => simp [previous, Nat.succ_eq_add_one]

theorem supported_cons {n : ℕ} (a : Site) (sites : Fin n → Site)
    (q : Bit) (v : Bits n) :
    supported (Fin.cons a sites) (Fin.cons q v) ↔
      allowed a q ∧ supported sites v := by
  simp [supported, Fin.forall_fin_succ]

theorem localValid_cons {n : ℕ} (d : Logical) (a : Site)
    (sites : Fin n → Site) (p q : Bit) (v : Bits n) :
    localValid d (Fin.cons a sites) p (Fin.cons q v) ↔
      constraint a d p (coord v 0) ∧ localValid d sites q v := by
  simp [localValid, Fin.forall_fin_succ]

@[simp] theorem totalCharge_cons {n : ℕ} (a : Site) (sites : Fin n → Site)
    (q : Bit) (v : Bits n) :
    totalCharge (Fin.cons a sites) (Fin.cons q v) =
      charge a.word q + totalCharge sites v := by
  simp [totalCharge, Fin.sum_univ_succ]

@[simp] theorem siteFactor_cons {n : ℕ} (a : Site) (sites : Fin n → Site) :
    siteFactor (Fin.cons a sites) = siteWeight a * siteFactor sites := by
  simp [siteFactor, Fin.prod_univ_succ]

/-- 全赋值有限和按首比特分组，使用Fin.cons的实际双射。 -/
theorem sum_bits_cons {n : ℕ} (f : Bits (n + 1) → ℚ) :
    (∑ v, f v) = ∑ q : Bit, ∑ v : Bits n, f (Fin.cons q v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bit)).sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

theorem staticSum_zero (d : Logical) (sites : Fin 0 → Site)
    (p : Bit) (acc k : Logical) (headGuard : Bit → Prop) :
    staticSum d sites p acc k headGuard =
      if headGuard 0 ∧ acc = k then 1 else 0 := by
  classical
  simp [staticSum, supported, localValid, totalCharge, siteFactor, coord]

/-- 逐位求平均是从静态全赋值和推出的递推式。 -/
theorem staticSum_cons {n : ℕ} (d : Logical) (a : Site)
    (sites : Fin n → Site) (p : Bit) (acc k : Logical)
    (headGuard : Bit → Prop) :
    staticSum d (Fin.cons a sites) p acc k headGuard =
      ∑ q : Bit, if allowed a q ∧ headGuard q then
        siteWeight a * staticSum d sites q (acc + charge a.word q) k
          (fun r => constraint a d p r) else 0 := by
  classical
  unfold staticSum
  rw [sum_bits_cons]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : allowed a q ∧ headGuard q
  · rw [if_pos h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [coord_cons_zero, supported_cons, localValid_cons,
      totalCharge_cons, siteFactor_cons]
    by_cases hv : constraint a d p (coord v 0) ∧ supported sites v ∧
        localValid d sites q v ∧ (acc + charge a.word q) + totalCharge sites v = k
    · have he : acc + (charge a.word q + totalCharge sites v) = k := by
        simpa only [add_assoc] using hv.2.2.2
      simp [h.1, h.2, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, he]
    · have hn : ¬(headGuard q ∧ (allowed a q ∧ supported sites v) ∧
          (constraint a d p (coord v 0) ∧ localValid d sites q v) ∧
          acc + (charge a.word q + totalCharge sites v) = k) := by
        intro hh
        exact hv ⟨hh.2.2.1.1, hh.2.1.2, hh.2.2.1.2,
          by simpa only [add_assoc] using hh.2.2.2⟩
      simp [hv, hn]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro v _
    simp only [coord_cons_zero, supported_cons, localValid_cons,
      totalCharge_cons, siteFactor_cons]
    have hn : ¬(headGuard q ∧ (allowed a q ∧ supported sites v) ∧
        (constraint a d p (coord v 0) ∧ localValid d sites q v) ∧
        acc + (charge a.word q + totalCharge sites v) = k) := by
      intro hh
      exact h ⟨hh.2.1.1, hh.1⟩
    exact if_neg hn

/-- 任意有限物理后缀的递归求和，等于其全部Fin n赋值的静态约束和。 -/
theorem pathSum_eq_staticSum {n : ℕ} (d : Logical) (sites : Fin n → Site)
    (a : Site) (s : Memory) (k : Logical) :
    pathSum d a (List.ofFn sites)
        (terminal d (finalSite a (List.ofFn sites)) k) s =
      staticSum d sites s.2.2 s.1 k (fun r => constraint a d s.2.1 r) := by
  induction n generalizing a s with
  | zero =>
      rw [staticSum_zero]
      simp [List.ofFn_zero, pathSum, finalSite, terminal, and_comm]
  | succ n ih =>
      obtain ⟨b, rest, rfl⟩ : ∃ b : Site, ∃ rest : Fin n → Site,
          sites = Fin.cons b rest :=
        ⟨sites 0, Fin.tail sites, (Fin.cons_self_tail sites).symm⟩
      simp only [List.ofFn_cons]
      rw [staticSum_cons]
      change (∑ q : Bit, if allowed b q ∧ constraint a d s.2.1 q then
        siteWeight b *
          pathSum d b (List.ofFn rest)
            (terminal d (finalSite b (List.ofFn rest)) k)
            (push b.word s q) else 0) = _
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : allowed b q ∧ constraint a d s.2.1 q
      · simp [h, ih, push]
      · simp [h]

/-- 从初始平均到右端封闭的完整动态规划，等于一次性静态赋值计数。 -/
theorem finish_evolve_eq_staticSum {n : ℕ} (d : Logical)
    (a : Site) (sites : Fin n → Site) (k : Logical) :
    finish d (finalSite a (List.ofFn sites))
        (evolve d a (List.ofFn sites) (initial a)) k =
      staticSum d (Fin.cons a sites) 0 0 k (fun _ => True) := by
  rw [finish_pairing, evolve_pairing, initial_pairing, staticSum_cons]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : allowed a q
  · simp only [h, true_and, and_true, if_true, pathSum_eq_staticSum, zero_add]
  · simp only [h, false_and, if_false]

/-- 完整静态计数中的头部保护恒真，归一化因子独立于赋值。 -/
theorem staticSum_unconditional {n : ℕ} (d : Logical)
    (sites : Fin n → Site) (k : Logical) :
    staticSum d sites 0 0 k (fun _ => True) =
      siteFactor sites * ∑ v : Bits n,
        if supported sites v ∧ localValid d sites 0 v ∧ totalCharge sites v = k
        then 1 else 0 := by
  classical
  simp only [staticSum, true_and, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

end UnifiedEJM.WeightedTransfer
