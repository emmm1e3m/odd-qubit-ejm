import UnifiedEJM.PhysicsTransferStatic
import UnifiedEJM.GraphLocalConstraints

noncomputable section
set_option backward.isDefEq.respectTransparency false
open OddEJM
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer

/-- 真实物理割的逐站颜色与W行向量。 -/
def physicalSites {n : ℕ} (S : Finset (Fin n)) (j : Fin n) : Site :=
  ⟨decide (j ∈ S), GraphBackground.rowWord n j⟩

theorem supported_physicalSites {n : ℕ} (S : Finset (Fin n)) (v : Bits n) :
    supported (physicalSites S) v ↔ GraphBackground.SupportedOn S v := by
  change (∀ j, decide (j ∈ S) = true ∨ v j = 0) ↔ (∀ j, j ∉ S → v j = 0)
  simp only [decide_eq_true_eq]
  constructor
  · intro h j hj
    exact (h j).resolve_left hj
  · intro h j
    by_cases hj : j ∈ S
    · exact Or.inl hj
    · exact Or.inr (h j hj)

theorem localValid_physicalSites {n : ℕ} (S : Finset (Fin n))
    (d : Logical) (v : Bits n) :
    localValid d (physicalSites S) 0 v ↔ GraphBackground.LocalConstraints S d v := by
  change (∀ j : Fin n, decide (j ∈ S) = true ∨
      previous 0 v j.val + coord v (j.val + 1) = dot (GraphBackground.rowWord n j) d) ↔ _
  simp only [decide_eq_true_eq]
  change (∀ j : Fin n, j ∈ S ∨
      GraphBackground.leftNeighbor v j.val + coord v (j.val + 1) =
        OddEJM.dot (GraphBackground.rowWord n j) d) ↔
    (∀ j : Fin n, j ∉ S →
      GraphBackground.leftNeighbor v j.val + coord v (j.val + 1) =
        OddEJM.dot (GraphBackground.rowWord n j) d)
  constructor
  · intro h j hj
    exact (h j).resolve_left hj
  · intro h j
    by_cases hj : j ∈ S
    · exact Or.inl hj
    · exact Or.inr (h j hj)

theorem totalCharge_physicalSites {n : ℕ} (S : Finset (Fin n)) (v : Bits n) :
    totalCharge (physicalSites S) v = GraphBackground.graphFeature v := by
  rw [GraphBackground.graphFeature_sum_charge]
  apply Finset.sum_congr rfl
  intro j _
  funext i
  rfl

/-- 对每个A位乘1/2、每个B位乘1，严格等于2^-|A|。 -/
theorem siteFactor_physicalSites {n : ℕ} (S : Finset (Fin n)) :
    siteFactor (physicalSites S) = (1 / 2 : ℚ) ^ S.card := by
  simp [siteFactor, siteWeight, physicalSites]

/-- 图态Pauli展开给出的真实静态权重，逐项接入独立Fin n赋值和。 -/
theorem physicalWeight_eq_staticSum {n : ℕ} (S : Finset (Fin n)) (d k : Logical) :
    GraphBackground.physicalWeight S d k =
      staticSum d (physicalSites S) 0 0 k (fun _ => True) := by
  rw [staticSum_unconditional, siteFactor_physicalSites]
  unfold GraphBackground.physicalWeight
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [supported_physicalSites S v, localValid_physicalSites S d v,
    totalCharge_physicalSites S v]

/-- 动态规划的列表包装；非空列表直接使用原initial/evolve/finish。 -/
def listWeight (d k : Logical) : List Site → ℚ
  | [] => if k = 0 then 1 else 0
  | a :: bs => finish d (finalSite a bs) (evolve d a bs (initial a)) k

theorem listWeight_ofFn {n : ℕ} (d k : Logical) (sites : Fin n → Site) :
    listWeight d k (List.ofFn sites) =
      staticSum d sites 0 0 k (fun _ => True) := by
  cases n with
  | zero =>
      rw [staticSum_zero]
      simp [listWeight, eq_comm]
  | succ n =>
      obtain ⟨a, rest, rfl⟩ : ∃ a : Site, ∃ rest : Fin n → Site,
          sites = Fin.cons a rest :=
        ⟨sites 0, Fin.tail sites, (Fin.cons_self_tail sites).symm⟩
      rw [List.ofFn_cons]
      exact finish_evolve_eq_staticSum d a rest k

/-- 任意物理长度与任意割的静态权重到动态规划桥。 -/
theorem physicalWeight_eq_listWeight {n : ℕ} (S : Finset (Fin n)) (d k : Logical) :
    GraphBackground.physicalWeight S d k = listWeight d k (List.ofFn (physicalSites S)) := by
  rw [physicalWeight_eq_staticSum, listWeight_ofFn]

theorem finalSite_append (a : Site) (xs ys : List Site) :
    finalSite a (xs ++ ys) = finalSite (finalSite a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => exact ih b

theorem finalSite_backgroundTail (first second : Bool) (middle : List Bool)
    (penultimate last : Bool) :
    finalSite ⟨first, firstWord⟩ (backgroundTail second middle penultimate last) =
      (⟨last, firstWord⟩ : Site) := by
  simp [backgroundTail, finalSite_append, finalSite]

theorem listWeight_background (first second : Bool) (middle : List Bool)
    (penultimate last : Bool) (d k : Logical) :
    listWeight d k (⟨first, firstWord⟩ :: backgroundTail second middle penultimate last) =
      backgroundWeight first second middle penultimate last d k := by
  simp only [listWeight, backgroundWeight, finalSite_backgroundTail]

/-- 任意长元组拆成两个首位、中央所有位和两个尾位，顺序保持不变。 -/
theorem ofFn_split_four {α : Type*} {m : ℕ} (f : Fin (m + 4) → α) :
    List.ofFn f =
      [f ⟨0, by omega⟩, f ⟨1, by omega⟩] ++
      List.ofFn (fun j : Fin m => f ⟨j.val + 2, by omega⟩) ++
      [f ⟨m + 2, by omega⟩, f ⟨m + 3, by omega⟩] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ', List.ofFn_succ']
  simp only [List.concat_eq_append, List.cons_append, List.nil_append, List.append_assoc] <;> rfl

def middleColors {m : ℕ} (S : Finset (Fin (m + 4))) : List Bool :=
  List.ofFn (fun j : Fin m => decide ((⟨j.val + 2, by omega⟩ : Fin (m + 4)) ∈ S))

/-- 4,1,8,...,8,2,4来自每一个真实物理站点，不从有限样本外推。 -/
theorem physicalSites_ofFn {m : ℕ} (hm : 1 ≤ m) (S : Finset (Fin (m + 4))) :
    List.ofFn (physicalSites S) =
      (⟨decide ((⟨0, by omega⟩ : Fin (m + 4)) ∈ S), firstWord⟩ : Site) ::
        backgroundTail (decide ((⟨1, by omega⟩ : Fin (m + 4)) ∈ S)) (middleColors S)
          (decide ((⟨m + 2, by omega⟩ : Fin (m + 4)) ∈ S))
          (decide ((⟨m + 3, by omega⟩ : Fin (m + 4)) ∈ S)) := by
  have hn : 5 ≤ m + 4 := by omega
  have hfirst : GraphBackground.rowWord (m + 4) ⟨0, by omega⟩ = firstWord := by
    simp [GraphBackground.rowWord_formula hn, firstWord]
  have hsecond : GraphBackground.rowWord (m + 4) ⟨1, by omega⟩ = secondWord := by
    simp [GraphBackground.rowWord_formula hn, secondWord]
  have hpenultimate : GraphBackground.rowWord (m + 4) ⟨m + 2, by omega⟩ =
      penultimateWord := by
    simp [GraphBackground.rowWord_formula hn, penultimateWord,
      show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega]
  have hlast : GraphBackground.rowWord (m + 4) ⟨m + 3, by omega⟩ = firstWord := by
    simp [GraphBackground.rowWord_formula hn, firstWord,
      show m + 3 ≠ 0 by omega, show m + 3 ≠ 1 by omega]
  have hmiddle (j : Fin m) :
      GraphBackground.rowWord (m + 4) ⟨j.val + 2, by omega⟩ = middleWord := by
    have hj := j.isLt
    simp [GraphBackground.rowWord_formula hn, middleWord,
      show j.val + 2 ≠ 0 by omega, show j.val + 2 ≠ 1 by omega,
      show j.val + 2 ≠ m + 2 by omega, show j.val + 2 ≠ m + 3 by omega,
      show j.val ≠ m by omega, show j.val ≠ m + 1 by omega]
  rw [ofFn_split_four]
  simp only [physicalSites, hfirst, hsecond, hpenultimate, hlast, hmiddle]
  simp [backgroundTail, middleSites, middleColors, List.map_ofFn, Function.comp_def]

/-- 实际Fin n全赋值计数恰等于闭包证书使用的backgroundWeight。
    参数m=n-4任意且至少一位，故覆盖所有n≥5与任意物理割。 -/
theorem physicalWeight_eq_backgroundWeight {m : ℕ} (hm : 1 ≤ m)
    (S : Finset (Fin (m + 4))) (d k : Logical) :
    GraphBackground.physicalWeight S d k =
      backgroundWeight
        (decide ((⟨0, by omega⟩ : Fin (m + 4)) ∈ S))
        (decide ((⟨1, by omega⟩ : Fin (m + 4)) ∈ S))
        (middleColors S)
        (decide ((⟨m + 2, by omega⟩ : Fin (m + 4)) ∈ S))
        (decide ((⟨m + 3, by omega⟩ : Fin (m + 4)) ∈ S)) d k := by
  rw [physicalWeight_eq_listWeight, physicalSites_ofFn hm, listWeight_background]

@[simp] theorem middleColors_length {m : ℕ} (S : Finset (Fin (m + 4))) :
    (middleColors S).length = m := by simp [middleColors]

end UnifiedEJM.WeightedTransfer
