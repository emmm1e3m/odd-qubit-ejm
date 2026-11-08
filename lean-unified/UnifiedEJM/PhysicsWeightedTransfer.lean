import UnifiedEJM.Core
import Mathlib.Tactic

open OddEJM
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer

/-- 四个逻辑坐标与两个未消去的路径位，共十个二元坐标。 -/
abbrev Logical := Bits 4
abbrev Memory := Logical × Bit × Bit
abbrev Distribution := Memory → ℚ

structure Site where
  inA : Bool
  word : Logical
  deriving DecidableEq

def dot (w d : Logical) : Bit := ∑ i, w i * d i
def charge (w : Logical) (r : Bit) : Logical := fun i => w i * r
def allowed (a : Site) (r : Bit) : Prop := a.inA = true ∨ r = 0
def constraint (a : Site) (d : Logical) (p r : Bit) : Prop :=
  a.inA = true ∨ p + r = dot a.word d

instance (a : Site) (r : Bit) : Decidable (allowed a r) := inferInstanceAs
  (Decidable (a.inA = true ∨ r = 0))
instance (a : Site) (d : Logical) (p r : Bit) : Decidable (constraint a d p r) :=
  inferInstanceAs (Decidable (a.inA = true ∨ p + r = dot a.word d))

/-- 每个A位按均匀比特求平均；B位强制为零。 -/
def siteWeight (a : Site) : ℚ := if a.inA then 1 / 2 else 1

def push (w : Logical) (s : Memory) (r : Bit) : Memory :=
  (s.1 + charge w r, s.2.2, r)

/-- 处理旧位的约束以后，累加新位的逻辑荷并删除旧的左邻位。 -/
def stepKernel (d : Logical) (a b : Site) (s t : Memory) : ℚ :=
  if t.1 = s.1 + charge b.word t.2.2 then
    if t.2.1 = s.2.2 then
      if allowed b t.2.2 ∧ constraint a d s.2.1 t.2.2 then siteWeight b else 0
    else 0
  else 0

def advance (d : Logical) (a b : Site) (μ : Distribution) : Distribution :=
  fun t => ∑ s, μ s * stepKernel d a b s t

/-- 左端点取v₀=0，逻辑荷从W₁v₁开始。d作为四个外部逻辑参数保留。 -/
def initial (a : Site) : Distribution := fun s =>
  if s.2.1 = 0 ∧ s.1 = charge a.word s.2.2 ∧ allowed a s.2.2
  then siteWeight a else 0

/-- 右端点取vₙ₊₁=0，再对尚存的两个路径位求和。 -/
def finish (d : Logical) (a : Site) (μ : Distribution) (k : Logical) : ℚ :=
  ∑ p : Bit, ∑ q : Bit,
    if constraint a d p 0 then μ (k, p, q) else 0

@[simp] theorem stepKernel_push (d : Logical) (a b : Site) (s : Memory) (r : Bit) :
    stepKernel d a b s (push b.word s r) =
      if allowed b r ∧ constraint a d s.2.1 r then siteWeight b else 0 := by
  by_cases h : allowed b r ∧ constraint a d s.2.1 r <;>
    simp [stepKernel, push, h]

/-- 两个前像公式；有限证书只需检查两个旧左邻位，无需信任二元消元程序。 -/
theorem advance_two (d : Logical) (a b : Site) (μ : Distribution) (t : Memory) :
    advance d a b μ t =
      ∑ p : Bit,
        μ (t.1 - charge b.word t.2.2, p, t.2.1) *
          (if allowed b t.2.2 ∧ constraint a d p t.2.2 then siteWeight b else 0) := by
  classical
  unfold advance
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single (t.1 - charge b.word t.2.2)]
  · rw [Finset.sum_eq_single t.2.1]
    · simp [stepKernel]
    · intro q hq hne
      simp [stepKernel, Ne.symm hne]
    · simp
  · intro k hk hne
    have hbad : t.1 ≠ k + charge b.word t.2.2 := by
      intro heq
      exact hne (eq_sub_iff_add_eq.mpr heq.symm)
    simp [stepKernel, hbad]
  · simp

/-- 一个输入状态的所有输出恰为新位r的两个取值。 -/
theorem stepKernel_pairing (d : Logical) (a b : Site) (s : Memory) (f : Memory → ℚ) :
    (∑ t, stepKernel d a b s t * f t) =
      ∑ r : Bit, if allowed b r ∧ constraint a d s.2.1 r
        then siteWeight b * f (push b.word s r) else 0 := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_eq_single s.2.2]
  · rw [Finset.sum_eq_single (s.1 + charge b.word r)]
    · by_cases h : allowed b r ∧ constraint a d s.2.1 r <;>
        simp [stepKernel, push, h]
    · intro k hk hne
      simp [stepKernel, hne]
    · simp
  · intro p hp hne
    simp [stepKernel, hne]
  · simp

theorem advance_pairing (d : Logical) (a b : Site) (μ : Distribution) (f : Memory → ℚ) :
    (∑ t, advance d a b μ t * f t) =
      ∑ s, μ s * (∑ r : Bit, if allowed b r ∧ constraint a d s.2.1 r
        then siteWeight b * f (push b.word s r) else 0) := by
  classical
  simp only [advance, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, stepKernel_pairing]

/-- 初始分布正是第一个物理A位的平均，B位只能取零。 -/
theorem initial_pairing (a : Site) (f : Memory → ℚ) :
    (∑ s, initial a s * f s) =
      ∑ r : Bit, if allowed a r
        then siteWeight a * f (charge a.word r, 0, r) else 0 := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single (charge a.word r)]
    · by_cases h : allowed a r <;> simp [initial, h]
    · intro k hk hne
      simp [initial, hne]
    · simp
  · intro p hp hne
    simp [initial, hne]
  · simp

/-- 任意长度路径的动态规划；每一步先完成前一站约束。 -/
def evolve (d : Logical) : Site → List Site → Distribution → Distribution
  | _, [], μ => μ
  | a, b :: bs, μ => evolve d b bs (advance d a b μ)

def finalSite : Site → List Site → Site
  | a, [] => a
  | _, b :: bs => finalSite b bs

/-- 前缀到达安全状态后，可将剩余任意长后缀单独交给质量收缩界。 -/
theorem evolve_append (d : Logical) (xs ys : List Site) (a : Site) (μ : Distribution) :
    evolve d a (xs ++ ys) μ =
      evolve d (finalSite a xs) ys (evolve d a xs μ) := by
  induction xs generalizing a μ with
  | nil => rfl
  | cons b xs ih =>
      exact ih b (advance d a b μ)

/-- 独立的逐比特求和语义：显式选择每一个新位，不进行线性消元。 -/
def pathSum (d : Logical) : Site → List Site → (Memory → ℚ) → Memory → ℚ
  | _, [], f, s => f s
  | a, b :: bs, f, s =>
      ∑ r : Bit, if allowed b r ∧ constraint a d s.2.1 r
        then siteWeight b * pathSum d b bs f (push b.word s r) else 0

/-- 无限长度量词由列表归纳承担，绝非见证长度的截断。 -/
theorem evolve_pairing (d : Logical) (bs : List Site) (a : Site)
    (μ : Distribution) (f : Memory → ℚ) :
    (∑ t, evolve d a bs μ t * f t) = ∑ s, μ s * pathSum d a bs f s := by
  induction bs generalizing a μ with
  | nil => rfl
  | cons b bs ih =>
      change (∑ t, evolve d b bs (advance d a b μ) t * f t) = _
      rw [ih, advance_pairing]
      rfl

def terminal (d : Logical) (a : Site) (k : Logical) (s : Memory) : ℚ :=
  if s.1 = k ∧ constraint a d s.2.1 0 then 1 else 0

theorem finish_pairing (d : Logical) (a : Site) (μ : Distribution) (k : Logical) :
    finish d a μ k = ∑ s, μ s * terminal d a k s := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · simp [finish, terminal, mul_ite]
  · intro l hl hne
    simp [terminal, hne]
  · simp

/-- 行向量采用178.3的低位顺序：4,1,8,…,8,2,4。 -/
def firstWord : Logical := ![0, 0, 1, 0]
def secondWord : Logical := ![1, 0, 0, 0]
def middleWord : Logical := ![0, 0, 0, 1]
def penultimateWord : Logical := ![0, 1, 0, 0]

def middleSites (colors : List Bool) : List Site := colors.map (fun a => ⟨a, middleWord⟩)

def backgroundTail (second : Bool) (middle : List Bool) (penultimate last : Bool) :
    List Site :=
  [⟨second, secondWord⟩] ++ middleSites middle ++
    [⟨penultimate, penultimateWord⟩, ⟨last, firstWord⟩]

def backgroundWeight (first second : Bool) (middle : List Bool) (penultimate last : Bool)
    (d k : Logical) : ℚ :=
  finish d ⟨last, firstWord⟩
    (evolve d ⟨first, firstWord⟩ (backgroundTail second middle penultimate last)
      (initial ⟨first, firstWord⟩)) k

/-- 所有中央长度的精确签名权重，右端点与每个B位约束均被保留。 -/
theorem backgroundWeight_eq_pathSum
    (first second : Bool) (middle : List Bool) (penultimate last : Bool) (d k : Logical) :
    backgroundWeight first second middle penultimate last d k =
      ∑ s, initial ⟨first, firstWord⟩ s *
        pathSum d ⟨first, firstWord⟩ (backgroundTail second middle penultimate last)
          (terminal d ⟨last, firstWord⟩ k) s := by
  unfold backgroundWeight
  rw [finish_pairing, evolve_pairing]

theorem backgroundWeight_eq_assignments
    (first second : Bool) (middle : List Bool) (penultimate last : Bool) (d k : Logical) :
    backgroundWeight first second middle penultimate last d k =
      ∑ r : Bit, if allowed (⟨first, firstWord⟩ : Site) r then
        siteWeight ⟨first, firstWord⟩ *
          pathSum d ⟨first, firstWord⟩ (backgroundTail second middle penultimate last)
            (terminal d ⟨last, firstWord⟩ k) (charge firstWord r, 0, r)
        else 0 := by
  rw [backgroundWeight_eq_pathSum, initial_pairing]

end UnifiedEJM.WeightedTransfer
