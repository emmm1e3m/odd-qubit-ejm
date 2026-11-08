import UnifiedEJM.PhysicsWeightedOrder
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Tactic

open OddEJM
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer.SparseCertificate

/-- 直接列出十个二元坐标的实际支撑；允许重数，因此不依赖GF(2)基独立性。 -/
abbrev Point := Logical × Memory
abbrev Support := Multiset Point

/-- 每个列表元素贡献同一个精确有理权重。 -/
def decode (support : Support) (weight : ℚ) (d : Logical) : Distribution :=
  fun t => (support.count (d, t) : ℚ) * weight

/-- 一个支撑元素的所有合法新位；零或一均直接按转移约束判断。 -/
def nextOne (a b : Site) (x : Point) : Support :=
  (if allowed b 0 ∧ constraint a x.1 x.2.2.1 0
    then {(x.1, push b.word x.2 0)} else 0) +
  (if allowed b 1 ∧ constraint a x.1 x.2.2.1 1
    then {(x.1, push b.word x.2 1)} else 0)

def nextSupport (a b : Site) (support : Support) : Support :=
  support.bind (nextOne a b)

@[simp] theorem decode_zero (w : ℚ) (d : Logical) (t : Memory) :
    decode 0 w d t = 0 := by simp [decode]

@[simp] theorem decode_add (s t : Support) (w : ℚ) (d : Logical) (x : Memory) :
    decode (s + t) w d x = decode s w d x + decode t w d x := by
  simp [decode, add_mul]

@[simp] theorem decode_ite (p : Prop) [Decidable p] (s t : Support)
    (w : ℚ) (d : Logical) (x : Memory) :
    decode (if p then s else t) w d x =
      if p then decode s w d x else decode t w d x := by
  split <;> rfl
@[simp] theorem decode_singleton (p : Point) (w : ℚ) (d : Logical) (x : Memory) :
    decode {p} w d x = if p = (d, x) then w else 0 := by
  simp [decode, Multiset.count_singleton, eq_comm]

@[simp] theorem decode_cons (x : Point) (xs : Support) (w : ℚ)
    (d : Logical) (t : Memory) :
    decode (x ::ₘ xs) w d t = decode {x} w d t + decode xs w d t := by
  have hs : x ::ₘ xs = ({x} : Support) + xs := by simp
  rw [hs]
  exact decode_add {x} xs w d t

@[simp] theorem nextSupport_zero (a b : Site) : nextSupport a b 0 = 0 := by
  simp [nextSupport]

@[simp] theorem nextSupport_add (a b : Site) (s t : Support) :
    nextSupport a b (s + t) = nextSupport a b s + nextSupport a b t := by
  simp [nextSupport]

@[simp] theorem nextSupport_singleton (a b : Site) (x : Point) :
    nextSupport a b {x} = nextOne a b x := by simp [nextSupport]

theorem decode_nonneg (support : Support) {weight : ℚ} (hw : 0 ≤ weight)
    (d : Logical) (t : Memory) : 0 ≤ decode support weight d t := by
  exact mul_nonneg (Nat.cast_nonneg _) hw

/-- 稀疏单点转移与完整有限核一致。 -/
theorem advance_singleton (a b : Site) (x : Point) (w : ℚ)
    (d : Logical) (t : Memory) :
    advance d a b (decode {x} w d) t =
      decode (nextOne a b x) (w * siteWeight b) d t := by
  classical
  rcases x with ⟨e, s⟩
  by_cases hed : e = d
  · subst e
    have hp := stepKernel_pairing d a b s (fun u => if u = t then (1 : ℚ) else 0)
    have huniv : (Finset.univ : Finset Bit) = {0, 1} := by decide +kernel
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hp
    rw [huniv] at hp
    norm_num only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.sum_singleton] at hp
    have hdecode : decode {(d, s)} w d = (fun x => if s = x then w else 0) := by
      funext x
      simp only [decode_singleton, Prod.mk.injEq, true_and]
    rw [hdecode]
    rw [show advance d a b (fun x => if s = x then w else 0) t =
      w * stepKernel d a b s t by
      simp [advance, eq_comm, ite_mul]]
    rw [hp]
    simp [nextOne, decode_add, decode_singleton, mul_add, mul_ite, ite_mul] <;> ring
  · have hleft : advance d a b (decode {(e, s)} w d) t = 0 := by
      simp [advance, decode_singleton, hed]
    rw [hleft]
    simp [nextOne, decode_add, decode_singleton, hed]

/-- 证书仅验证多重集相等；此定理将其提升到所有十比特点的精确有理转移。 -/
theorem advance_decode (a b : Site) (support : Support) (w : ℚ)
    (d : Logical) (t : Memory) :
    advance d a b (decode support w d) t =
      decode (nextSupport a b support) (w * siteWeight b) d t := by
  induction support using Multiset.induction_on with
  | empty => simp [advance]
  | @cons x xs ih =>
      have hs : x ::ₘ xs = ({x} : Support) + xs := by simp
      rw [hs, nextSupport_add, decode_add]
      calc
        _ = advance d a b (decode {x} w d) t +
            advance d a b (decode xs w d) t := by
          simp [advance, decode_add, add_mul, Finset.sum_add_distrib]
        _ = _ := by rw [advance_singleton, ih, nextSupport_singleton]

/-- 列表的实际长度就是总质量中的重数；没有使用基的维数。 -/
theorem decode_totalMass (support : Support) (w : ℚ) :
    (∑ d, mass (decode support w d)) = (support.card : ℚ) * w := by
  induction support using Multiset.induction_on with
  | empty => simp [mass]
  | @cons x xs ih =>
      have hs : x ::ₘ xs = ({x} : Support) + xs := by simp
      rw [hs]
      simp only [mass, decode_add, Finset.sum_add_distrib]
      rw [show (∑ d, ∑ t, decode {x} w d t) = w by
        rcases x with ⟨d, t⟩
        simp [decode_singleton, ite_and]]
      change w + (∑ d, mass (decode xs w d)) = _
      rw [ih]
      simp [add_mul] <;> ring

/-- 相同支撑重复f次可由单元素权重乘f吸收。 -/
theorem decode_nsmul (support : Support) (f : ℕ) (w : ℚ)
    (d : Logical) (t : Memory) :
    decode (f • support) w d t = decode support ((f : ℚ) * w) d t := by
  simp [decode, Multiset.count_nsmul]
  ring

/-- 这是有限生成器需要提供的唯一转移证书：实际合法前像的多重集相等。 -/
theorem checked_transition (a b : Site) (source target : Support) (f : ℕ)
    (h : nextSupport a b source = f • target) (w w' : ℚ)
    (hw : (f : ℚ) * (w * siteWeight b) = w') :
    ∀ d t, advance d a b (decode source w d) t = decode target w' d t := by
  intro d t
  rw [advance_decode, h, decode_nsmul, hw]

/-- 小质量支撑的安全性由实际元素总数直接证明。 -/
theorem checked_smallMass (support : Support) (w : ℚ)
    (h : (support.card : ℚ) * w ≤ 1 / 4) :
    (∑ d, mass (decode support w d)) ≤ 1 / 4 := by
  simpa only [decode_totalMass] using h

/-- 与178和225的数据相同的低位顺序：d,k,p,q。 -/
def bits4 (x : ℕ) : Logical :=
  ![(x : Bit), ((x / 2 : ℕ) : Bit), ((x / 4 : ℕ) : Bit), ((x / 8 : ℕ) : Bit)]

def point (x : ℕ) : Point :=
  (bits4 (x % 16), bits4 ((x / 16) % 16), ((x / 256 : ℕ) : Bit),
    ((x / 512 : ℕ) : Bit))

def fromList (xs : List ℕ) : Support := (xs.map point : List Point)

end UnifiedEJM.WeightedTransfer.SparseCertificate

