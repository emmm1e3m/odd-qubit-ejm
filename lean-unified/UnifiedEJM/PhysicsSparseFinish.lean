import UnifiedEJM.PhysicsSparseCertificate

open OddEJM
open scoped BigOperators

namespace UnifiedEJM.WeightedTransfer.SparseCertificate

/-- 右端点约束后仅保留(d,k)，以p=q=0的同一十比特空间表示。 -/
def finishOne (a : Site) (x : Point) : Support :=
  if constraint a x.1 x.2.2.1 0 then {(x.1, (x.2.1, 0, 0))} else 0

def finishSupport (a : Site) (support : Support) : Support :=
  support.bind (finishOne a)

@[simp] theorem finishSupport_zero (a : Site) : finishSupport a 0 = 0 := by
  simp [finishSupport]

@[simp] theorem finishSupport_add (a : Site) (s t : Support) :
    finishSupport a (s + t) = finishSupport a s + finishSupport a t := by
  simp [finishSupport]

@[simp] theorem finishSupport_singleton (a : Site) (x : Point) :
    finishSupport a {x} = finishOne a x := by simp [finishSupport]

theorem finish_singleton (a : Site) (x : Point) (w : ℚ)
    (d k : Logical) :
    finish d a (decode {x} w d) k =
      decode (finishOne a x) w d (k, 0, 0) := by
  classical
  rcases x with ⟨e, l, p, q⟩
  by_cases he : e = d
  · subst e
    by_cases hl : l = k
    · subst l
      simp [finish, finishOne, decode_singleton, Prod.mk.injEq, eq_comm, ite_and]
      symm
      rw [Finset.sum_eq_single p]
      · simp
      · intro r hr hne
        simp [Ne.symm hne]
      · simp
    · simp [finish, finishOne, decode_singleton, Prod.mk.injEq, hl, ite_and]
  · simp [finish, finishOne, decode_singleton, Prod.mk.injEq, he, ite_and]

/-- 真实终端的四个记忆位前像全部由多重集保留，允许纤维重数。 -/
theorem finish_decode (a : Site) (support : Support) (w : ℚ)
    (d k : Logical) :
    finish d a (decode support w d) k =
      decode (finishSupport a support) w d (k, 0, 0) := by
  induction support using Multiset.induction_on with
  | empty => simp [finish]
  | @cons x xs ih =>
      have hs : x ::ₘ xs = ({x} : Support) + xs := by simp
      rw [hs, finishSupport_add, decode_add]
      calc
        _ = finish d a (decode {x} w d) k + finish d a (decode xs w d) k := by
          simp only [finish, decode_add, decode_cons]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro q hq
          split_ifs <;> simp
        _ = _ := by rw [finish_singleton, ih, finishSupport_singleton]

theorem checked_finish (a : Site) (source target : Support) (f : ℕ)
    (h : finishSupport a source = f • target) (w w' : ℚ)
    (hw : (f : ℚ) * w = w') :
    ∀ d k, finish d a (decode source w d) k = decode target w' d (k, 0, 0) := by
  intro d k
  rw [finish_decode, h, decode_nsmul, hw]

end UnifiedEJM.WeightedTransfer.SparseCertificate

