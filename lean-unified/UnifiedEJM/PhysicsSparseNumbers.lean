import UnifiedEJM.PhysicsSparseFinish
import UnifiedEJM.PhysicsSparseEncoding

open OddEJM

namespace UnifiedEJM.WeightedTransfer.SparseCertificate

/-- 十个实际二元坐标的整数编码；这里只使用已经核验的四位逆编码。 -/
def pointNumber (x : Point) : ℕ :=
  index4 x.1 + 16 * index4 x.2.1 + 256 * x.2.2.1.val + 512 * x.2.2.2.val

theorem point_pointNumber (x : Point) : point (pointNumber x) = x := by
  rcases x with ⟨d, k, p, q⟩
  have hd := index4_lt d
  have hk := index4_lt k
  have hp := ZMod.val_lt p
  have hq := ZMod.val_lt q
  have h0 : (index4 d + 16 * index4 k + 256 * p.val + 512 * q.val) % 16 =
      index4 d := by omega
  have h1 : ((index4 d + 16 * index4 k + 256 * p.val + 512 * q.val) / 16) % 16 =
      index4 k := by omega
  have h2 : (index4 d + 16 * index4 k + 256 * p.val + 512 * q.val) / 256 =
      p.val + 2 * q.val := by omega
  have h3 : (index4 d + 16 * index4 k + 256 * p.val + 512 * q.val) / 512 =
      q.val := by omega
  simp only [pointNumber, point, h0, h1, h2, h3, bits4_index,
    Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  have htwo : (2 : Bit) = 0 := by decide +kernel
  norm_num [htwo]
  exact Or.inl htwo

/-- 数字后继仍按原始物理约束计算；只把结果编码，未另设转移表。 -/
def nextNumbersOne (a b : Site) (n : ℕ) : List ℕ :=
  let x := point n
  (if allowed b 0 ∧ constraint a x.1 x.2.2.1 0
    then [pointNumber (x.1, push b.word x.2 0)] else []) ++
  (if allowed b 1 ∧ constraint a x.1 x.2.2.1 1
    then [pointNumber (x.1, push b.word x.2 1)] else [])

def nextNumbers (a b : Site) (ns : List ℕ) : List ℕ :=
  ns.flatMap (nextNumbersOne a b)

theorem nextOne_numbers (a b : Site) (n : ℕ) :
    nextOne a b (point n) = fromList (nextNumbersOne a b n) := by
  simp only [nextOne, nextNumbersOne]
  split_ifs <;> simp [fromList, point_pointNumber] <;> rfl

theorem fromList_append (xs ys : List ℕ) :
    fromList (xs ++ ys) = fromList xs + fromList ys := by
  simp [fromList]

theorem nextSupport_fromList (a b : Site) (ns : List ℕ) :
    nextSupport a b (fromList ns) = fromList (nextNumbers a b ns) := by
  induction ns with
  | nil => simp [fromList, nextNumbers]
  | cons n ns ih =>
      change nextSupport a b ({point n} + fromList ns) =
        fromList (nextNumbersOne a b n ++ nextNumbers a b ns)
      rw [nextSupport_add, nextSupport_singleton, nextOne_numbers,
        fromList_append, ih]

def finishNumbersOne (a : Site) (n : ℕ) : List ℕ :=
  let x := point n
  if constraint a x.1 x.2.2.1 0 then [pointNumber (x.1, x.2.1, 0, 0)] else []

def finishNumbers (a : Site) (ns : List ℕ) : List ℕ :=
  ns.flatMap (finishNumbersOne a)

theorem finishOne_numbers (a : Site) (n : ℕ) :
    finishOne a (point n) = fromList (finishNumbersOne a n) := by
  simp only [finishOne, finishNumbersOne]
  split_ifs <;> simp [fromList, point_pointNumber]

theorem finishSupport_fromList (a : Site) (ns : List ℕ) :
    finishSupport a (fromList ns) = fromList (finishNumbers a ns) := by
  induction ns with
  | nil => simp [fromList, finishNumbers]
  | cons n ns ih =>
      change finishSupport a ({point n} + fromList ns) =
        fromList (finishNumbersOne a n ++ finishNumbers a ns)
      rw [finishSupport_add, finishSupport_singleton, finishOne_numbers,
        fromList_append, ih]

end UnifiedEJM.WeightedTransfer.SparseCertificate
