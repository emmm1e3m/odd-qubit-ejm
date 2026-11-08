import UnifiedEJM.PrefixLongCrossBlocks

open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

/-- 使用具体数据积保存全部系数，使同一项的H和二次乘积可供各输出共用。 -/
abbrev Data3 (A : Type*) := A × A × A
abbrev Data5 := G × G × G × G × G
abbrev Data15 := Data3 Data5
abbrev Data45 := Data3 Data15

def pick3Hom {A : Type*} [AddCommMonoid A] (i : Fin 3) : Data3 A →+ A where
  toFun q := ![q.1, q.2.1, q.2.2] i
  map_zero' := by fin_cases i <;> rfl
  map_add' _ _ := by fin_cases i <;> rfl

def pick5Hom (k : Fin 5) : Data5 →+ G where
  toFun q := ![q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2] k
  map_zero' := by fin_cases k <;> rfl
  map_add' _ _ := by fin_cases k <;> rfl

def coefficient15Hom (i : Fin 3) (k : Fin 5) : Data15 →+ G :=
  (pick5Hom k).comp (pick3Hom i)

def coefficient45Hom (i j : Fin 3) (k : Fin 5) : Data45 →+ G :=
  (coefficient15Hom j k).comp (pick3Hom i)

def coefficient15 (q : Data15) (i : Fin 3) (k : Fin 5) : G :=
  coefficient15Hom i k q

def coefficient45 (q : Data45) (i j : Fin 3) (k : Fin 5) : G :=
  coefficient45Hom i j k q

theorem coefficient15_sum {ι : Type*} [Fintype ι] (q : ι → Data15)
    (i : Fin 3) (k : Fin 5) :
    coefficient15 (∑ x, q x) i k = ∑ x, coefficient15 (q x) i k :=
  map_sum (coefficient15Hom i k) q Finset.univ

theorem coefficient45_sum {ι : Type*} [Fintype ι] (q : ι → Data45)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (∑ x, q x) i j k = ∑ x, coefficient45 (q x) i j k :=
  map_sum (coefficient45Hom i j k) q Finset.univ

def scale5 (w : G) (q : Data5) : Data5 :=
  (w*q.1, w*q.2.1, w*q.2.2.1, w*q.2.2.2.1, w*q.2.2.2.2)

theorem pick5_scale5 (w : G) (q : Data5) (k : Fin 5) :
    pick5Hom k (scale5 w q) = w * pick5Hom k q := by
  fin_cases k <;> rfl

/-- 六个二次乘积只在数据构造中定义一次。 -/
def quartetData (h : Fin 4 → Fin 2 → G) : Data5 :=
  let a₀ := h 0 0 * h 1 0
  let a₁ := h 0 0 * h 1 1 + h 0 1 * h 1 0
  let a₂ := h 0 1 * h 1 1
  let b₀ := star (h 2 0 * h 3 0)
  let b₁ := star (h 2 0 * h 3 1 + h 2 1 * h 3 0)
  let b₂ := star (h 2 1 * h 3 1)
  (a₀*b₂, a₀*b₁+a₁*b₂, a₀*b₀+a₁*b₁+a₂*b₂, a₁*b₀+a₂*b₁, a₂*b₀)

theorem quartetData_spec (h : Fin 4 → Fin 2 → G) (k : Fin 5) :
    pick5Hom k (quartetData h) = quartet h k := by
  fin_cases k <;> rfl

def weighted15 (w : Fin 3 → ℤ) (q : Data5) : Data15 :=
  (if w 0 = 0 then 0 else scale5 (w 0 : G) q,
   if w 1 = 0 then 0 else scale5 (w 1 : G) q,
   if w 2 = 0 then 0 else scale5 (w 2 : G) q)

theorem weighted15_spec (w : Fin 3 → ℤ) (q : Data5) (i : Fin 3) (k : Fin 5) :
    coefficient15 (weighted15 w q) i k =
      if w i = 0 then 0 else (w i : G) * pick5Hom k q := by
  have hw (a : ℤ) :
      pick5Hom k (if a = 0 then 0 else scale5 (a : G) q) =
        if a = 0 then 0 else (a : G) * pick5Hom k q := by
    by_cases h : a = 0
    · simp only [h, ite_true, map_zero]
    · simp only [h, ite_false, pick5_scale5]
  fin_cases i
  · exact hw (w 0)
  · exact hw (w 1)
  · exact hw (w 2)

def weighted45 (wA wB : Fin 3 → ℤ) (q : Data5) : Data45 :=
  (weighted15 (fun j => wA 0 * wB j) q,
   weighted15 (fun j => wA 1 * wB j) q,
   weighted15 (fun j => wA 2 * wB j) q)

theorem weighted45_spec (wA wB : Fin 3 → ℤ) (q : Data5)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (weighted45 wA wB q) i j k =
      if wA i * wB j = 0 then 0 else ((wA i * wB j : ℤ) : G) * pick5Hom k q := by
  fin_cases i
  · exact weighted15_spec (fun h => wA 0 * wB h) q j k
  · exact weighted15_spec (fun h => wA 1 * wB h) q j k
  · exact weighted15_spec (fun h => wA 2 * wB h) q j k

def p12TermData (nu : Bit) (suffix : Bool)
    (f s t p l c d : Fin 4) : Data5 :=
  let sg := if suffix then
      gsign ((pair t).1 + (pair t).2) ^ (if (pair p).1 = (pair p).2 then 0 else 1)
    else gsign ((pair s).1 + (pair s).2) ^ (if (pair t).1 = (pair t).2 then 0 else 1)
  scale5 sg (quartetData (p12H nu suffix f s t p l c d))

theorem p12TermData_spec (nu : Bit) (suffix : Bool)
    (f s t p l c d : Fin 4) (k : Fin 5) :
    pick5Hom k (p12TermData nu suffix f s t p l c d) =
      p12Term nu suffix f s t p l c d k := by
  simp only [p12TermData, p12Term, pick5_scale5, quartetData_spec]

def p12BlockData (nu : Bit) (suffix : Bool) (f s : Fin 4) : Data15 :=
  ∑ t : Fin 4, ∑ p : Fin 4, ∑ l : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
    weighted15 (pairWeight (1+nu) c d) (p12TermData nu suffix f s t p l c d)

/-- 每个数据投影严格等于原始有限和；原证书接口可直接复用。 -/
theorem p12BlockData_spec (nu : Bit) (suffix : Bool) (f s : Fin 4)
    (i : Fin 3) (k : Fin 5) :
    coefficient15 (p12BlockData nu suffix f s) i k = p12Block nu suffix f s i k := by
  simp only [p12BlockData, p12Block, coefficient15_sum, weighted15_spec, p12TermData_spec]

def longTermData (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) : Data5 :=
  let sg := gsign ((pair a).1 + (pair a).2) ^
    (if (pair b).1 = (pair b).2 then 0 else 1)
  scale5 sg (quartetData (longH la lb f s a b p l ca da cb db))

theorem longTermData_spec (la lb : Option Bit)
    (f s a b p l ca da cb db : Fin 4) (k : Fin 5) :
    pick5Hom k (longTermData la lb f s a b p l ca da cb db) =
      longTerm la lb f s a b p l ca da cb db k := by
  simp only [longTermData, longTerm, pick5_scale5, quartetData_spec]

def longCrossBlockData (la lb : Option Bit) (f s a b : Fin 4) : Data45 :=
  ∑ p : Fin 4, ∑ l : Fin 4, ∑ ca : Fin 4, ∑ da : Fin 4,
    ∑ cb : Fin 4, ∑ db : Fin 4,
      weighted45 (runPairWeight la ca da) (runPairWeight lb cb db)
        (longTermData la lb f s a b p l ca da cb db)

theorem longCrossBlockData_spec (la lb : Option Bit) (f s a b : Fin 4)
    (i j : Fin 3) (k : Fin 5) :
    coefficient45 (longCrossBlockData la lb f s a b) i j k =
      longCrossBlock la lb f s a b i j k := by
  simp only [longCrossBlockData, longCrossBlock, coefficient45_sum,
    weighted45_spec, longTermData_spec]

end UnifiedEJM.PrefixKernel
