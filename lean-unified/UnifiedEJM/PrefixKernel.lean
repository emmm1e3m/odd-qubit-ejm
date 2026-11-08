import UnifiedEJM.PhysicsLaurent
import Mathlib.Tactic

open OddEJM
open UnifiedEJM.PhysicsFinite
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- 每个位置的两个独立比特，以及交换后的两个副本。 -/
def replica (side : Bool) (x y : Bit) : Bits 4 :=
  ![x, y, if side then y else x, if side then x else y]

def pair (j : Fin 4) : Bit × Bit := ((j.val / 2 : ℕ), (j.val % 2 : ℕ))

def rep (side : Bool) (j : Fin 4) : Bits 4 := replica side (pair j).1 (pair j).2

/-- 归约后的四位布尔核。 -/
def kernel (x b c s : Bit) : Bit :=
  if s = 0 then 1 + (1 + c) * (x + b) else b + x * c

/-- 局域路径图相位抽去后的单副本仿射振幅。 -/
def H (e : Bits 4) (p : Bit) (constant : Bool) (nu : Bit) (j : Fin 2) : G :=
  let x := e 0 + e 1 + e 2 + e 3
  let b := e 1 + p + if nu = 0 then e 2 else 0
  let c := p + if nu = 0 then 0 else e 2
  let f₀ := kernel x b c (e 0 + e 1)
  let f₁ := kernel x b c (e 0 + e 1 + 1)
  (if f₀.val = j.val then 1 else 0) +
    (if f₁.val = j.val then gi * gsign (e 3) else 0) +
    if constant then (if j = 0 then gi else -1) else 0

def quartet (h : Fin 4 → Fin 2 → G) : Fin 5 → G :=
  coefficientTerm
    ![h 0 0 * h 1 0, h 0 0 * h 1 1 + h 0 1 * h 1 0, h 0 1 * h 1 1]
    ![h 2 0 * h 3 0, h 2 0 * h 3 1 + h 2 1 * h 3 0, h 2 1 * h 3 1]

def catParity (lp : Bit) : Fin 4 → Bit := ![0, lp, 0, 1]

def catMatches (c : Fin 4) (b : Bit) : Bool :=
  (c = 0 && b = 0) || (c = 1 && b = 1)

/-- 类大小的常数、一次项；四类依次为全零、全一、混合偶、混合奇。 -/
def catCoeff (lp : Bit) (c : Fin 4) : Fin 2 → ℤ :=
  if c = 0 ∨ c = 1 then ![1, 0]
  else if c = 2 then ![-1 - (if lp = 0 then 1 else 0), 1]
  else ![-(if lp = 1 then 1 else 0), 1]

def catWeight (X : ℤ) (lp : Bit) (c : Fin 4) : ℤ :=
  catCoeff lp c 0 + X * catCoeff lp c 1

def pairWeight (lp : Bit) (c d : Fin 4) : Fin 3 → ℤ :=
  ![catCoeff lp c 0 * catCoeff lp d 0,
    catCoeff lp c 0 * catCoeff lp d 1 + catCoeff lp c 1 * catCoeff lp d 0,
    catCoeff lp c 1 * catCoeff lp d 1]

def catRep (side : Bool) (c d : Fin 4) : Fin 4 → Fin 4 :=
  ![c, d, if side then d else c, if side then c else d]

def p12H (nu : Bit) (suffix : Bool)
    (first second third penult last cy cv : Fin 4) : Fin 4 → Fin 2 → G :=
  let rf := rep true first
  let rs := rep true second
  let rt := rep suffix third
  let rp := rep false penult
  let rl := rep false last
  let par := replica suffix (catParity (1 + nu) cy) (catParity (1 + nu) cv)
  let cr := catRep suffix cy cv
  fun r => H ![rf r, rs r, rp r, rl r] (rt r + par r)
    (decide (rs r = rf r ∧ rt r = rf r ∧ rp r = rf r ∧ rl r = rf r) &&
      catMatches (cr r) (rf r)) nu

def p12Term (nu : Bit) (suffix : Bool)
    (first second third penult last cy cv : Fin 4) : Fin 5 → G :=
  let sg := if suffix then
      gsign ((pair third).1 + (pair third).2) ^ (if (pair penult).1 = (pair penult).2 then 0 else 1)
    else gsign ((pair second).1 + (pair second).2) ^ (if (pair third).1 = (pair third).2 then 0 else 1)
  fun k => sg * quartet (p12H nu suffix first second third penult last cy cv) k

def p12Coeff (nu : Bit) (suffix : Bool) (power : Fin 3) (k : Fin 5) : G :=
  ∑ f : Fin 4, ∑ s : Fin 4, ∑ t : Fin 4, ∑ p : Fin 4, ∑ l : Fin 4,
    ∑ c : Fin 4, ∑ d : Fin 4,
      (pairWeight (1 + nu) c d power : G) * p12Term nu suffix f s t p l c d k

/-- 空自由组只有一个类别，且不额外破坏常量串条件。 -/
def runParity (lp : Option Bit) (c : Fin 4) : Bit :=
  match lp with
  | none => 0
  | some p => catParity p c

def runMatches (lp : Option Bit) (c : Fin 4) (b : Bit) : Bool :=
  match lp with
  | none => true
  | some _ => catMatches c b

def runCoeff (lp : Option Bit) (c : Fin 4) : Fin 2 → ℤ :=
  match lp with
  | none => if c = 0 then ![1, 0] else ![0, 0]
  | some p => catCoeff p c

def runWeight (X : ℤ) (lp : Option Bit) (c : Fin 4) : ℤ :=
  runCoeff lp c 0 + X * runCoeff lp c 1

def runPairWeight (lp : Option Bit) (c d : Fin 4) : Fin 3 → ℤ :=
  ![runCoeff lp c 0 * runCoeff lp d 0,
    runCoeff lp c 0 * runCoeff lp d 1 + runCoeff lp c 1 * runCoeff lp d 0,
    runCoeff lp c 1 * runCoeff lp d 1]

/-- 任意长前缀的固定六个位对和四个自由串类别对应的四副本核。
`none` 精确表示长度为零的自由组；`some lp` 表示正长度组。 -/
def longH (la lb : Option Bit)
    (first second left right penult last ca da cb db : Fin 4) : Fin 4 → Fin 2 → G :=
  let rf := rep true first
  let rs := rep true second
  let ra := rep true left
  let rb := rep false right
  let rp := rep false penult
  let rl := rep false last
  let pa := replica true (runParity la ca) (runParity la da)
  let pb := replica false (runParity lb cb) (runParity lb db)
  let ac := catRep true ca da
  let bc := catRep false cb db
  fun r => H ![rf r, rs r, rp r, rl r]
    (ra r + rb r + pa r + pb r)
    (decide (rs r = rf r ∧ ra r = rf r ∧ rb r = rf r ∧
      rp r = rf r ∧ rl r = rf r) &&
      runMatches la (ac r) (rf r) && runMatches lb (bc r) (rf r))
    (la.getD 0 + lb.getD 0)

def longTerm (la lb : Option Bit)
    (first second left right penult last ca da cb db : Fin 4) : Fin 5 → G :=
  let sg := gsign ((pair left).1 + (pair left).2) ^
    (if (pair right).1 = (pair right).2 then 0 else 1)
  fun k => sg * quartet (longH la lb first second left right penult last ca da cb db) k

def longCoeff (la lb : Option Bit) (i j : Fin 3) (k : Fin 5) : G :=
  ∑ f : Fin 4, ∑ s : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
    ∑ p : Fin 4, ∑ l : Fin 4, ∑ ca : Fin 4, ∑ da : Fin 4,
      ∑ cb : Fin 4, ∑ db : Fin 4,
        ((runPairWeight la ca da i * runPairWeight lb cb db j : ℤ) : G) *
          longTerm la lb f s a b p l ca da cb db k

/-- 这里的参数为任意整数；长度只在上游计数桥中代入。 -/
def longSum (la lb : Option Bit) (X Y : ℤ) (k : Fin 5) : G :=
  ∑ f : Fin 4, ∑ s : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
    ∑ p : Fin 4, ∑ l : Fin 4, ∑ ca : Fin 4, ∑ da : Fin 4,
      ∑ cb : Fin 4, ∑ db : Fin 4,
        ((runWeight X la ca * runWeight X la da *
          runWeight Y lb cb * runWeight Y lb db : ℤ) : G) *
          longTerm la lb f s a b p l ca da cb db k

def p12Sum (nu : Bit) (suffix : Bool) (K : ℤ) (k : Fin 5) : G :=
  ∑ f : Fin 4, ∑ s : Fin 4, ∑ t : Fin 4, ∑ p : Fin 4, ∑ l : Fin 4,
    ∑ c : Fin 4, ∑ d : Fin 4,
      ((catWeight K (1 + nu) c * catWeight K (1 + nu) d : ℤ) : G) *
        p12Term nu suffix f s t p l c d k

theorem pairWeight_eval (X : ℤ) (lp : Bit) (c d : Fin 4) :
    catWeight X lp c * catWeight X lp d =
      pairWeight lp c d 0 + X * pairWeight lp c d 1 + X^2 * pairWeight lp c d 2 := by
  simp [catWeight, pairWeight]
  ring

theorem runPairWeight_eval (X : ℤ) (lp : Option Bit) (c d : Fin 4) :
    runWeight X lp c * runWeight X lp d =
      runPairWeight lp c d 0 + X * runPairWeight lp c d 1 +
        X^2 * runPairWeight lp c d 2 := by
  simp [runWeight, runPairWeight]
  ring

end UnifiedEJM.PrefixKernel
