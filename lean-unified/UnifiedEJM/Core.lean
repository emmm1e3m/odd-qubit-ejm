import OddEJM.Compress
import OddEJM.OriginalPhase

namespace UnifiedEJM
open OddEJM
open scoped BigOperators
open Complex

/-- 新版固定四特征三次核；四坐标顺序为 x,b,c,s。 -/
def F (v : Bits 4) : Bit :=
  1 + v 0 + v 1 + v 3 + v 0 * v 3 + v 0 * v 2 + v 1 * v 2 + v 1 * v 2 * v 3

/-- 五特征到四特征的精确线性压缩。 -/
def project4 (v : Bits 5) : Bits 4 := ![v 0 + v 3, v 1, v 2, v 0 + v 4]

def Q20 (v : Bits 5) : Bit := F (project4 v)

def features {n : ℕ} (z : Bits n) : Bits 4 := project4 (compress z)

def q {n : ℕ} (z : Bits n) : Bit := Q20 (compress z)

def phaseSupport {n : ℕ} (z : Bits n) : Bit := if z = 0 then 0 else q z

def background {n : ℕ} (u : ℂ) (z : Bits n) : ℂ := I ^ weight z * u ^ (q z).val

def corrected {n : ℕ} (u : ℂ) (z : Bits n) : ℂ := background u z + (I - u) * deltaZero z

def rawPhase {n : ℕ} (u : ℂ) (z : Bits n) : ℂ :=
  if z = 0 then 1 else -I * I ^ weight z * u ^ (q z).val

noncomputable def seed (n : ℕ) (t : ℝ) : Vec n :=
  circuit (fun z => normFactor n * rawPhase (anglePhase t) z)

noncomputable def measurement (n : ℕ) (t : ℝ) (label : Bits n) : Vec n :=
  circuit (fun z => normFactor n * rawPhase (anglePhase t) z * character label z)

theorem q_eq_features {n : ℕ} (z : Bits n) : q z = F (features z) := rfl

@[simp] theorem Q20_zero : Q20 0 = 1 := by decide

@[simp] theorem q_zero (n : ℕ) : q (0 : Bits n) = 1 := by
  simp only [q, compress_zero, Q20_zero]

/-- 分段核与三次多项式逐输入一致。 -/
theorem F_branch : ∀ v : Bits 4,
    F v = if v 3 = 0 then 1 + (1 + v 2) * (v 0 + v 1) else v 1 + v 0 * v 2 := by decide

end UnifiedEJM
