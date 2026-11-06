import UnifiedEJM.UnitaryPhase
import UnifiedEJM.DiagonalDifference

noncomputable section
open scoped BigOperators Matrix
open OddEJM

namespace UnifiedEJM.CliffordFoundation

def root4 (a : ZMod 4) : ℂ := Complex.I ^ a.val

theorem root4_mem_unitary (a : ZMod 4) : root4 a ∈ unitary ℂ := by
  have hI : Complex.I ∈ unitary ℂ := by
    constructor <;> simp
  exact (unitary ℂ).pow_mem hI a.val

theorem root4_injective : Function.Injective root4 := by
  intro a b h
  fin_cases a <;> fin_cases b
  all_goals first | rfl | norm_num [root4, ZMod.val,
      Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
      Complex.ext_iff] at h

theorem root4_add (a b : ZMod 4) : root4 (a+b) = root4 a * root4 b := by
  unfold root4
  rw [ZMod.val_add, ← pow_eq_pow_mod (a.val+b.val) Complex.I_pow_four, pow_add]

theorem root4_neg (a : ZMod 4) : root4 (-a) = (root4 a)⁻¹ := by
  have h : root4 (-a) * root4 a = 1 := by rw [← root4_add]; simp [root4]
  exact eq_inv_of_mul_eq_one_left h

theorem root4_sub (a b : ZMod 4) : root4 (a-b) = root4 a * (root4 b)⁻¹ := by
  rw [sub_eq_add_neg, root4_add, root4_neg]

def phase4 {n : ℕ} (f : DiagonalDifference.Phase4 n) : Phase n :=
  fun z => ⟨root4 (f z), root4_mem_unitary (f z)⟩

def diagonal4 {n : ℕ} (f : DiagonalDifference.Phase4 n) : Gate n :=
  diagonalGate (phase4 f)

theorem phase4_difference {n : ℕ} (a : Bits n) (f : DiagonalDifference.Phase4 n) :
    phaseDifference a (phase4 f) = phase4 (DiagonalDifference.diff a f) := by
  ext z
  simp only [phaseDifference, phase4, Submonoid.coe_mul, Unitary.coe_inv,
    DiagonalDifference.diff, root4_sub]

theorem phaseDepth_phase4_iff {n : ℕ} (k : ℕ) (f : DiagonalDifference.Phase4 n) :
    PhaseDepth k (phase4 f) ↔ DiagonalDifference.Depth k f := by
  induction k generalizing f with
  | zero =>
      constructor
      · intro h x y
        apply root4_injective
        exact congrArg (fun z : unitary ℂ => (z : ℂ)) (h x y)
      · intro h x y
        apply Subtype.ext
        change root4 (f x) = root4 (f y)
        rw [h x y]
  | succ k ih =>
      change (∀ a, PhaseDepth k (phaseDifference a (phase4 f))) ↔
        ∀ a, DiagonalDifference.Depth k (DiagonalDifference.diff a f)
      simp_rw [phase4_difference, ih]

/-- 模4有限差分判据已经接到真正酉矩阵Pauli共轭定义。 -/
theorem diagonal4_isLevel_iff {n k : ℕ} (hk : 0 < k)
    (f : DiagonalDifference.Phase4 n) :
    IsLevel k (diagonal4 f) ↔ DiagonalDifference.Depth k f := by
  rw [diagonal4, diagonalGate_isLevel_iff hk, phaseDepth_phase4_iff]

end UnifiedEJM.CliffordFoundation


