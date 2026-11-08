import UnifiedEJM.PhysicsClosureNodeFacts
import UnifiedEJM.PhysicsSparseInitial

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- 固定首站字与证书整数编码的显式连接。 -/
private theorem initial_firstWord_eq : bits4 4 = firstWord := by decide +kernel

/-- 两个首站B支撑由同一整数列表定义。 -/
private theorem initial_B_support_eq : support1776 = initialBSupport := by rfl

def initialNode (first second third : Bool) : Fin 1756 :=
  if first then (if second then (if third then 7 else 6) else (if third then 5 else 4))
  else (if second then (if third then 3 else 2) else (if third then 1 else 0))

theorem initialNode_current : ∀ first second third,
    nodeCurrent (initialNode first second third) = ⟨third, middleWord⟩ := by
  intro first second third
  cases first <;> cases second <;> cases third <;> rfl

theorem initialNode_scan : ∀ first second third,
    nodeScan (initialNode first second third) = scanFirstThree first second third := by
  intro first second third
  cases first <;> cases second <;> cases third <;> rfl

theorem initialNode_parity : ∀ first second third,
    (nodeData (initialNode first second third)).parity = true := by
  intro first second third
  cases first <;> cases second <;> cases third <;> rfl

theorem initialPrefix0 (d : Logical) :
    evolve d ⟨false, bits4 4⟩ [⟨false, bits4 1⟩, ⟨false, bits4 8⟩] (initial ⟨false, bits4 4⟩) =
      nodeDecode 0 d := by
  have hi : initial ⟨false, bits4 4⟩ = decode support1776 (1 / (2 : ℚ) ^ 0) d := by
    funext t
    simpa only [pow_zero, div_one, initial_firstWord_eq, initial_B_support_eq]
      using initialB_checked d t
  have h1 := fun e => funext (checked_transition ⟨false, bits4 4⟩ ⟨false, bits4 1⟩ support1776 support0180 1 transition3166 (1 / (2 : ℚ) ^ 0) (1 / (2 : ℚ) ^ 0) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨false, bits4 1⟩ ⟨false, bits4 8⟩ support0180 support0000 1 transition3167 (1 / (2 : ℚ) ^ 0) (1 / (2 : ℚ) ^ 0) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨false, bits4 1⟩ ⟨false, bits4 8⟩)
    ((congrArg (advance d ⟨false, bits4 4⟩ ⟨false, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix1 (d : Logical) :
    evolve d ⟨false, bits4 4⟩ [⟨false, bits4 1⟩, ⟨true, bits4 8⟩] (initial ⟨false, bits4 4⟩) =
      nodeDecode 1 d := by
  have hi : initial ⟨false, bits4 4⟩ = decode support1776 (1 / (2 : ℚ) ^ 0) d := by
    funext t
    simpa only [pow_zero, div_one, initial_firstWord_eq, initial_B_support_eq]
      using initialB_checked d t
  have h1 := fun e => funext (checked_transition ⟨false, bits4 4⟩ ⟨false, bits4 1⟩ support1776 support0180 1 transition3166 (1 / (2 : ℚ) ^ 0) (1 / (2 : ℚ) ^ 0) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨false, bits4 1⟩ ⟨true, bits4 8⟩ support0180 support0001 1 transition3168 (1 / (2 : ℚ) ^ 0) (1 / (2 : ℚ) ^ 1) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨false, bits4 1⟩ ⟨true, bits4 8⟩)
    ((congrArg (advance d ⟨false, bits4 4⟩ ⟨false, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix2 (d : Logical) :
    evolve d ⟨false, bits4 4⟩ [⟨true, bits4 1⟩, ⟨false, bits4 8⟩] (initial ⟨false, bits4 4⟩) =
      nodeDecode 2 d := by
  have hi : initial ⟨false, bits4 4⟩ = decode support1776 (1 / (2 : ℚ) ^ 0) d := by
    funext t
    simpa only [pow_zero, div_one, initial_firstWord_eq, initial_B_support_eq]
      using initialB_checked d t
  have h1 := fun e => funext (checked_transition ⟨false, bits4 4⟩ ⟨true, bits4 1⟩ support1776 support0372 1 transition3169 (1 / (2 : ℚ) ^ 0) (1 / (2 : ℚ) ^ 1) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨true, bits4 1⟩ ⟨false, bits4 8⟩ support0372 support0002 1 transition3170 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 1) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨true, bits4 1⟩ ⟨false, bits4 8⟩)
    ((congrArg (advance d ⟨false, bits4 4⟩ ⟨true, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix3 (d : Logical) :
    evolve d ⟨false, bits4 4⟩ [⟨true, bits4 1⟩, ⟨true, bits4 8⟩] (initial ⟨false, bits4 4⟩) =
      nodeDecode 3 d := by
  have hi : initial ⟨false, bits4 4⟩ = decode support1776 (1 / (2 : ℚ) ^ 0) d := by
    funext t
    simpa only [pow_zero, div_one, initial_firstWord_eq, initial_B_support_eq]
      using initialB_checked d t
  have h1 := fun e => funext (checked_transition ⟨false, bits4 4⟩ ⟨true, bits4 1⟩ support1776 support0372 1 transition3169 (1 / (2 : ℚ) ^ 0) (1 / (2 : ℚ) ^ 1) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨true, bits4 1⟩ ⟨true, bits4 8⟩ support0372 support0003 1 transition3171 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 2) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨true, bits4 1⟩ ⟨true, bits4 8⟩)
    ((congrArg (advance d ⟨false, bits4 4⟩ ⟨true, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix4 (d : Logical) :
    evolve d ⟨true, bits4 4⟩ [⟨false, bits4 1⟩, ⟨false, bits4 8⟩] (initial ⟨true, bits4 4⟩) =
      nodeDecode 4 d := by
  have hi : initial ⟨true, bits4 4⟩ = decode support1777 (1 / (2 : ℚ) ^ 1) d := by
    funext t
    exact initialA_checked d t
  have h1 := fun e => funext (checked_transition ⟨true, bits4 4⟩ ⟨false, bits4 1⟩ support1777 support1778 1 transition3172 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 1) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨false, bits4 1⟩ ⟨false, bits4 8⟩ support1778 support0004 1 transition3173 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 1) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨false, bits4 1⟩ ⟨false, bits4 8⟩)
    ((congrArg (advance d ⟨true, bits4 4⟩ ⟨false, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix5 (d : Logical) :
    evolve d ⟨true, bits4 4⟩ [⟨false, bits4 1⟩, ⟨true, bits4 8⟩] (initial ⟨true, bits4 4⟩) =
      nodeDecode 5 d := by
  have hi : initial ⟨true, bits4 4⟩ = decode support1777 (1 / (2 : ℚ) ^ 1) d := by
    funext t
    exact initialA_checked d t
  have h1 := fun e => funext (checked_transition ⟨true, bits4 4⟩ ⟨false, bits4 1⟩ support1777 support1778 1 transition3172 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 1) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨false, bits4 1⟩ ⟨true, bits4 8⟩ support1778 support0005 1 transition3174 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 2) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨false, bits4 1⟩ ⟨true, bits4 8⟩)
    ((congrArg (advance d ⟨true, bits4 4⟩ ⟨false, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix6 (d : Logical) :
    evolve d ⟨true, bits4 4⟩ [⟨true, bits4 1⟩, ⟨false, bits4 8⟩] (initial ⟨true, bits4 4⟩) =
      nodeDecode 6 d := by
  have hi : initial ⟨true, bits4 4⟩ = decode support1777 (1 / (2 : ℚ) ^ 1) d := by
    funext t
    exact initialA_checked d t
  have h1 := fun e => funext (checked_transition ⟨true, bits4 4⟩ ⟨true, bits4 1⟩ support1777 support1779 1 transition3175 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 2) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨true, bits4 1⟩ ⟨false, bits4 8⟩ support1779 support0006 1 transition3176 (1 / (2 : ℚ) ^ 2) (1 / (2 : ℚ) ^ 2) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨true, bits4 1⟩ ⟨false, bits4 8⟩)
    ((congrArg (advance d ⟨true, bits4 4⟩ ⟨true, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix7 (d : Logical) :
    evolve d ⟨true, bits4 4⟩ [⟨true, bits4 1⟩, ⟨true, bits4 8⟩] (initial ⟨true, bits4 4⟩) =
      nodeDecode 7 d := by
  have hi : initial ⟨true, bits4 4⟩ = decode support1777 (1 / (2 : ℚ) ^ 1) d := by
    funext t
    exact initialA_checked d t
  have h1 := fun e => funext (checked_transition ⟨true, bits4 4⟩ ⟨true, bits4 1⟩ support1777 support1779 1 transition3175 (1 / (2 : ℚ) ^ 1) (1 / (2 : ℚ) ^ 2) (by norm_num [siteWeight]) e)
  have h2 := fun e => funext (checked_transition ⟨true, bits4 1⟩ ⟨true, bits4 8⟩ support1779 support0007 1 transition3177 (1 / (2 : ℚ) ^ 2) (1 / (2 : ℚ) ^ 3) (by norm_num [siteWeight]) e)
  exact (congrArg (advance d ⟨true, bits4 1⟩ ⟨true, bits4 8⟩)
    ((congrArg (advance d ⟨true, bits4 4⟩ ⟨true, bits4 1⟩) hi).trans (h1 d))).trans (h2 d)

theorem initialPrefix_eq (first second third : Bool) (d : Logical) :
    evolve d ⟨first, firstWord⟩ [⟨second, secondWord⟩, ⟨third, middleWord⟩]
      (initial ⟨first, firstWord⟩) = nodeDecode (initialNode first second third) d := by
  cases first <;> cases second <;> cases third
  · exact initialPrefix0 d
  · exact initialPrefix1 d
  · exact initialPrefix2 d
  · exact initialPrefix3 d
  · exact initialPrefix4 d
  · exact initialPrefix5 d
  · exact initialPrefix6 d
  · exact initialPrefix7 d

/-- 首三站的真实路径分布接到闭包初态，后缀仍保持任意长度。 -/
theorem backgroundWeight_initialNode (first second third : Bool) (middle : List Bool)
    (pen last : Bool) (d k : Logical) :
    backgroundWeight first second (third :: middle) pen last d k =
      finish d ⟨last, firstWord⟩
        (evolve d (nodeCurrent (initialNode first second third))
          (middle.map centralSite ++ [⟨pen, penultimateWord⟩, ⟨last, firstWord⟩])
          (nodeDecode (initialNode first second third) d)) k := by
  have hp := initialPrefix_eq first second third d
  change finish d ⟨last, firstWord⟩
    (evolve d ⟨third, middleWord⟩
      (middle.map centralSite ++ [⟨pen, penultimateWord⟩, ⟨last, firstWord⟩])
      (evolve d ⟨first, firstWord⟩ [⟨second, secondWord⟩, ⟨third, middleWord⟩]
        (initial ⟨first, firstWord⟩))) k = _
  conv_rhs => rw [initialNode_current]
  exact congrArg (fun μ : Distribution => finish d ⟨last, firstWord⟩
    (evolve d ⟨third, middleWord⟩
      (middle.map centralSite ++ [⟨pen, penultimateWord⟩, ⟨last, firstWord⟩]) μ) k) hp

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
