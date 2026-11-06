import UnifiedEJM.DiagonalDifference
import UnifiedEJM.Features

namespace UnifiedEJM.DiagonalDifference
open OddEJM
open scoped BigOperators

/-- 固定首位为零的线性嵌入，用于混合差分归纳。 -/
def tailEmbed (n : ℕ) : Bits n →+ Bits (n+1) where
  toFun z := Fin.cons 0 z
  map_zero' := by ext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp
  map_add' x y := by ext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp

theorem cons_zero_add_first {n} (z : Bits n) :
    Fin.cons 0 z + unitBit (n+1) 0 = Fin.cons 1 z := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [unitBit]
  · simp [unitBit]

theorem cons_one_add_first {n} (z : Bits n) :
    Fin.cons 1 z + unitBit (n+1) 0 = Fin.cons 0 z := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [unitBit,show (1 : Bit)+1=0 by decide]
  · simp [unitBit]

/-- 沿全部坐标各作一次差分，在零串取值。 -/
def cubeDiff : (n : ℕ) → Phase4 n → ZMod 4
  | 0, f => f 0
  | n+1, f => cubeDiff n (fun z => f (Fin.cons 1 z) - f (Fin.cons 0 z))

theorem cubeDiff_add (n) (f g : Phase4 n) :
    cubeDiff n (f+g) = cubeDiff n f + cubeDiff n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeDiff]
    have he : (fun z => (f+g) (Fin.cons 1 z) - (f+g) (Fin.cons 0 z)) =
        (fun z => f (Fin.cons 1 z) - f (Fin.cons 0 z)) +
        (fun z => g (Fin.cons 1 z) - g (Fin.cons 0 z)) := by ext z; simp; ring
    rw [he,ih]

theorem cubeDiff_scale (n) (c : ZMod 4) (f : Phase4 n) :
    cubeDiff n (scale c f) = c * cubeDiff n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeDiff]
    have he : (fun z => scale c f (Fin.cons 1 z) - scale c f (Fin.cons 0 z)) =
        scale c (fun z => f (Fin.cons 1 z) - f (Fin.cons 0 z)) := by
      ext z; simp [scale]; ring
    rw [he,ih]

theorem cubeDiff_neg (n) (f : Phase4 n) :
    cubeDiff n (-f) = -cubeDiff n f := by
  have he : -f = scale (-1) f := by ext z; simp [scale]
  rw [he,cubeDiff_scale]
  ring

theorem depth_cubeDiff_zero (n : ℕ) (f : Phase4 (n+1))
    (h : Depth n f) : cubeDiff (n+1) f = 0 := by
  induction n with
  | zero =>
    simp only [cubeDiff]
    exact sub_eq_zero.mpr (h _ _)
  | succ n ih =>
    let g : Phase4 (n+1) := fun z => f (Fin.cons 1 z) - f (Fin.cons 0 z)
    have hg : Depth n g := by
      have hp := depth_pullback (tailEmbed (n+1)) (h (unitBit (n+2) 0))
      have he : diff (unitBit (n+2) 0) f ∘ tailEmbed (n+1) = g := by
        ext z
        simp only [Function.comp_apply,tailEmbed,AddMonoidHom.coe_mk,ZeroHom.coe_mk,diff]
        rw [cons_zero_add_first]
      rwa [he] at hp
    exact ih g hg

theorem cubeDiff_first_diff (n : ℕ) (f : Phase4 (n+1)) :
    cubeDiff (n+1) (diff (unitBit (n+1) 0) f) = -2 * cubeDiff (n+1) f := by
  simp only [cubeDiff]
  have he : (fun z => diff (unitBit (n+1) 0) f (Fin.cons 1 z) -
      diff (unitBit (n+1) 0) f (Fin.cons 0 z)) =
      scale (-2) (fun z => f (Fin.cons 1 z)-f (Fin.cons 0 z)) := by
    ext z
    simp only [diff,cons_one_add_first,cons_zero_add_first,scale]
    ring
  rw [he,cubeDiff_scale]

theorem depth_twice_cubeDiff_zero (n : ℕ) (f : Phase4 (n+1))
    (h : Depth (n+1) f) : 2 * cubeDiff (n+1) f = 0 := by
  have hz := depth_cubeDiff_zero n (diff (unitBit (n+1) 0) f) (h _)
  rw [cubeDiff_first_diff] at hz
  have he : -2 * cubeDiff (n+1) f = -(2 * cubeDiff (n+1) f) := by ring
  rw [he,neg_eq_zero] at hz
  exact hz

@[simp] theorem delta_cons_zero {n} (z : Bits n) :
    delta (Fin.cons 0 z) = delta z := by
  simp [delta,subsetZero,Fin.forall_fin_succ]

@[simp] theorem delta_cons_one {n} (z : Bits n) :
    delta (Fin.cons 1 z) = 0 := by
  simp [delta,subsetZero,Fin.forall_fin_succ]

theorem cubeDiff_delta (n : ℕ) : cubeDiff n (delta (n := n)) = (-1)^n := by
  induction n with
  | zero => simp [cubeDiff,delta,subsetZero]
  | succ n ih =>
    rw [cubeDiff]
    have he : (fun z : Bits n => delta (Fin.cons 1 z)-delta (Fin.cons 0 z)) = -delta := by
      ext z
      simp
    rw [he,cubeDiff_neg,ih,pow_succ]
    ring

theorem two_mul_neg_one_pow_ne_zero (n : ℕ) : (2 : ZMod 4)*(-1)^n ≠ 0 := by
  intro h
  have hs : (-1 : ZMod 4)^n * (-1)^n = 1 := by
    rw [←mul_pow]
    norm_num
  have he : (2 : ZMod 4)=0 := by
    calc
      2 = 2*((-1 : ZMod 4)^n * (-1)^n) := by rw [hs]; ring
      _ = (2*(-1)^n)*(-1)^n := by ring
      _ = 0 := by rw [h]; ring
  exact (by decide : (2 : ZMod 4)≠0) he

theorem delta_not_depth {n : ℕ} (hn : 0<n) : ¬Depth n (delta (n := n)) := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    have hz := depth_twice_cubeDiff_zero n delta h
    rw [cubeDiff_delta] at hz
    exact two_mul_neg_one_pow_ne_zero (n+1) hz

theorem twice_delta_not_depth {n : ℕ} (hn : 0<n) :
    ¬Depth (n-1) (scale 2 (delta (n := n))) := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    have hz := depth_cubeDiff_zero n (scale 2 delta) h
    rw [cubeDiff_scale,cubeDiff_delta] at hz
    exact two_mul_neg_one_pow_ne_zero (n+1) hz

def kernelPhase : Phase4 4 := fun v => (UnifiedEJM.F v).val

def kernelTerms : Fin 12 → ZMod 4 × Finset (Fin 4) :=
  ![(1,∅),(3,{0}),(3,{1}),(2,{0,1}),(1,{0,2}),(1,{1,2}),
    (2,{0,1,2}),(3,{3}),(1,{0,3}),(2,{1,3}),(2,{0,1,3}),(3,{1,2,3})]

def positiveMonomial {n} (S : Finset (Fin n)) : Phase4 n :=
  translate (fun _ => 1) (subsetZero S)

def kernelModel : Phase4 4 :=
  ∑ i : Fin 12, scale (kernelTerms i).1 (positiveMonomial (kernelTerms i).2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kernel_eq_model : kernelPhase = kernelModel := by
  funext v
  exact (by decide : ∀ v, kernelPhase v = kernelModel v) v

theorem depth_sum {n k} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → Phase4 n) (hf : ∀ i ∈ S, Depth k (f i)) :
    Depth k (∑ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact depth_const k 0
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact depth_add (hf i (Finset.mem_insert_self i S))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem kernel_depth : Depth 4 kernelPhase := by
  rw [kernel_eq_model]
  unfold kernelModel
  apply depth_sum
  intro i _
  apply depth_scale
  apply depth_mono (k := (kernelTerms i).2.card+1)
  · exact (by decide : ∀ i : Fin 12, (kernelTerms i).2.card+1 ≤ 4) i
  · exact depth_translate (subsetZero_depths (kernelTerms i).2).2 (fun _ => 1)

theorem kernel_not_depth : ¬Depth 3 kernelPhase := by
  intro h
  let b := unitBit 4 1
  let c := unitBit 4 2
  let s := unitBit 4 3
  have hz : diff b (diff s (diff c (diff b kernelPhase))) 0 = 0 := by
    change diff s (diff c (diff b kernelPhase)) (0+b) -
      diff s (diff c (diff b kernelPhase)) 0 = 0
    exact sub_eq_zero.mpr (h b c s (0+b) 0)
  have hv : diff b (diff s (diff c (diff b kernelPhase))) 0 = 2 := by decide
  rw [hv] at hz
  exact (by decide : (2 : ZMod 4)≠0) hz

end UnifiedEJM.DiagonalDifference
