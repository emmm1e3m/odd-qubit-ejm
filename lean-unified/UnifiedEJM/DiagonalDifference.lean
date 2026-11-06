import OddEJM.Pauli
import Mathlib.Tactic

namespace UnifiedEJM.DiagonalDifference
open OddEJM
open scoped BigOperators

abbrev Phase4 (n : ℕ) := Bits n → ZMod 4

/-- 模4相位的真实平移差分。 -/
def diff {n : ℕ} (a : Bits n) (f : Phase4 n) : Phase4 n :=
  fun z => f (z + a) - f z

def translate {n : ℕ} (a : Bits n) (f : Phase4 n) : Phase4 n :=
  fun z => f (z + a)

/-- 第零层是常相位；每次差分降低一层。 -/
def Depth {n : ℕ} : ℕ → Phase4 n → Prop
  | 0, f => ∀ x y, f x = f y
  | k+1, f => ∀ a, Depth k (diff a f)

def CoordinateDepth {n : ℕ} : ℕ → Phase4 n → Prop
  | 0, f => ∀ x y, f x = f y
  | k+1, f => ∀ j : Fin n, CoordinateDepth k (diff (unitBit n j.val) f)

@[simp] theorem diff_zero {n} (f : Phase4 n) : diff 0 f = 0 := by
  ext z
  simp [diff]

theorem diff_add {n} (a : Bits n) (f g : Phase4 n) :
    diff a (f+g) = diff a f + diff a g := by
  ext z
  simp [diff]
  ring

theorem diff_neg {n} (a : Bits n) (f : Phase4 n) :
    diff a (-f) = -diff a f := by
  ext z
  simp [diff]
  ring

theorem diff_comm {n} (a b : Bits n) (f : Phase4 n) :
    diff a (diff b f) = diff b (diff a f) := by
  ext z
  simp only [diff]
  rw [show z+a+b=z+b+a by abel]
  ring

theorem diff_translate {n} (a b : Bits n) (f : Phase4 n) :
    diff a (translate b f) = translate b (diff a f) := by
  ext z
  simp only [diff, translate]
  rw [show z+a+b=z+b+a by abel]

theorem diff_add_direction {n} (a b : Bits n) (f : Phase4 n) :
    diff (a+b) f = translate b (diff a f) + diff b f := by
  ext z
  simp only [diff, translate, Pi.add_apply]
  rw [show z+(a+b)=z+b+a by abel]
  ring

theorem coordinate_const {n} (k : ℕ) (c : ZMod 4) :
    CoordinateDepth (n := n) k (fun _ => c) := by
  induction k generalizing c with
  | zero => intro x y; rfl
  | succ k ih =>
    intro j
    change CoordinateDepth k (fun _ : Bits n => c-c)
    simp only [sub_self]
    exact ih 0

theorem coordinate_add {n} {k : ℕ} {f g : Phase4 n}
    (hf : CoordinateDepth k f) (hg : CoordinateDepth k g) :
    CoordinateDepth k (f+g) := by
  induction k generalizing f g with
  | zero => intro x y; simp only [Pi.add_apply, hf x y, hg x y]
  | succ k ih =>
    intro j
    rw [diff_add]
    exact ih (hf j) (hg j)

theorem coordinate_neg {n} {k : ℕ} {f : Phase4 n}
    (hf : CoordinateDepth k f) : CoordinateDepth k (-f) := by
  induction k generalizing f with
  | zero => intro x y; simp only [Pi.neg_apply, hf x y]
  | succ k ih =>
    intro j
    rw [diff_neg]
    exact ih (hf j)

theorem coordinate_translate {n} {k : ℕ} {f : Phase4 n}
    (hf : CoordinateDepth k f) (a : Bits n) :
    CoordinateDepth k (translate a f) := by
  induction k generalizing f with
  | zero => intro x y; exact hf (x+a) (y+a)
  | succ k ih =>
    intro j
    rw [diff_translate]
    exact ih (hf j)

theorem bits_sum_units {n : ℕ} (a : Bits n) :
    a = ∑ j : Fin n, if a j = 0 then 0 else unitBit n j.val := by
  ext i
  simp only [Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : a i = 0
    · simp [h]
    · have h1 : a i = 1 := (CircuitPauli.bit_cases (a i)).resolve_left h
      simp [h, h1, unitBit]
  · intro j _ hji
    have hij : i.val ≠ j.val := by
      intro h
      exact hji (Fin.ext h.symm)
    split_ifs <;> simp [unitBit, hij]
  · simp

theorem coordinate_arbitrary_diff {n : ℕ} {k : ℕ} {f : Phase4 n}
    (hf : CoordinateDepth (k+1) f) (a : Bits n) :
    CoordinateDepth k (diff a f) := by
  have hsum : ∀ S : Finset (Fin n),
      CoordinateDepth k (diff (∑ j ∈ S, if a j = 0 then 0 else unitBit n j.val) f) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, diff_zero]
      exact coordinate_const (n := n) k 0
    | @insert j S hj ih =>
      rw [Finset.sum_insert hj, diff_add_direction]
      apply coordinate_add
      · apply coordinate_translate
        by_cases h : a j = 0
        · simp only [h, ite_true, diff_zero]
          exact coordinate_const k 0
        · simpa only [h, ite_false] using hf j
      · exact ih
  rw [bits_sum_units a]
  simpa using hsum Finset.univ

theorem depth_iff_coordinate {n : ℕ} (k : ℕ) (f : Phase4 n) :
    Depth k f ↔ CoordinateDepth k f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    constructor
    · intro h j
      exact (ih _).mp (h (unitBit n j.val))
    · intro h a
      exact (ih _).mpr (coordinate_arbitrary_diff h a)

theorem depth_const {n} (k : ℕ) (c : ZMod 4) :
    Depth (n := n) k (fun _ => c) :=
  (depth_iff_coordinate k _).mpr (coordinate_const k c)

theorem depth_add {n} {k : ℕ} {f g : Phase4 n}
    (hf : Depth k f) (hg : Depth k g) : Depth k (f+g) :=
  (depth_iff_coordinate k _).mpr
    (coordinate_add ((depth_iff_coordinate k _).mp hf) ((depth_iff_coordinate k _).mp hg))

theorem depth_neg {n} {k : ℕ} {f : Phase4 n}
    (hf : Depth k f) : Depth k (-f) :=
  (depth_iff_coordinate k _).mpr (coordinate_neg ((depth_iff_coordinate k _).mp hf))

theorem depth_sub {n} {k : ℕ} {f g : Phase4 n}
    (hf : Depth k f) (hg : Depth k g) : Depth k (f-g) := by
  rw [sub_eq_add_neg]
  exact depth_add hf (depth_neg hg)

theorem depth_translate {n} {k : ℕ} {f : Phase4 n}
    (hf : Depth k f) (a : Bits n) : Depth k (translate a f) :=
  (depth_iff_coordinate k _).mpr (coordinate_translate ((depth_iff_coordinate k _).mp hf) a)

theorem depth_mono_succ {n} {k : ℕ} {f : Phase4 n}
    (hf : Depth k f) : Depth (k+1) f := by
  induction k generalizing f with
  | zero =>
    intro a x y
    simp only [diff, hf (x+a) x, hf (y+a) y, sub_self]
  | succ k ih => intro a; exact ih (hf a)

theorem depth_mono {n} {k l : ℕ} {f : Phase4 n}
    (hkl : k ≤ l) (hf : Depth k f) : Depth l f := by
  induction l, hkl using Nat.le_induction with
  | base => exact hf
  | succ l hl ih => exact depth_mono_succ ih

theorem depth_succ_of_coordinates {n k} {f : Phase4 n}
    (h : ∀ j : Fin n, Depth k (diff (unitBit n j.val) f)) : Depth (k+1) f := by
  apply (depth_iff_coordinate (k+1) f).mpr
  intro j
  exact (depth_iff_coordinate k _).mp (h j)

theorem depth_pullback {m n k} (L : Bits m →+ Bits n) {f : Phase4 n}
    (h : Depth k f) : Depth k (f ∘ L) := by
  induction k generalizing f with
  | zero => intro x y; exact h (L x) (L y)
  | succ k ih =>
    intro a
    have heq : diff a (f ∘ L) = diff (L a) f ∘ L := by
      ext z
      simp [diff]
    rw [heq]
    exact ih (h (L a))

theorem depth_pullback_iff {m n k} (L : Bits m →+ Bits n)
    (hL : Function.Surjective L) (f : Phase4 n) :
    Depth k (f ∘ L) ↔ Depth k f := by
  constructor
  · intro h
    induction k generalizing f with
    | zero =>
      intro x y
      obtain ⟨x',rfl⟩ := hL x
      obtain ⟨y',rfl⟩ := hL y
      exact h x' y'
    | succ k ih =>
      intro a
      obtain ⟨a',rfl⟩ := hL a
      apply ih
      have heq : diff a' (f ∘ L) = diff (L a') f ∘ L := by
        ext z
        simp [diff]
      rw [← heq]
      exact h a'
  · exact depth_pullback L

def scale {n} (c : ZMod 4) (f : Phase4 n) : Phase4 n := fun z => c * f z

theorem diff_scale {n} (a : Bits n) (c : ZMod 4) (f : Phase4 n) :
    diff a (scale c f) = scale c (diff a f) := by
  ext z
  simp only [diff,scale]
  ring

theorem depth_scale {n k} {f : Phase4 n} (h : Depth k f) (c : ZMod 4) :
    Depth k (scale c f) := by
  induction k generalizing f with
  | zero => intro x y; simp only [scale,h x y]
  | succ k ih => intro a; rw [diff_scale]; exact ih (h a)

def subsetZero {n} (S : Finset (Fin n)) : Phase4 n :=
  fun z => if ∀ j ∈ S, z j = 0 then 1 else 0

@[simp] theorem unitBit_apply_fin {n} (j i : Fin n) :
    unitBit n j.val i = if i=j then 1 else 0 := by
  simp [unitBit,Fin.ext_iff]

theorem subsetZero_split {n} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (z : Bits n) :
    subsetZero S z = if z j = 0 then subsetZero (S.erase j) z else 0 := by
  have hcond : (∀ i ∈ S, z i=0) ↔ z j=0 ∧ ∀ i ∈ S.erase j, z i=0 := by
    constructor
    · intro h
      exact ⟨h j hj,fun i hi => h i (Finset.mem_of_mem_erase hi)⟩
    · rintro ⟨hz,h⟩ i hi
      by_cases hij : i=j
      · simpa [hij] using hz
      · exact h i (Finset.mem_erase.mpr ⟨hij,hi⟩)
  simp only [subsetZero,hcond]
  split_ifs <;> simp_all

theorem subsetZero_translate_of_not_mem {n} (S : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ S) : translate (unitBit n j.val) (subsetZero S) = subsetZero S := by
  ext z
  simp only [translate,subsetZero,Pi.add_apply,unitBit_apply_fin]
  have heq : (∀ i ∈ S, z i + (if i=j then 1 else 0)=0) ↔ (∀ i ∈ S,z i=0) := by
    constructor <;> intro h i hi
    · have hij : i≠j := by intro he; subst i; exact hj hi
      simpa [hij] using h i hi
    · have hij : i≠j := by intro he; subst i; exact hj hi
      simpa [hij] using h i hi
  simp only [heq]

theorem subsetZero_diff_of_not_mem {n} (S : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ S) : diff (unitBit n j.val) (subsetZero S) = 0 := by
  have h := subsetZero_translate_of_not_mem S j hj
  ext z
  have hz := congrFun h z
  simp only [translate] at hz
  simp [diff,hz]

theorem subsetZero_diff_of_mem {n} (S : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ S) :
    diff (unitBit n j.val) (subsetZero S) =
      subsetZero (S.erase j) - scale 2 (subsetZero S) := by
  ext z
  have hshift := congrFun (subsetZero_translate_of_not_mem (S.erase j) j (by simp)) z
  simp only [translate] at hshift
  simp only [diff,Pi.sub_apply,scale,subsetZero_split S j hj,
    Pi.add_apply,unitBit_apply_fin,ite_true,hshift]
  rcases CircuitPauli.bit_cases (z j) with hz | hz
  · simp [hz]
    ring
  · simp [hz, show (1 : Bit)+1=0 by decide]

theorem subsetZero_depths {n} (S : Finset (Fin n)) :
    Depth S.card (scale 2 (subsetZero S)) ∧ Depth (S.card+1) (subsetZero S) := by
  refine Finset.strongInductionOn S (fun S ih => ?_)
  · by_cases hS : S=∅
    · subst S
      have he : subsetZero (n := n) ∅ = fun _ => 1 := by
        ext z
        simp [subsetZero]
      rw [he]
      constructor
      · change Depth 0 (fun _ : Bits n => (2 : ZMod 4)*1)
        exact depth_const 0 (2*1)
      · exact depth_const 1 1
    · have hc : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      have hecard (j : Fin n) (hj : j∈S) : (S.erase j).card = S.card-1 :=
        Finset.card_erase_of_mem hj
      have herase (j : Fin n) (hj : j∈S) : S.erase j ⊂ S :=
        Finset.erase_ssubset hj
      have htwo : Depth S.card (scale 2 (subsetZero S)) := by
        rw [show S.card=(S.card-1)+1 by omega]
        apply depth_succ_of_coordinates
        intro j
        rw [diff_scale]
        by_cases hj : j∈S
        · rw [subsetZero_diff_of_mem S j hj]
          have heq : scale 2 (subsetZero (S.erase j) - scale 2 (subsetZero S)) =
              scale 2 (subsetZero (S.erase j)) := by
            ext z
            simp only [scale,Pi.sub_apply]
            ring_nf
            simp [show (4 : ZMod 4)=0 by decide]
          rw [heq]
          simpa only [hecard j hj] using (ih (S.erase j) (herase j hj)).1
        · rw [subsetZero_diff_of_not_mem S j hj]
          have hz : scale (n := n) 2 0 = fun _ => 0 := by ext z; simp [scale]
          rw [hz]
          exact depth_const _ 0
      refine ⟨htwo, ?_⟩
      apply depth_succ_of_coordinates
      intro j
      by_cases hj : j∈S
      · rw [subsetZero_diff_of_mem S j hj]
        apply depth_sub
        · have hi := (ih (S.erase j) (herase j hj)).2
          have he : (S.erase j).card+1=S.card := by rw [hecard j hj]; omega
          simpa only [he] using hi
        · exact htwo
      · rw [subsetZero_diff_of_not_mem S j hj]
        exact depth_const _ 0

def delta {n} : Phase4 n := subsetZero Finset.univ

theorem delta_depth {n} : Depth (n+1) (delta (n := n)) := by
  simpa only [delta,Finset.card_univ,Fintype.card_fin] using
    (subsetZero_depths (Finset.univ : Finset (Fin n))).2

theorem twice_delta_depth {n} : Depth n (scale 2 (delta (n := n))) := by
  simpa only [delta,Finset.card_univ,Fintype.card_fin] using
    (subsetZero_depths (Finset.univ : Finset (Fin n))).1

end UnifiedEJM.DiagonalDifference
