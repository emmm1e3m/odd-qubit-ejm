import UnifiedEJM.Core
import UnifiedEJM.EvenCertificate
import OddEJM.Walsh
import Mathlib.Tactic

namespace UnifiedEJM.EvenWalsh
open OddEJM
open scoped BigOperators

/-- 物理偶内部位在零基编号中为奇数坐标。 -/
def InE (n j : ℕ) : Prop := 1 ≤ j ∧ j < n - 2 ∧ j % 2 = 1

instance (n j : ℕ) : Decidable (InE n j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def EZero {n : ℕ} (z : Bits n) : Prop := ∀ j : Fin n, InE n j.val → z j = 0

instance {n : ℕ} (z : Bits n) : Decidable (EZero z) :=
  inferInstanceAs (Decidable (∀ j : Fin n, InE n j.val → z j = 0))

/-- 原偶数族的 AND 支持，保留物理零点。 -/
def qA {n : ℕ} (z : Bits n) : Bit := if EZero z then 1 else 0

/-- 删除的是唯一物理零串。 -/
def dA {n : ℕ} (z : Bits n) : Bit := if z = 0 then 0 else qA z

@[simp] theorem ezero_zero (n : ℕ) : EZero (0 : Bits n) := by
  intro j _; rfl

@[simp] theorem qA_zero (n : ℕ) : qA (0 : Bits n) = 1 := by simp [qA]

theorem ezero_add {n : ℕ} {z w : Bits n} (hz : EZero z) (hw : EZero w) :
    EZero (z + w) := by
  intro j hj
  simp [hz j hj, hw j hj]

theorem ezero_add_iff {n : ℕ} (z w : Bits n) (hw : EZero w) :
    EZero (z + w) ↔ EZero z := by
  constructor
  · intro hz j hj
    have hh := hz j hj
    simpa [hw j hj] using hh
  · intro hz; exact ezero_add hz hw

theorem qA_add {n : ℕ} (z w : Bits n) (hw : EZero w) : qA (z + w) = qA z := by
  simp only [qA, ezero_add_iff z w hw]

theorem ezero_unit {n : ℕ} (j : ℕ) (hj : ¬ InE n j) : EZero (unitBit n j) := by
  intro i hi
  have hne : i.val ≠ j := by intro he; apply hj; simpa [he] using hi
  simp [unitBit, hne]

theorem ezero_smul {n : ℕ} (r : Bit) {z : Bits n} (hz : EZero z) : EZero (r • z) := by
  intro i hi; simp [hz i hi]

theorem blockParity_E_zero {n : ℕ} {z : Bits n} (hz : EZero z) : blockParity z 1 = 0 := by
  unfold blockParity
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · exact hz i hi
  · rfl

/-- AND 正扇区保留四个自由特征。 -/
def sector4 {n : ℕ} (z : Bits n) : Bits 4 :=
  ![coord z 0, blockParity z 0, coord z (n - 2), coord z (n - 1)]

def embedSector (e : Bit) (w : Bits 4) : Bits 5 := ![w 0, e, w 1, w 2, w 3]

theorem compress_of_ezero {n : ℕ} {z : Bits n} (hz : EZero z) :
    compress z = embedSector 0 (sector4 z) := by
  ext i; fin_cases i <;> simp [compress, embedSector, sector4, blockParity_E_zero hz]

theorem sector4_add {n : ℕ} (z w : Bits n) : sector4 (z + w) = sector4 z + sector4 w := by
  ext i; fin_cases i <;> simp [sector4, at_add, blockParity_add]

def expandSector (n : ℕ) (v : Bits 4) : Bits n := expand5 n (embedSector 0 v)

theorem expandSector_ezero {n : ℕ} (hn : 5 ≤ n) (v : Bits 4) :
    EZero (expandSector n v) := by
  unfold expandSector expand5 embedSector
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_smul, add_zero]
  apply ezero_add
  · apply ezero_add
    · apply ezero_add
      · apply ezero_smul; apply ezero_unit; simp [InE]
      · apply ezero_smul; apply ezero_unit; simp [InE]
    · apply ezero_smul; apply ezero_unit; simp [InE]
  · apply ezero_smul; apply ezero_unit; unfold InE; omega

theorem sector4_expand {n : ℕ} (hn : 5 ≤ n) (v : Bits 4) :
    sector4 (expandSector n v) = v := by
  have h := compress_expand5 hn (embedSector 0 v)
  change compress (expandSector n v) = embedSector 0 v at h
  have hz := compress_of_ezero (expandSector_ezero hn v)
  rw [hz] at h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 2
  · exact congrFun h 3
  · exact congrFun h 4

/-- 在 AND 正扇区作平移平均；任意长度只需一个固定四位证书。 -/
theorem sum_sector4_zero {n : ℕ} (hn : 5 ≤ n) (F : Bits 4 → ℂ)
    (hF : ∑ v, F v = 0) :
    (∑ z : Bits n, if EZero z then F (sector4 z) else 0) = 0 := by
  classical
  let S := ∑ z : Bits n, if EZero z then F (sector4 z) else 0
  have hshift (v : Bits 4) :
      (∑ z : Bits n, if EZero z then F (sector4 z + v) else 0) = S := by
    calc
      _ = ∑ z : Bits n, if EZero (z + expandSector n v) then
          F (sector4 (z + expandSector n v)) else 0 := by
        simp only [ezero_add_iff _ _ (expandSector_ezero hn v), sector4_add,
          sector4_expand hn]
      _ = _ := Equiv.sum_comp (Equiv.addRight (expandSector n v))
        (fun z : Bits n => if EZero z then F (sector4 z) else 0)
  have hz (z : Bits n) :
      (∑ v : Bits 4, if EZero z then F (sector4 z + v) else 0) = 0 := by
    by_cases he : EZero z
    · simp only [if_pos he]
      calc
        _ = ∑ v : Bits 4, F v :=
          Fintype.sum_equiv (Equiv.addLeft (sector4 z)) _ _ (fun _ => rfl)
        _ = 0 := hF
    · simp [he]
  have havg : (16 : ℂ) * S = 0 := by
    calc
      _ = ∑ v : Bits 4, S := by simp [Fintype.card_fun]
      _ = ∑ v : Bits 4, ∑ z : Bits n, if EZero z then F (sector4 z + v) else 0 := by
        simp only [hshift]
      _ = ∑ z : Bits n, ∑ v : Bits 4, if EZero z then F (sector4 z + v) else 0 :=
        Finset.sum_comm
      _ = 0 := by simp only [hz, Finset.sum_const_zero]
  exact (mul_eq_zero.mp havg).resolve_left (by norm_num)

/-- 未归一化正扇区和；G 可取真实联合相位相关。 -/
def positiveSum {n : ℕ} (h a : Bits n) (G : Bits 5 → Bits 5 → ℂ) : ℂ :=
  ∑ z, character h z * (if EZero z then G (compress z) (compress (z + a)) else 0)

theorem positiveSum_zero_kernel {n : ℕ} (h a w : Bits n)
    (G : Bits 5 → Bits 5 → ℂ) (he : EZero w)
    (hc : compress w = 0) (hd : dot h w = 1) : positiveSum h a G = 0 := by
  unfold positiveSum
  apply weighted_character_zero h w _ hd
  intro z
  simp only [ezero_add_iff z w he]
  have ha : z + w + a = z + a + w := by abel
  simp only [ha, compress_add, hc, add_zero]

theorem positiveSum_zero_mixed {n : ℕ} (h a : Bits n)
    (G : Bits 5 → Bits 5 → ℂ) (i j : Fin n)
    (hi : 1 ≤ i.val) (hin : i.val < n - 2) (hip : i.val % 2 = 0)
    (hj : 1 ≤ j.val) (hjn : j.val < n - 2) (hjp : j.val % 2 = 0)
    (hhi : h i = 1) (hhj : h j = 0) : positiveSum h a G = 0 := by
  apply positiveSum_zero_kernel h a (unitBit n i.val + unitBit n j.val) G
  · apply ezero_add <;> apply ezero_unit
    · simp [InE, hip]
    · simp [InE, hjp]
  · rw [compress_add, compress_internal_even i hi hin hip,
      compress_internal_even j hj hjn hjp, bits_add_self]
  · rw [dot_add, dot_unitBit h i, dot_unitBit h j, hhi, hhj, add_zero]

theorem dot_on_sector {n : ℕ} (hn : 5 ≤ n) (h : Bits n) (H : Bits 4)
    (hh : ∀ i : Fin n, ¬ InE n i.val → h i = liftMask n (embedSector 0 H) i)
    (z : Bits n) (hz : EZero z) : dot h z = dot H (sector4 z) := by
  calc
    dot h z = dot (liftMask n (embedSector 0 H)) z := by
      unfold dot
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : InE n i.val
      · simp [hz i hi]
      · rw [hh i hi]
    _ = dot (embedSector 0 H) (compress z) := dot_liftMask hn _ z
    _ = dot H (sector4 z) := by
      rw [compress_of_ezero hz]
      simp [dot, embedSector, Fin.sum_univ_succ]

theorem embedSector_add (e f : Bit) (w v : Bits 4) :
    embedSector e w + embedSector f v = embedSector (e + f) (w + v) := by
  ext i; fin_cases i <;> simp [embedSector]

theorem positiveSum_zero_residual {n : ℕ} (hn : 5 ≤ n) (h a : Bits n) (A H : Bits 4)
    (G : Bits 5 → Bits 5 → ℂ)
    (ha : compress a = embedSector 1 A)
    (hh : ∀ i : Fin n, ¬ InE n i.val → h i = liftMask n (embedSector 0 H) i)
    (hfinite : (∑ w : Bits 4, character H w *
      G (embedSector 0 w) (embedSector 1 (w + A))) = 0) : positiveSum h a G = 0 := by
  unfold positiveSum
  have heq (z : Bits n) :
      character h z * (if EZero z then G (compress z) (compress (z + a)) else 0) =
      if EZero z then character H (sector4 z) *
        G (embedSector 0 (sector4 z)) (embedSector 1 (sector4 z + A)) else 0 := by
    by_cases hz : EZero z
    · simp only [if_pos hz, character, dot_on_sector hn h H hh z hz,
        compress_add, compress_of_ezero hz, ha, embedSector_add, zero_add]
    · simp [hz]
  simp_rw [heq]
  exact sum_sector4_zero hn _ hfinite

/-- 六个残留字符在 AND 扇区上的准确四位标签。 -/
theorem restricted_X_first {n : ℕ} (hn : 5 ≤ n) :
    ∀ i : Fin n, ¬ InE n i.val →
      adjacentMask n 1 i = liftMask n (embedSector 0 ![1,0,0,0]) i := by
  intro i hi
  have h1 : i.val ≠ 1 := by intro h; apply hi; simp [InE, h] <;> omega
  simp [adjacentMask, liftMask, embedSector, unitBit, blockMask, h1]

theorem restricted_X_last {n : ℕ} (hn : 8 ≤ n) (he : Even n) :
    ∀ i : Fin n, ¬ InE n i.val →
      adjacentMask n (n-2) i = liftMask n (embedSector 0 ![0,0,1,0]) i := by
  intro i hi
  have hnpar := Nat.even_iff.mp he
  have h1 : i.val ≠ n-2-1 := by
    intro h; apply hi; unfold InE; omega
  simp [adjacentMask, liftMask, embedSector, unitBit, blockMask, h1]

theorem restricted_Y_first {n : ℕ} (hn : 5 ≤ n) :
    ∀ i : Fin n, ¬ InE n i.val →
      internalYCharacter n 1 i = liftMask n (embedSector 0 ![1,1,1,1]) i := by
  intro i hi
  have hil := i.isLt
  have hp : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  unfold InE at hi
  simp only [internalYCharacter, liftMask, embedSector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, zero_smul, one_smul, add_zero, zero_add,
    Pi.add_apply, unitBit, blockMask, tailMask]
  split_ifs <;> simp_all <;> omega

theorem restricted_Y_third {n : ℕ} (hn : 8 ≤ n) :
    ∀ i : Fin n, ¬ InE n i.val →
      internalYCharacter n 3 i = liftMask n (embedSector 0 ![0,1,1,1]) i := by
  intro i hi
  have hil := i.isLt
  have hp : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  unfold InE at hi
  simp only [internalYCharacter, liftMask, embedSector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, zero_smul, one_smul, add_zero, zero_add,
    Pi.add_apply, unitBit, blockMask, tailMask]
  split_ifs <;> simp_all <;> omega

theorem restricted_Y_penultimate {n : ℕ} (hn : 8 ≤ n) (he : Even n) :
    ∀ i : Fin n, ¬ InE n i.val →
      internalYCharacter n (n-4) i = liftMask n (embedSector 0 ![0,0,1,1]) i := by
  intro i hi
  have hil := i.isLt
  have hnpar := Nat.even_iff.mp he
  unfold InE at hi
  simp only [internalYCharacter, liftMask, embedSector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, zero_smul, one_smul, add_zero, zero_add,
    Pi.add_apply, unitBit, blockMask, tailMask]
  split_ifs <;> simp_all <;> omega

theorem restricted_Y_last {n : ℕ} (hn : 8 ≤ n) (he : Even n) :
    ∀ i : Fin n, ¬ InE n i.val →
      internalYCharacter n (n-2) i = liftMask n (embedSector 0 ![0,0,0,1]) i := by
  intro i hi
  have hil := i.isLt
  have hnpar := Nat.even_iff.mp he
  unfold InE at hi
  simp only [internalYCharacter, liftMask, embedSector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, zero_smul, one_smul, add_zero, zero_add,
    Pi.add_apply, unitBit, blockMask, tailMask]
  split_ifs <;> simp_all <;> omega

/-- X 内部项除两端外，O 字符必为非空真子集。 -/
theorem positiveSum_X_mixed {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n - 1) (hj1 : j ≠ 1) (hjl : j ≠ n - 2)
    (G : Bits 5 → Bits 5 → ℂ) :
    positiveSum (adjacentMask n j) (adjacentMask n j) G = 0 := by
  have hnpar : n % 2 = 0 := Nat.even_iff.mp he
  by_cases hp : j % 2 = 0
  · have hjint : j < n - 2 := by omega
    by_cases hj2 : j = 2
    · subst j
      apply positiveSum_zero_mixed _ _ G (⟨2, by omega⟩ : Fin n) (⟨4, by omega⟩ : Fin n)
        (by simp) (by (try dsimp) <;> omega) (by simp) (by simp) (by (try dsimp) <;> omega) (by simp)
      · simp [adjacentMask, unitBit]
      · simp [adjacentMask, unitBit]
    · apply positiveSum_zero_mixed _ _ G (⟨j, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n)
        hj hjint hp (by simp) (by (try dsimp) <;> omega) (by simp)
      · simp [adjacentMask, unitBit, show j ≠ j - 1 by omega]
      · simp [adjacentMask, unitBit, show (2:ℕ) ≠ j - 1 by omega, Ne.symm hj2]
  · have hpp : (j - 1) % 2 = 0 := by omega
    have hpi : 1 ≤ j - 1 := by omega
    have hpn : j - 1 < n - 2 := by omega
    by_cases hj3 : j = 3
    · subst j
      apply positiveSum_zero_mixed _ _ G (⟨2, by omega⟩ : Fin n) (⟨4, by omega⟩ : Fin n)
        (by simp) (by (try dsimp) <;> omega) (by simp) (by simp) (by (try dsimp) <;> omega) (by simp)
      · simp [adjacentMask, unitBit]
      · simp [adjacentMask, unitBit]
    · apply positiveSum_zero_mixed _ _ G (⟨j - 1, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n)
        hpi hpn hpp (by simp) (by (try dsimp) <;> omega) (by simp)
      · simp [adjacentMask, unitBit, show j - 1 ≠ j by omega]
      · simp [adjacentMask, unitBit, show (2:ℕ) ≠ j - 1 by omega, show (2:ℕ) ≠ j by omega]

/-- Y 内部项除四个残留位置外，同样由两个 O 坐标配对。 -/
theorem positiveSum_Y_mixed {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n - 1)
    (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj4 : j ≠ n - 4) (hjl : j ≠ n - 2)
    (G : Bits 5 → Bits 5 → ℂ) :
    positiveSum (internalYCharacter n j) (internalYMask n j) G = 0 := by
  have hnpar : n % 2 = 0 := Nat.even_iff.mp he
  by_cases hp : j % 2 = 0
  · have hup : (j + 2) % 2 = 0 := by omega
    have hun : j + 2 < n - 2 := by omega
    apply positiveSum_zero_mixed _ _ G (⟨j + 2, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n)
      (by (try dsimp) <;> omega) hun hup (by simp) (by (try dsimp) <;> omega) (by simp)
    · simp [internalYCharacter, unitBit, tailMask, show j + 2 ≠ j - 1 by omega]
    · simp [internalYCharacter, unitBit, tailMask, show (2:ℕ) ≠ j - 1 by omega,
        show ¬ j + 1 ≤ 2 by omega]
  · have hpp : (j - 1) % 2 = 0 := by omega
    apply positiveSum_zero_mixed _ _ G (⟨j - 1, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n)
      (by (try dsimp) <;> omega) (by (try dsimp) <;> omega) hpp (by simp) (by (try dsimp) <;> omega) (by simp)
    · simp [internalYCharacter, unitBit, tailMask, show ¬ j + 1 ≤ j - 1 by omega]
    · simp [internalYCharacter, unitBit, tailMask, show (2:ℕ) ≠ j - 1 by omega,
        show ¬ j + 1 ≤ 2 by omega]

/-- 偶数维的邻位翻转，包含末端额外的 E 位。 -/
theorem compress_adjacent_even {n : ℕ} (hn : 5 ≤ n) (he : Even n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) :
    compress (adjacentMask n j) =
      if j = 1 then unitBit 5 0 + unitBit 5 1
      else if j = n - 2 then unitBit 5 1 + unitBit 5 3
      else unitBit 5 1 + unitBit 5 2 := by
  have hnp : n % 2 = 0 := Nat.even_iff.mp he
  unfold adjacentMask
  rw [compress_add]
  by_cases h1 : j = 1
  · subst j; simp [compress_first hn, compress_second hn]
  simp only [if_neg h1]
  by_cases h2 : j = n - 2
  · subst j
    rw [if_pos rfl, compress_penultimate hn]
    exact congrArg (fun v : Bits 5 => v + unitBit 5 3)
      (compress_internal_odd (⟨n-2-1,by omega⟩ : Fin n) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega))
  simp only [if_neg h2]
  by_cases hp : j % 2 = 0
  · rw [compress_internal_odd (⟨j-1,by omega⟩ : Fin n) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega),
      compress_internal_even (⟨j,by omega⟩ : Fin n) hj (by (try dsimp) <;> omega) hp]
  · rw [compress_internal_even (⟨j-1,by omega⟩ : Fin n) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega),
      compress_internal_odd (⟨j,by omega⟩ : Fin n) hj (by (try dsimp) <;> omega) (by (try dsimp) <;> omega), add_comm]

theorem not_ezero_adjacent {n : ℕ} (hn : 5 ≤ n) (he : Even n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) : ¬ EZero (adjacentMask n j) := by
  have hnp : n % 2 = 0 := Nat.even_iff.mp he
  intro hz
  by_cases hp : j % 2 = 0
  · have h := hz (⟨j-1,by omega⟩ : Fin n) (by unfold InE; simp only; omega)
    simpa [adjacentMask, unitBit, show j-1 ≠ j by omega] using h
  · have h := hz (⟨j,by omega⟩ : Fin n) (by unfold InE; simp only; omega)
    simpa [adjacentMask, unitBit, show j ≠ j-1 by omega] using h

theorem ezero_last {n : ℕ} (hn : 2 ≤ n) : EZero (unitBit n (n-1)) := by
  apply ezero_unit; unfold InE; omega

theorem not_ezero_internalY {n : ℕ} (hn : 5 ≤ n) (he : Even n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) : ¬ EZero (internalYMask n j) := by
  simpa only [internalYMask, ezero_add_iff _ _ (ezero_last (n:=n) (by omega))] using
    not_ezero_adjacent hn he j hj hjn

theorem qA_adjacent {n : ℕ} (hn : 5 ≤ n) (he : Even n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) : qA (adjacentMask n j) = 0 := by
  simp [qA, not_ezero_adjacent hn he j hj hjn]

theorem qA_internalY {n : ℕ} (hn : 5 ≤ n) (he : Even n) (j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n - 1) : qA (internalYMask n j) = 0 := by
  simp [qA, not_ezero_internalY hn he j hj hjn]

/-- 一次 E 非零翻转不可能把两个输入同时留在正扇区。 -/
theorem not_ezero_translated {n : ℕ} (a z : Bits n) (ha : ¬ EZero a)
    (hz : EZero z) : ¬ EZero (z + a) := by
  intro hza
  apply ha
  have h := ezero_add hz hza
  simpa [← add_assoc, bits_add_self] using h

def qPhasePair (u : ℂ) (v w : Bits 5) : ℂ :=
  u ^ (Q20 v).val * star (u ^ (Q20 w).val)

theorem decode4_1 : EvenCertificate.decode4 1 = ![0,0,0,1] := by decide
theorem decode4_2 : EvenCertificate.decode4 2 = ![0,0,1,0] := by decide
theorem decode4_3 : EvenCertificate.decode4 3 = ![0,0,1,1] := by decide
theorem decode4_5 : EvenCertificate.decode4 5 = ![0,1,0,1] := by decide
theorem decode4_7 : EvenCertificate.decode4 7 = ![0,1,1,1] := by decide
theorem decode4_8 : EvenCertificate.decode4 8 = ![1,0,0,0] := by decide
theorem decode4_9 : EvenCertificate.decode4 9 = ![1,0,0,1] := by decide
theorem decode4_15 : EvenCertificate.decode4 15 = ![1,1,1,1] := by decide

theorem positiveSum_X {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u : ℂ) (hu : u * star u = 1) :
    positiveSum (adjacentMask n j) (adjacentMask n j) (qPhasePair u) = 0 := by
  have hn5 : 5 ≤ n := by omega
  by_cases hj1 : j = 1
  · subst j
    apply positiveSum_zero_residual hn5 _ _ ![1,0,0,0] ![1,0,0,0]
    · rw [compress_adjacent_even hn5 he 1 (by (try dsimp) <;> omega) (by (try dsimp) <;> omega)]
      simp only [if_pos rfl, ite_true]
      decide
    · exact restricted_X_first hn5
    · simpa only [character, qPhasePair, embedSector, EvenCertificate.embedSector,
        decode4_1, decode4_2, decode4_3, decode4_5, decode4_7, decode4_8, decode4_9, decode4_15] using
        EvenCertificate.sector_phase_zero (a:=8) (h:=8) (by decide) u hu
  by_cases hjl : j = n-2
  · subst j
    apply positiveSum_zero_residual hn5 _ _ ![0,0,1,0] ![0,0,1,0]
    · rw [compress_adjacent_even hn5 he (n-2) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega)]
      simp only [if_neg (show n-2 ≠ 1 by omega), if_pos rfl]
      decide
    · exact restricted_X_last hn he
    · simpa only [character, qPhasePair, embedSector, EvenCertificate.embedSector,
        decode4_1, decode4_2, decode4_3, decode4_5, decode4_7, decode4_8, decode4_9, decode4_15] using
        EvenCertificate.sector_phase_zero (a:=2) (h:=2) (by decide) u hu
  exact positiveSum_X_mixed hn he j hj hjn hj1 hjl _

theorem positiveSum_Y {n : ℕ} (hn : 8 ≤ n) (he : Even n)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j < n-1) (u : ℂ) (hu : u * star u = 1) :
    positiveSum (internalYCharacter n j) (internalYMask n j) (qPhasePair u) = 0 := by
  have hn5 : 5 ≤ n := by omega
  by_cases hj1 : j = 1
  · subst j
    apply positiveSum_zero_residual hn5 _ _ ![1,0,0,1] ![1,1,1,1]
    · rw [internalYMask, compress_add, compress_adjacent_even hn5 he 1 (by (try dsimp) <;> omega) (by (try dsimp) <;> omega),
        compress_last hn5]
      simp only [if_pos rfl, ite_true]
      decide
    · exact restricted_Y_first hn5
    · simpa only [character, qPhasePair, embedSector, EvenCertificate.embedSector,
        decode4_1, decode4_2, decode4_3, decode4_5, decode4_7, decode4_8, decode4_9, decode4_15] using
        EvenCertificate.sector_phase_zero (a:=9) (h:=15) (by decide) u hu
  by_cases hj3 : j = 3
  · subst j
    apply positiveSum_zero_residual hn5 _ _ ![0,1,0,1] ![0,1,1,1]
    · rw [internalYMask, compress_add, compress_adjacent_even hn5 he 3 (by (try dsimp) <;> omega) (by (try dsimp) <;> omega),
        compress_last hn5]
      simp only [if_neg (show (3:ℕ) ≠ 1 by omega), if_neg (show (3:ℕ) ≠ n-2 by omega)]
      decide
    · exact restricted_Y_third hn
    · simpa only [character, qPhasePair, embedSector, EvenCertificate.embedSector,
        decode4_1, decode4_2, decode4_3, decode4_5, decode4_7, decode4_8, decode4_9, decode4_15] using
        EvenCertificate.sector_phase_zero (a:=5) (h:=7) (by decide) u hu
  by_cases hj4 : j = n-4
  · subst j
    apply positiveSum_zero_residual hn5 _ _ ![0,1,0,1] ![0,0,1,1]
    · rw [internalYMask, compress_add, compress_adjacent_even hn5 he (n-4) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega),
        compress_last hn5]
      simp only [if_neg (show n-4 ≠ 1 by omega), if_neg (show n-4 ≠ n-2 by omega)]
      decide
    · exact restricted_Y_penultimate hn he
    · simpa only [character, qPhasePair, embedSector, EvenCertificate.embedSector,
        decode4_1, decode4_2, decode4_3, decode4_5, decode4_7, decode4_8, decode4_9, decode4_15] using
        EvenCertificate.sector_phase_zero (a:=5) (h:=3) (by decide) u hu
  by_cases hjl : j = n-2
  · subst j
    apply positiveSum_zero_residual hn5 _ _ ![0,0,1,1] ![0,0,0,1]
    · rw [internalYMask, compress_add, compress_adjacent_even hn5 he (n-2) (by (try dsimp) <;> omega) (by (try dsimp) <;> omega),
        compress_last hn5]
      simp only [if_neg (show n-2 ≠ 1 by omega), if_pos rfl]
      decide
    · exact restricted_Y_last hn he
    · simpa only [character, qPhasePair, embedSector, EvenCertificate.embedSector,
        decode4_1, decode4_2, decode4_3, decode4_5, decode4_7, decode4_8, decode4_9, decode4_15] using
        EvenCertificate.sector_phase_zero (a:=3) (h:=1) (by decide) u hu
  exact positiveSum_Y_mixed hn he j hj hjn hj1 hj3 hj4 hjl _

end UnifiedEJM.EvenWalsh



