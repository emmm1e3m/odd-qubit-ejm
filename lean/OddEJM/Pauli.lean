import OddEJM.Core
import OddEJM.Chain
import OddEJM.Character
import OddEJM.Quantum
import Mathlib.Tactic

namespace OddEJM
namespace CircuitPauli
open scoped BigOperators
open Complex

theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  exact (show ∀ b : Bit, b = 0 ∨ b = 1 by decide) b

theorem sign_add (a b : Bit) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp only [zero_add, add_zero, CharTwo.add_self_eq_zero, bitSign] <;> norm_num

theorem dot_add_right {n : ℕ} (b x y : Bits n) :
    dot b (x + y) = dot b x + dot b y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_add_left {n : ℕ} (b c x : Bits n) :
    dot (b + c) x = dot b x + dot c x := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem char_add {n : ℕ} (b x y : Bits n) :
    character b (x + y) = character b x * character b y := by
  simp only [character, dot_add_right, sign_add]

theorem coord_add {n : ℕ} (x y : Bits n) (j : ℕ) :
    coord (x + y) j = coord x j + coord y j := by
  by_cases h : j < n <;> simp [coord, h]

theorem difference_add {n : ℕ} (x y : Bits n) :
    difference (x + y) = difference x + difference y := by
  funext j
  simp only [difference, Pi.add_apply, coord_add]
  ring

theorem dot_unit_right {n : ℕ} (z : Bits n) (j : ℕ) :
    dot z (unitBit n j) = coord z j := by
  by_cases h : j < n
  · have heq : ∀ i : Fin n, i.val = j ↔ i = ⟨j, h⟩ := by
      intro i
      constructor
      · intro hi
        apply Fin.ext
        exact hi
      · intro hi; exact congrArg Fin.val hi
    simp [dot, unitBit, coord, h, heq]
  · have hne : ∀ i : Fin n, i.val ≠ j := by intro i heq; omega
    simp [dot, unitBit, coord, h, hne]

theorem dot_unit_left {n : ℕ} (z : Bits n) (j : ℕ) :
    dot (unitBit n j) z = coord z j := by
  simpa only [dot, mul_comm] using dot_unit_right z j

theorem setBit_add_unit {n : ℕ} (z : Bits n) (j : ℕ) (v : Bit) :
    setBit z j v = z + fun k => unitBit n j k * (coord z j + v) := by
  funext k
  by_cases h : k.val = j
  · have hj : j < n := by omega
    have hk : k = ⟨j, hj⟩ := Fin.ext h
    subst k
    simp [setBit, unitBit, coord, hj, CharTwo.add_self_eq_zero, ← add_assoc]
  · simp [setBit, unitBit, h]

theorem dot_setBit_right {n : ℕ} (b z : Bits n) (j : ℕ) (v : Bit) :
    dot b (setBit z j v) = dot b z + coord b j * (coord z j + v) := by
  rw [setBit_add_unit, dot_add_right]
  congr 1
  rw [← dot_unit_right b j]
  simp only [dot, Finset.sum_mul, mul_assoc]

theorem char_setBit {n : ℕ} (b z : Bits n) (j : ℕ) (v : Bit) :
    character b (setBit z j v) =
      character b z * bitSign (coord b j * (coord z j + v)) := by
  simp only [character, dot_setBit_right, sign_add]

theorem coord_setBit {n : ℕ} (z : Bits n) (j : ℕ) (v : Bit) (hj : j < n) :
    coord (setBit z j v) j = v := by simp [coord, setBit, hj]

theorem setBit_twice {n : ℕ} (z : Bits n) (j : ℕ) (u v : Bit) :
    setBit (setBit z j u) j v = setBit z j v := by
  funext k
  simp only [setBit]
  split <;> rfl

theorem setBit_add {n : ℕ} (x y : Bits n) (j : ℕ) (u v : Bit) :
    setBit x j u + setBit y j v = setBit (x + y) j (u + v) := by
  funext k
  simp only [setBit, Pi.add_apply]
  split <;> rfl

theorem setBit_add_right {n : ℕ} (x y : Bits n) (j : ℕ) (u : Bit) :
    setBit x j u + y = setBit (x + y) j (u + coord y j) := by
  funext k
  by_cases h : k.val = j
  · have hj : j < n := by omega
    have hk : k = ⟨j, hj⟩ := Fin.ext h
    subst k
    simp [setBit, coord, hj]
  · simp [setBit, h]

theorem dot_setBit_left {n : ℕ} (b z : Bits n) (j : ℕ) (v : Bit) :
    dot (setBit b j v) z = dot b z + (coord b j + v) * coord z j := by
  simpa only [dot, mul_comm] using dot_setBit_right z b j v

theorem char_setBit_both {n : ℕ} (b z : Bits n) (j : ℕ) (v u : Bit)
    (hj : j < n) :
    character (setBit b j v) (setBit z j u) =
      character b z * bitSign (coord b j * coord z j + v * u) := by
  unfold character
  rw [dot_setBit_right, dot_setBit_left, coord_setBit _ _ _ hj]
  have heq : dot b z + (coord b j + v) * coord z j + v * (coord z j + u) =
      dot b z + (coord b j * coord z j + v * u) := by
    have hv : v * coord z j + v * coord z j = 0 := CharTwo.add_self_eq_zero _
    linear_combination hv
  rw [heq, sign_add]

/-- 在实际振幅定义上，Hadamard交换所在位的X、Z掩码。 -/
theorem hadamard_pauli {n : ℕ} (j : ℕ) (hj : j < n)
    (a b : Bits n) (c : ℂ) (ψ : Vec n) :
    pauliAction a b c (hadamardAt j ψ) =
      hadamardAt j (pauliAction (setBit a j (coord b j))
        (setBit b j (coord a j)) (c * bitSign (coord a j * coord b j)) ψ) := by
  funext z
  simp only [pauliAction, hadamardAt]
  rw [setBit_add, setBit_add, char_setBit_both _ _ _ _ _ hj,
    char_setBit_both _ _ _ _ _ hj, coord_add]
  rcases bit_cases (coord a j) with ha | ha <;>
    rcases bit_cases (coord b j) with hb | hb <;>
    rcases bit_cases (coord z j) with hz | hz <;>
    simp [ha, hb, hz, coord_add, bitSign, show (1 : Bit) + 1 = 0 by decide] <;> ring

def tailMask (n j : ℕ) : Bits n := fun k => if j ≤ k.val then 1 else 0

theorem dot_tail {n : ℕ} (z : Bits n) (j : ℕ) (hj : j < n) :
    dot (tailMask n j) z = suffix z ⟨j, hj⟩ := by
  simp [dot, tailMask, suffix, Fin.le_def]

theorem tail_pullback {n : ℕ} (z : Bits n) (j : ℕ) (hj : j < n) :
    character (unitBit n j) z = character (tailMask n j) (difference z) := by
  simp only [character, dot_unit_left, dot_tail _ _ hj, suffix_difference]
  simp [coord, hj]

/-- 直接由实际振幅重排得到CNOT链的Pauli交织。 -/
theorem chain_pauli {n : ℕ} (a b B : Bits n) (c : ℂ) (ψ : Vec n)
    (hB : ∀ z, character b z = character B (difference z)) :
    pauliAction a b c (chain ψ) = chain (pauliAction (difference a) B c ψ) := by
  funext z
  simp only [pauliAction, chain, hB, difference_add]

theorem circuit_pauli {n : ℕ} (hn : 0 < n)
    (a b B : Bits n) (c : ℂ) (ψ : Vec n)
    (hB : ∀ z, character b z = character B (difference z)) :
    pauliAction a b c (circuit ψ) = circuit
      (pauliAction (setBit (difference a) (n - 1) (coord B (n - 1)))
        (setBit B (n - 1) (coord (difference a) (n - 1)))
        (c * bitSign (coord (difference a) (n - 1) * coord B (n - 1))) ψ) := by
  unfold circuit
  rw [chain_pauli a b B c _ hB, hadamard_pauli (n - 1) (by omega)]

theorem localX_pullback {n : ℕ} (hn : 0 < n) (j : ℕ) (ψ : Vec n) :
    pauliAction (unitBit n j) 0 1 (circuit ψ) = circuit
      (pauliAction (setBit (difference (unitBit n j)) (n - 1) 0)
        (setBit 0 (n - 1) (coord (difference (unitBit n j)) (n - 1))) 1 ψ) := by
  simpa [coord, bitSign] using circuit_pauli hn (unitBit n j) 0 0 1 ψ
    (by intro z; simp [character, dot, bitSign])

theorem localZ_pullback {n : ℕ} (hn : 0 < n) (j : ℕ) (hj : j < n) (ψ : Vec n) :
    pauliAction 0 (unitBit n j) 1 (circuit ψ) = circuit
      (pauliAction (setBit 0 (n - 1) 1) (setBit (tailMask n j) (n - 1) 0) 1 ψ) := by
  have ht : coord (tailMask n j) (n - 1) = 1 := by
    simp [coord, tailMask, show n - 1 < n by omega, show j ≤ n - 1 by omega]
  have hd : difference (0 : Bits n) = 0 := by ext k; simp [difference, coord]
  have hz : coord (0 : Bits n) (n - 1) = 0 := by simp [coord]
  simpa only [hd, hz, ht, zero_mul, bitSign, ite_true, mul_one] using
    circuit_pauli hn 0 (unitBit n j) (tailMask n j) 1 ψ
      (fun z => tail_pullback z j hj)

theorem localY_pullback {n : ℕ} (hn : 0 < n) (j : ℕ) (hj : j < n) (ψ : Vec n) :
    pauliAction (unitBit n j) (unitBit n j) I (circuit ψ) = circuit
      (pauliAction (setBit (difference (unitBit n j)) (n - 1) 1)
        (setBit (tailMask n j) (n - 1) (coord (difference (unitBit n j)) (n - 1)))
        (I * bitSign (coord (difference (unitBit n j)) (n - 1))) ψ) := by
  have ht : coord (tailMask n j) (n - 1) = 1 := by
    simp [coord, tailMask, show n - 1 < n by omega, show j ≤ n - 1 by omega]
  simpa only [ht, mul_one] using
    circuit_pauli hn (unitBit n j) (unitBit n j) (tailMask n j) I ψ
      (fun z => tail_pullback z j hj)

theorem coord_unit {n : ℕ} (j k : ℕ) (hj : j < n) :
    coord (unitBit n j) k = if k = j then 1 else 0 := by
  by_cases hk : k < n
  · simp [coord, unitBit, hk]
  · have hne : k ≠ j := by omega
    simp [coord, hk, hne]

theorem difference_unit {n : ℕ} (j : ℕ) (hj : j < n) :
    difference (unitBit n j) = unitBit n j + if j = 0 then 0 else unitBit n (j - 1) := by
  funext k
  change (if k.val = j then 1 else 0) + coord (unitBit n j) (k.val + 1) = _
  rw [coord_unit _ _ hj]
  by_cases h0 : j = 0
  · subst j
    simp [unitBit, show k.val + 1 ≠ 0 by omega]
  · rw [if_neg h0]
    change (if k.val = j then (1 : Bit) else 0) + (if k.val + 1 = j then 1 else 0) =
      (if k.val = j then 1 else 0) + (if k.val = j - 1 then 1 else 0)
    have heq : k.val + 1 = j ↔ k.val = j - 1 := by omega
    simp [heq]

theorem setBit_eq_self {n : ℕ} (z : Bits n) (j : ℕ) (v : Bit)
    (hz : coord z j = v) : setBit z j v = z := by
  funext k
  by_cases h : k.val = j
  · have hj : j < n := by omega
    have hk : k = ⟨j, hj⟩ := Fin.ext h
    subst k
    simpa [setBit, coord, hj] using hz.symm
  · simp [setBit, h]

theorem setBit_zero_one (n j : ℕ) : setBit (0 : Bits n) j 1 = unitBit n j := by
  funext k
  simp [setBit, unitBit]

theorem setBit_zero_zero (n j : ℕ) : setBit (0 : Bits n) j 0 = 0 := by
  funext k
  simp [setBit]

theorem difference_last_coord {n : ℕ} (hn : 0 < n) (j : ℕ) (hj : j < n) :
    coord (difference (unitBit n j)) (n - 1) = if n - 1 = j then 1 else 0 := by
  simp [coord, difference, unitBit, show n - 1 < n by omega,
    show ¬ n - 1 + 1 < n by omega]

theorem localX_beforeLast {n : ℕ} (j : ℕ) (hj : j < n - 1) (ψ : Vec n) :
    pauliAction (unitBit n j) 0 1 (circuit ψ) = circuit
      (pauliAction (unitBit n j + if j = 0 then 0 else unitBit n (j - 1)) 0 1 ψ) := by
  have hn : 0 < n := by omega
  have hc : coord (difference (unitBit n j)) (n - 1) = 0 := by
    rw [difference_last_coord hn j (by omega), if_neg (by omega)]
  rw [localX_pullback hn, setBit_eq_self _ _ _ hc, hc, setBit_zero_zero,
    difference_unit _ (by omega)]

theorem localZ_table {n : ℕ} (hn : 0 < n) (j : ℕ) (hj : j < n) (ψ : Vec n) :
    pauliAction 0 (unitBit n j) 1 (circuit ψ) = circuit
      (pauliAction (unitBit n (n - 1)) (setBit (tailMask n j) (n - 1) 0) 1 ψ) := by
  rw [localZ_pullback hn j hj, setBit_zero_one]

theorem localY_beforeLast {n : ℕ} (j : ℕ) (hj : j < n - 1) (ψ : Vec n) :
    pauliAction (unitBit n j) (unitBit n j) I (circuit ψ) = circuit
      (pauliAction ((unitBit n j + if j = 0 then 0 else unitBit n (j - 1)) +
        unitBit n (n - 1)) (setBit (tailMask n j) (n - 1) 0) I ψ) := by
  have hn : 0 < n := by omega
  have hc : coord (difference (unitBit n j)) (n - 1) = 0 := by
    rw [difference_last_coord hn j (by omega), if_neg (by omega)]
  rw [localY_pullback hn j (by omega), hc]
  have hs : setBit (difference (unitBit n j)) (n - 1) 1 =
      difference (unitBit n j) + unitBit n (n - 1) := by
    rw [setBit_add_unit]
    simp [hc]
  rw [hs, difference_unit _ (by omega)]
  simp [bitSign]

theorem tail_last {n : ℕ} (hn : 0 < n) : tailMask n (n - 1) = unitBit n (n - 1) := by
  funext k
  have heq : n - 1 ≤ k.val ↔ k.val = n - 1 := by omega
  simp [tailMask, unitBit, heq]

theorem localX_last {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n) :
    pauliAction (unitBit n (n - 1)) 0 1 (circuit ψ) = circuit
      (pauliAction (unitBit n (n - 2)) (unitBit n (n - 1)) 1 ψ) := by
  have hp : n - 1 - 1 = n - 2 := by omega
  have hd : difference (unitBit n (n - 1)) =
      unitBit n (n - 1) + unitBit n (n - 2) := by
    rw [difference_unit _ (by omega), if_neg (by omega), hp]
  have hs : setBit (difference (unitBit n (n - 1))) (n - 1) 0 =
      unitBit n (n - 2) := by
    rw [hd]
    funext k
    by_cases hk : k.val = n - 1
    · simp [setBit, hk, unitBit, show n - 1 ≠ n - 2 by omega]
    · simp [setBit, hk, unitBit]
  rw [localX_pullback (by omega), hs, difference_last_coord (by omega) _ (by omega),
    if_pos rfl, setBit_zero_one]

theorem localY_last {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n) :
    pauliAction (unitBit n (n - 1)) (unitBit n (n - 1)) I (circuit ψ) = circuit
      (pauliAction (unitBit n (n - 1) + unitBit n (n - 2))
        (unitBit n (n - 1)) (-I) ψ) := by
  have hc : coord (difference (unitBit n (n - 1))) (n - 1) = 1 := by
    rw [difference_last_coord (by omega) _ (by omega), if_pos rfl]
  have hu : coord (unitBit n (n - 1)) (n - 1) = 1 := by
    rw [coord_unit _ _ (by omega), if_pos rfl]
  rw [localY_pullback (by omega) _ (by omega), hc,
    setBit_eq_self _ _ _ hc, tail_last (by omega), setBit_eq_self _ _ _ hu,
    difference_unit _ (by omega), if_neg (by omega)]
  simp [show n - 1 - 1 = n - 2 by omega, bitSign]

theorem cut_tail {n : ℕ} (j : ℕ) :
    setBit (tailMask n j) (n - 1) 0 =
      fun k => if j ≤ k.val ∧ k.val < n - 1 then 1 else 0 := by
  funext k
  by_cases hk : k.val = n - 1
  · simp [setBit, hk]
  · have hlt : k.val < n - 1 := by omega
    simp [setBit, tailMask, hk, hlt]

/-- 每个输入边标签作用在其相邻的两个物理Z上。 -/
def edgeMask {n : ℕ} (e : Bits n) : Bits n :=
  fun k => ∑ j : Fin n, e j * (unitBit n j.val k + unitBit n (j.val + 1) k)

theorem dot_edgeMask {n : ℕ} (e z : Bits n) :
    dot (edgeMask e) z = dot e (difference z) := by
  unfold dot edgeMask
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ k : Fin n, e j * (unitBit n j.val k + unitBit n (j.val + 1) k) * z k) =
        e j * (dot (unitBit n j.val) z + dot (unitBit n (j.val + 1)) z) := by
      simp [dot, Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc]
    _ = e j * difference z j := by
      rw [dot_unit_left, dot_unit_left]
      simp [coord, j.isLt, difference]

def orbitX {n : ℕ} (label : Bits n) : Bits n := fun _ => coord label (n - 1)

def orbitZ {n : ℕ} (label : Bits n) : Bits n :=
  edgeMask (setBit label (n - 1) 0)

theorem difference_const {n : ℕ} (hn : 0 < n) (s : Bit) :
    difference (fun _ : Fin n => s) = fun k => if k.val = n - 1 then s else 0 := by
  funext k
  by_cases hk : k.val = n - 1
  · simp [difference, coord, hk, show ¬ n - 1 + 1 < n by omega]
  · have hnext : k.val + 1 < n := by omega
    simp [difference, coord, hk, hnext, CharTwo.add_self_eq_zero]

theorem orbit_pullback {n : ℕ} (hn : 0 < n) (label : Bits n) (ψ : Vec n) :
    pauliAction (orbitX label) (orbitZ label) 1 (circuit ψ) =
      circuit (pauliAction 0 label 1 ψ) := by
  let e := setBit label (n - 1) 0
  have hchar : ∀ z, character (orbitZ label) z = character e (difference z) := by
    intro z
    exact congrArg bitSign (dot_edgeMask e z)
  have he : coord e (n - 1) = 0 := coord_setBit _ _ _ (by omega)
  have hd : difference (orbitX label) =
      fun k => if k.val = n - 1 then coord label (n - 1) else 0 :=
    difference_const hn _
  have hc : coord (difference (orbitX label)) (n - 1) = coord label (n - 1) := by
    rw [hd]
    simp [coord, show n - 1 < n by omega]
  have hA : setBit (difference (orbitX label)) (n - 1) 0 = 0 := by
    rw [hd]
    funext k
    by_cases hk : k.val = n - 1 <;> simp [setBit, hk]
  have hB : setBit e (n - 1) (coord label (n - 1)) = label := by
    rw [show e = setBit label (n - 1) 0 from rfl, setBit_twice]
    exact setBit_eq_self _ _ _ rfl
  simpa only [he, hc, hA, hB, mul_zero, bitSign, ite_true, mul_one] using
    circuit_pauli hn (orbitX label) (orbitZ label) e 1 ψ hchar

/-- 字符输入列与边ZZ、全X产生的实际Pauli轨道逐振幅相同。 -/
theorem measurement_orbit {n : ℕ} (hn : 0 < n) (t : ℝ) (label : Bits n) :
    measurement n t label = pauliAction (orbitX label) (orbitZ label) 1 (seed n t) := by
  rw [seed, orbit_pullback hn]
  unfold measurement
  congr 1
  funext z
  simp [pauliAction, mul_comm]

theorem edgeMask_unit {n : ℕ} (j : ℕ) (hj : j < n) :
    edgeMask (unitBit n j) = unitBit n j + unitBit n (j + 1) := by
  funext k
  have heq : ∀ i : Fin n, i.val = j ↔ i = ⟨j, hj⟩ := by
    intro i
    constructor
    · intro hi; apply Fin.ext; exact hi
    · intro hi; exact congrArg Fin.val hi
  simp [edgeMask, unitBit, heq]

theorem adjacentZZ_pullback {n : ℕ} (j : ℕ) (hj : j < n - 1) (ψ : Vec n) :
    pauliAction 0 (unitBit n j + unitBit n (j + 1)) 1 (circuit ψ) =
      circuit (pauliAction 0 (unitBit n j) 1 ψ) := by
  have hc : coord (unitBit n j) (n - 1) = 0 := by
    rw [coord_unit _ _ (by omega), if_neg (by omega)]
  have hX : orbitX (unitBit n j) = 0 := by funext k; exact hc
  have hZ : orbitZ (unitBit n j) = unitBit n j + unitBit n (j + 1) := by
    unfold orbitZ
    rw [setBit_eq_self _ _ _ hc, edgeMask_unit _ (by omega)]
  simpa only [hX, hZ] using orbit_pullback (by omega) (unitBit n j) ψ

theorem allX_pullback {n : ℕ} (hn : 0 < n) (ψ : Vec n) :
    pauliAction (fun _ : Fin n => 1) 0 1 (circuit ψ) =
      circuit (pauliAction 0 (unitBit n (n - 1)) 1 ψ) := by
  have hc : coord (unitBit n (n - 1)) (n - 1) = 1 := by
    rw [coord_unit _ _ (by omega), if_pos rfl]
  have hX : orbitX (unitBit n (n - 1)) = fun _ : Fin n => 1 := by funext k; exact hc
  have he : setBit (unitBit n (n - 1)) (n - 1) 0 = 0 := by
    funext k
    by_cases hk : k.val = n - 1 <;> simp [setBit, unitBit, hk]
  have hZ : orbitZ (unitBit n (n - 1)) = 0 := by
    unfold orbitZ
    rw [he]
    funext k
    simp [edgeMask]
  simpa only [hX, hZ] using orbit_pullback hn (unitBit n (n - 1)) ψ

/-- Core的显式期望与振幅内积完全相同。 -/
theorem inner_pauliExpectation {n : ℕ} (ψ : Vec n) (a b : Bits n) (c : ℂ) :
    inner ψ (pauliAction a b c ψ) = pauliExpectation ψ a b c := by
  have hsum := Equiv.sum_comp (Equiv.addRight a)
    (fun z => star (ψ z) * (c * character b (z + a) * ψ (z + a)))
  have haa : a + a = 0 := bits_add_self a
  simpa [inner, pauliAction, pauliExpectation, add_assoc, haa, mul_assoc] using hsum.symm

/-- 任意已证明的算符交织均可输运为真实Pauli期望恒等式。 -/
theorem circuit_expectation {n : ℕ} (hn : 0 < n)
    (ψ : Vec n) (a b A B : Bits n) (c C : ℂ)
    (h : pauliAction a b c (circuit ψ) = circuit (pauliAction A B C ψ)) :
    pauliExpectation (circuit ψ) a b c = pauliExpectation ψ A B C := by
  rw [← inner_pauliExpectation, h, circuit_inner hn, inner_pauliExpectation]

theorem pauli_inner {n : ℕ} (a b : Bits n) (ψ φ : Vec n) :
    inner (pauliAction a b 1 ψ) (pauliAction a b 1 φ) = inner ψ φ := by
  unfold inner
  calc
    _ = ∑ z, star (ψ (z + a)) * φ (z + a) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [pauliAction, one_mul, star_mul, character_star]
      calc
        star (ψ (z + a)) * character b (z + a) * (character b (z + a) * φ (z + a)) =
            (character b (z + a) * character b (z + a)) *
              (star (ψ (z + a)) * φ (z + a)) := by ring
        _ = _ := by rw [character_mul_self]; simp
    _ = ∑ z, star (ψ z) * φ z := by
      simpa using Equiv.sum_comp (Equiv.addRight a) (fun z => star (ψ z) * φ z)

theorem pauli_commute {n : ℕ} (a b p q : Bits n) (d : ℂ) (ψ : Vec n) :
    pauliAction p q d (pauliAction a b 1 ψ) =
      fun z => (character q a * character b p) *
        pauliAction a b 1 (pauliAction p q d ψ) z := by
  funext z
  have hshift : z + p + a = z + a + p := by abel
  simp only [pauliAction, one_mul, char_add, hshift]
  have hqa := character_mul_self q a
  linear_combination -(d * character q z * character q p * character b z *
    character b p * character b a * ψ (z + a + p)) * hqa

theorem inner_scale_right {n : ℕ} (ψ φ : Vec n) (c : ℂ) :
    inner ψ (fun z => c * φ z) = c * inner ψ φ := by
  unfold inner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem pauli_conjugation_expectation {n : ℕ} (a b p q : Bits n) (d : ℂ) (ψ : Vec n) :
    pauliExpectation (pauliAction a b 1 ψ) p q d =
      (character q a * character b p) * pauliExpectation ψ p q d := by
  rw [← inner_pauliExpectation, pauli_commute]
  rw [inner_scale_right, pauli_inner, inner_pauliExpectation]

theorem coord_edgeMask {n : ℕ} (e : Bits n) (j : ℕ) (hj : j < n) :
    coord (edgeMask e) j = coord e j + if j = 0 then 0 else coord e (j - 1) := by
  rw [← dot_unit_right, dot_edgeMask, difference_unit j hj, dot_add_right]
  have hz : dot e 0 = 0 := by simp [dot]
  by_cases h0 : j = 0 <;> simp only [h0, ite_true, ite_false, dot_unit_right, hz]

/-- 首尾不存在的边由setBit和条件分支补零。 -/
def localParity {n : ℕ} (label : Bits n) (j : ℕ) : Bit :=
  coord (setBit label (n - 1) 0) j +
    if j = 0 then 0 else coord (setBit label (n - 1) 0) (j - 1)

theorem orbitZ_coord {n : ℕ} (label : Bits n) (j : ℕ) (hj : j < n) :
    coord (orbitZ label) j = localParity label j := coord_edgeMask _ _ hj

theorem orbitX_coord {n : ℕ} (label : Bits n) (j : ℕ) (hj : j < n) :
    coord (orbitX label) j = coord label (n - 1) := by simp [coord, orbitX, hj]

theorem measurement_localX_sign {n : ℕ} (hn : 0 < n) (t : ℝ)
    (label : Bits n) (j : ℕ) (hj : j < n) :
    pauliExpectation (measurement n t label) (unitBit n j) 0 1 =
      bitSign (localParity label j) * pauliExpectation (seed n t) (unitBit n j) 0 1 := by
  rw [measurement_orbit hn, pauli_conjugation_expectation]
  have hz : dot (0 : Bits n) (orbitX label) = 0 := by simp [dot]
  simp only [character, dot_unit_right, orbitZ_coord _ _ hj, hz, bitSign_zero, one_mul]

theorem measurement_localZ_sign {n : ℕ} (hn : 0 < n) (t : ℝ)
    (label : Bits n) (j : ℕ) (hj : j < n) :
    pauliExpectation (measurement n t label) 0 (unitBit n j) 1 =
      bitSign (coord label (n - 1)) * pauliExpectation (seed n t) 0 (unitBit n j) 1 := by
  rw [measurement_orbit hn, pauli_conjugation_expectation]
  have hz : dot (orbitZ label) 0 = 0 := by simp [dot]
  simp only [character, dot_unit_left, orbitX_coord _ _ hj, hz, bitSign_zero, mul_one]

theorem measurement_localY_sign {n : ℕ} (hn : 0 < n) (t : ℝ)
    (label : Bits n) (j : ℕ) (hj : j < n) :
    pauliExpectation (measurement n t label) (unitBit n j) (unitBit n j) I =
      bitSign (coord label (n - 1) + localParity label j) *
        pauliExpectation (seed n t) (unitBit n j) (unitBit n j) I := by
  rw [measurement_orbit hn, pauli_conjugation_expectation]
  simp only [character, dot_unit_left, dot_unit_right, orbitZ_coord _ _ hj,
    orbitX_coord _ _ hj, sign_add]

theorem bitSign_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Bit) :
    bitSign (∑ i ∈ s, f i) = ∏ i ∈ s, bitSign (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, sign_add, ih]

theorem character_edge_product {n : ℕ} (e z : Bits n) :
    character (edgeMask e) z =
      ∏ j : Fin n, bitSign (e j * (z j + coord z (j.val + 1))) := by
  rw [character, dot_edgeMask]
  exact bitSign_sum Finset.univ (fun j => e j * difference z j)

theorem orbit_character_self {n : ℕ} (hn : 0 < n) (label : Bits n) :
    character (orbitZ label) (orbitX label) = 1 := by
  let e := setBit label (n - 1) 0
  have he : coord e (n - 1) = 0 := coord_setBit _ _ _ (by omega)
  have hd : difference (orbitX label) =
      fun k => if k.val = n - 1 then coord label (n - 1) else 0 :=
    difference_const hn _
  have hm : dot e (difference (orbitX label)) =
      dot e (unitBit n (n - 1)) * coord label (n - 1) := by
    rw [hd]
    unfold dot
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val = n - 1 <;> simp [unitBit, hk]
  change bitSign (dot (edgeMask e) (orbitX label)) = 1
  rw [dot_edgeMask, hm, dot_unit_right, he]
  simp

/-- 原生成元乘积的逐振幅形式：边ZZ符号乘积，随后全X平移。 -/
theorem measurement_generator_product {n : ℕ} (hn : 0 < n) (t : ℝ)
    (label z : Bits n) :
    measurement n t label z =
      (∏ j : Fin n, bitSign ((setBit label (n - 1) 0) j *
        (z j + coord z (j.val + 1)))) * seed n t (z + orbitX label) := by
  rw [measurement_orbit hn]
  simp only [pauliAction, one_mul, char_add, orbit_character_self hn, mul_one]
  rw [show character (orbitZ label) z = _ from character_edge_product _ z]

end CircuitPauli
end OddEJM
