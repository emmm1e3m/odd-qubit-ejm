import UnifiedEJM.PhysicsCircuit
import UnifiedEJM.Background
import UnifiedEJM.Features
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open OddEJM Complex

namespace UnifiedEJM.GraphBackground

/-- 归一化四位 Fourier 系数。 -/
def fourier (f : Bits 4 → ℂ) (h : Bits 4) : ℂ :=
  (1 / 16 : ℂ) * ∑ x, f x * character h x

theorem fourier_inversion (f : Bits 4 → ℂ) (x : Bits 4) :
    (∑ h, fourier f h * character h x) = f x := by
  simp only [fourier, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (y : Bits 4) :
      (∑ h, 1 / 16 * (f y * character h y) * character h x) =
        (f y / 16) * (if y = x then (2:ℂ)^4 else 0) := by
    rw [← character_orthogonality y x]
    simp only [character_star, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [PhysicsCircuit.character_symm h y, PhysicsCircuit.character_symm h x]
    ring
  simp_rw [he]
  simp
  ring

/-- 四特征逻辑字的物理提升；定义本身保留所有实际物理位。 -/
def featureMask (n : ℕ) (h : Bits 4) : Bits n :=
  fun j => dot h (features (unitBit n j.val))

theorem features_basis {n : ℕ} (z : Bits n) :
    features z = ∑ j : Fin n, z j • features (unitBit n j.val) := by
  have hz : z = ∑ j : Fin n, z j • unitBit n j.val := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitBit]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      have hjk : k.val ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [hjk]
    · simp
  have hsmul (b : Bit) (v : Bits n) : features (b • v) = b • features v := by
    rcases OddEJM.bit_cases b with rfl | rfl
    · simp only [zero_smul]
      exact (featuresHom n).map_zero
    · simp
  calc
    features z = (featuresHom n) (∑ j : Fin n, z j • unitBit n j.val) :=
      congrArg features hz
    _ = ∑ j, features (z j • unitBit n j.val) := map_sum _ _ _
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro j _
  exact hsmul _ _

/-- 每一逻辑字符精确等于提升后物理字符。 -/
theorem character_featureMask {n : ℕ} (h : Bits 4) (z : Bits n) :
    character (featureMask n h) z = character h (features z) := by
  rw [features_basis]
  simp only [character, dot, featureMask, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- 真实输入的 Y 基字符列。 -/
def yColumn {n : ℕ} (w : Bits n) : Vec n :=
  fun z => normFactor n * I ^ weight z * character w z

/-- 归一化物理背景；包含论文选择的整体 -i。 -/
def physicalBackground (n : ℕ) (u : ℂ) : Vec n :=
  fun y => -I * circuit (fun z : Bits n => normFactor n * background u z) y

/-- 原始背景在至多十六个真实 Y 基列上的精确展开。 -/
theorem background_fourier {n : ℕ} (u : ℂ) (z : Bits n) :
    normFactor n * background u z =
      ∑ h : Bits 4, fourier (fun x => u ^ (F x).val) h * yColumn (featureMask n h) z := by
  simp only [yColumn, character_featureMask]
  calc
    _ = normFactor n * I ^ weight z *
        (∑ h, fourier (fun x => u ^ (F x).val) h * character h (features z)) := by
      rw [fourier_inversion]
      simp [background, q_eq_features, mul_assoc]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring

theorem circuit_finite_linear {α : Type*} [Fintype α] {n : ℕ}
    (c : α → ℂ) (v : α → Vec n) (y : Bits n) :
    circuit (fun z => ∑ a, c a * v a z) y = ∑ a, c a * circuit (v a) y := by
  simp only [circuit, chain, hadamardAt, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- 展开与原始 H/CNOT 电路逐振幅交换，无图态语义假设。 -/
theorem physicalBackground_fourier (n : ℕ) (u : ℂ) (y : Bits n) :
    physicalBackground n u y = -I * ∑ h : Bits 4,
      fourier (fun x => u ^ (F x).val) h * circuit (yColumn (featureMask n h)) y := by
  unfold physicalBackground
  simp_rw [background_fourier]
  rw [circuit_finite_linear]

theorem weight_setBit {n : ℕ} (z : Bits n) (j : Fin n) (b : Bit) :
    weight (setBit z j.val b) = b.val + ∑ k ∈ Finset.univ.erase j, (z k).val := by
  unfold weight
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  simp only [setBit, if_pos rfl]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k.val ≠ j.val := fun h => (Finset.mem_erase.mp hk).1 (Fin.ext h)
  simp [hkj]

theorem weight_phase_setBit_one {n : ℕ} (z : Bits n) (j : ℕ) (hj : j < n) :
    I ^ weight (setBit z j 1) = I ^ weight (setBit z j 0) * I := by
  rw [weight_setBit z ⟨j,hj⟩ 1, weight_setBit z ⟨j,hj⟩ 0]
  simp [ZMod.val_one_eq_one_mod, pow_add, mul_comm]

/-- Hadamard 产生的相对相位是 (-i)^w_j，不能从图字中删除。 -/
theorem hadamard_yColumn {n : ℕ} (w z : Bits n) (j : ℕ) (hj : j < n) :
    hadamardAt j (yColumn w) z =
      (-I) ^ (coord w j).val * character w z * hadamardAt j (yColumn 0) z := by
  simp only [hadamardAt, yColumn, CircuitPauli.char_setBit, weight_phase_setBit_one z j hj]
  have hw := OddEJM.bit_cases (coord w j)
  have hz := OddEJM.bit_cases (coord z j)
  have htwo : (2 : Bit) = 0 := by decide
  generalize I ^ weight (setBit z j 0) = A
  rcases hw with hw | hw <;> rcases hz with hz | hz <;>
    simp [hw, hz, character, dot, ZMod.val_one_eq_one_mod, CharTwo.add_self_eq_zero] <;>
    ring_nf <;> simp [I_sq, htwo, bitSign] <;> ring

/-- 原门 Y 基输出恰为同一参考态的图字像，并保留末位 Hadamard 相位。 -/
theorem circuit_yColumn {n : ℕ} (hn : 0 < n) (w y : Bits n) :
    circuit (yColumn w) y =
      (-I) ^ (coord w (n-1)).val * character (CircuitPauli.edgeMask w) y *
        circuit (yColumn (0 : Bits n)) y := by
  change hadamardAt (n-1) (yColumn w) (difference y) = _
  rw [hadamard_yColumn w (difference y) (n-1) (by omega)]
  simp only [character, CircuitPauli.dot_edgeMask, circuit, chain]

/-- 参考图态仍由真实 H/CNOT 电路定义。 -/
def baseGraph (n : ℕ) : Vec n := circuit (yColumn (0 : Bits n))

def graphCoefficient (n : ℕ) (u : ℂ) (h : Bits 4) : ℂ :=
  fourier (fun x => u ^ (F x).val) h *
    (-I) ^ (coord (featureMask n h) (n-1)).val

/-- 与 Appendix E 的十六图字正规形逐振幅相同。 -/
theorem physicalBackground_graph_words {n : ℕ} (hn : 0 < n) (u : ℂ) (y : Bits n) :
    physicalBackground n u y = -I *
      ∑ h : Bits 4, graphCoefficient n u h *
        character (CircuitPauli.edgeMask (featureMask n h)) y * baseGraph n y := by
  rw [physicalBackground_fourier]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [circuit_yColumn hn]
  simp only [graphCoefficient, baseGraph]
  ring

end UnifiedEJM.GraphBackground
