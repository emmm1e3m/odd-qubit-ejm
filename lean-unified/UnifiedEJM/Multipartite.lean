import UnifiedEJM.PauliTensor
import UnifiedEJM.MonomialInvariant
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open OddEJM OddEJM.CircuitPauli

namespace UnifiedEJM.Multipartite

abbrev Side {n : ℕ} (S : Finset (Fin n)) := {j : Fin n // j ∈ S} → Bit
abbrev OtherSide {n : ℕ} (S : Finset (Fin n)) := {j : Fin n // j ∉ S} → Bit

/-- 按实际物理位集合拆分计算基。 -/
def split {n : ℕ} (S : Finset (Fin n)) : Bits n ≃ Side S × OtherSide S :=
  Equiv.piEquivPiSubtypeProd (fun j => j ∈ S) (fun _ => Bit)

@[simp] theorem merge_left {n : ℕ} (S : Finset (Fin n)) (a : Side S)
    (b : OtherSide S) (j : {j // j ∈ S}) : (split S).symm (a,b) j = a j := by
  simp [split, Equiv.piEquivPiSubtypeProd, j.property]

@[simp] theorem merge_right {n : ℕ} (S : Finset (Fin n)) (a : Side S)
    (b : OtherSide S) (j : {j // j ∉ S}) : (split S).symm (a,b) j = b j := by
  simp [split, Equiv.piEquivPiSubtypeProd, j.property]

/-- 用两个完整位串的两部分拼接一个实际位串。 -/
def mix {n : ℕ} (S : Finset (Fin n)) (z w : Bits n) : Bits n :=
  fun j => if j ∈ S then z j else w j

/-- 纯态振幅矩阵；没有把任何纯度结论放进定义。 -/
def reshape {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    Matrix (Side S) (OtherSide S) ℂ :=
  fun a b => ψ ((split S).symm (a,b))

def reduced {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :=
  reshape S ψ * (reshape S ψ)ᴴ

def cutPurity {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) : ℂ :=
  PurityInvariant.purity (reshape S ψ)

theorem reduced_apply {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) (a a' : Side S) :
    reduced S ψ a a' = ∑ b : OtherSide S,
      ψ ((split S).symm (a,b)) * star (ψ ((split S).symm (a',b))) := by
  simp [reduced, reshape, Matrix.mul_apply, Matrix.conjTranspose_apply]

@[simp] theorem mix_merge {n : ℕ} (S : Finset (Fin n))
    (a a' : Side S) (b b' : OtherSide S) :
    mix S ((split S).symm (a,b)) ((split S).symm (a',b')) =
      (split S).symm (a,b') := by
  funext j
  by_cases h : j ∈ S <;> simp [mix,split,Equiv.piEquivPiSubtypeProd,h]

/-- 真实偏迹平方的迹等于交换算符的双位串有限和。 -/
theorem cutPurity_eq_swap_sum {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    cutPurity S ψ = ∑ z : Bits n, ∑ w : Bits n,
      ψ z * ψ w * star (ψ (mix S z w)) * star (ψ (mix S w z)) := by
  rw [← (split S).symm.sum_comp (fun z => ∑ w : Bits n,
      ψ z * ψ w * star (ψ (mix S z w)) * star (ψ (mix S w z)))]
  simp_rw [← (split S).symm.sum_comp (fun w =>
      ψ _ * ψ w * star (ψ (mix S _ w)) * star (ψ (mix S w _)))]
  simp only [Fintype.sum_prod_type, mix_merge]
  unfold cutPurity PurityInvariant.purity
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs =>
    arg 2
    ext a'
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a' ha'
  apply Finset.sum_congr rfl
  intro b' hb'
  simp only [reshape]
  ring

/-- 任意有限行列重新编号均保持真实约化纯度。 -/
theorem purity_equiv {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix m n ℂ) (e : p ≃ m) (f : q ≃ n) :
    PurityInvariant.purity (A.submatrix e f) = PurityInvariant.purity A := by
  unfold PurityInvariant.purity
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  exact Equiv.sum_comp e (fun i => ((A * Aᴴ) * (A * Aᴴ)) i i)

/-- 单比特矩阵的真实张量积，在所有计算基赋值上索引。 -/
def tensorMatrix {ι : Type*} [Fintype ι] (U : ι → Matrix Bit Bit ℂ) :
    Matrix (ι → Bit) (ι → Bit) ℂ := fun z w => ∏ j, U j (z j) (w j)

theorem tensorMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1) :
    (tensorMatrix U)ᴴ * tensorMatrix U = 1 := by
  classical
  ext z v
  change (∑ w : ι → Bit, star (∏ j, U j (w j) (z j)) *
    (∏ j, U j (w j) (v j))) = if z = v then 1 else 0
  calc
    _ = ∑ w : ι → Bit, ∏ j, star (U j (w j) (z j)) * U j (w j) (v j) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [star_prod, Finset.prod_mul_distrib]
    _ = ∏ j, ∑ b : Bit, star (U j b (z j)) * U j b (v j) :=
      (Fintype.prod_sum (fun j b => star (U j b (z j)) * U j b (v j))).symm
    _ = ∏ j, (if z j = v j then (1 : ℂ) else 0) := by
      apply Finset.prod_congr rfl
      intro j hj
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
        using congrArg (fun A : Matrix Bit Bit ℂ => A (z j) (v j)) (hU j)
    _ = _ := by
      by_cases h : z = v
      · subst v; simp
      · have hne : ∃ j, z j ≠ v j := by
          by_contra hcontra
          push Not at hcontra
          exact h (funext hcontra)
        obtain ⟨j,hj⟩ := hne
        rw [ite_eq_right h]
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
def localAction {n : ℕ} (U : Fin n → Matrix Bit Bit ℂ) (ψ : Vec n) : Vec n :=
  fun z => ∑ w, tensorMatrix U z w * ψ w

theorem tensorMatrix_split {n : ℕ} (S : Finset (Fin n))
    (U : Fin n → Matrix Bit Bit ℂ) (a a' : Side S) (b b' : OtherSide S) :
    tensorMatrix U ((split S).symm (a,b)) ((split S).symm (a',b')) =
      tensorMatrix (fun j : {j // j ∈ S} => U j) a a' *
      tensorMatrix (fun j : {j // j ∉ S} => U j) b b' := by
  unfold tensorMatrix
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ S)]
  simp only [merge_left, merge_right]
  congr 1
  apply Finset.prod_congr
  · ext j; simp
  · intro j hj; rfl

theorem reshape_localAction {n : ℕ} (S : Finset (Fin n))
    (U : Fin n → Matrix Bit Bit ℂ) (ψ : Vec n) :
    reshape S (localAction U ψ) =
      tensorMatrix (fun j : {j // j ∈ S} => U j) * reshape S ψ *
      (tensorMatrix (fun j : {j // j ∉ S} => U j))ᵀ := by
  ext a b
  unfold reshape localAction
  rw [← (split S).symm.sum_comp (fun w =>
    tensorMatrix U ((split S).symm (a,b)) w * ψ w)]
  simp only [Fintype.sum_prod_type, tensorMatrix_split, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b' hb'
  apply Finset.sum_congr rfl
  intro a' ha'
  ring

theorem purity_left_right_transpose {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k]
    (A : Matrix m k ℂ) (L : Matrix m m ℂ) (R : Matrix k k ℂ)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) :
    PurityInvariant.purity (L * A * Rᵀ) = PurityInvariant.purity A := by
  have hRT : Rᵀ * (Rᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose]
      using congrArg Matrix.transpose hR
  simpa only [Matrix.conjTranspose_conjTranspose] using
    PurityInvariant.purity_local_unitary A L (Rᵀ)ᴴ hL (by simpa using hRT)

/-- 真实约化态在局域酉作用下仅作子系统内的酉共轭。 -/
theorem reduced_localAction {n : ℕ} (S : Finset (Fin n))
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1) (ψ : Vec n) :
    reduced S (localAction U ψ) =
      tensorMatrix (fun j : {j // j ∈ S} => U j) * reduced S ψ *
        (tensorMatrix (fun j : {j // j ∈ S} => U j))ᴴ := by
  let L := tensorMatrix (fun j : {j // j ∈ S} => U j)
  let R := tensorMatrix (fun j : {j // j ∉ S} => U j)
  have hR : Rᴴ * R = 1 := tensorMatrix_unitary _ (fun j => hU j)
  have hRT : Rᵀ * (Rᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose]
      using congrArg Matrix.transpose hR
  unfold reduced
  rw [reshape_localAction]
  change (L * reshape S ψ * Rᵀ) * (L * reshape S ψ * Rᵀ)ᴴ =
    L * (reshape S ψ * (reshape S ψ)ᴴ) * Lᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc
    _ = L * reshape S ψ * (Rᵀ * (Rᵀ)ᴴ) * (reshape S ψ)ᴴ * Lᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hRT]; simp only [Matrix.mul_one,Matrix.mul_assoc]

/-- 任意物理分割的纯度在任意单比特局域酉下不变。 -/
theorem cutPurity_localAction {n : ℕ} (S : Finset (Fin n))
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1) (ψ : Vec n) :
    cutPurity S (localAction U ψ) = cutPurity S ψ := by
  unfold cutPurity
  rw [reshape_localAction]
  exact purity_left_right_transpose _ _ _
    (tensorMatrix_unitary _ (fun j => hU j))
    (tensorMatrix_unitary _ (fun j => hU j))

/-- 实际测量列和种子的任意二分割纯度相同。 -/
theorem cutPurity_measurement {n : ℕ} (hn : 0 < n)
    (u : Bits n → ℂ) (label : Bits n) (S : Finset (Fin n)) :
    cutPurity S (Physical.measurement u label) = cutPurity S (Physical.seed u) := by
  have heq : Physical.measurement u label =
      localAction (fun j => Physical.pauliMatrix (orbitX label j) (orbitZ label j))
        (Physical.seed u) := by
    rw [Physical.measurement_orbit hn]
    funext z
    exact Physical.pauliAction_tensor _ _ _ _
  rw [heq]
  exact cutPurity_localAction S _ (fun j => Physical.pauliMatrix_unitary _ _) _

theorem cutPurity_phase {n : ℕ} (S : Finset (Fin n))
    (c : ℂ) (hc : star c * c = 1) (ψ : Vec n) :
    cutPurity S (c • ψ) = cutPurity S ψ := by
  unfold cutPurity
  have h : reshape S (c • ψ) =
      Matrix.of (fun a b => c * 1 * reshape S ψ a b) := by
    ext a b
    simp [reshape]
  rw [h]
  exact PurityInvariant.purity_phase _ _ _ (fun _ => hc) (fun _ => by simp)

/-- 物理位的真实重排；p把旧的分割位置映到新的位置。 -/
def permuteBits {n : ℕ} (p : Equiv.Perm (Fin n)) : Bits n ≃ Bits n where
  toFun z := fun j => z (p.symm j)
  invFun z := fun j => z (p j)
  left_inv z := by funext j; simp
  right_inv z := by funext j; simp

def permute {n : ℕ} (p : Equiv.Perm (Fin n)) (ψ : Vec n) : Vec n :=
  fun z => ψ (permuteBits p z)

theorem permuteBits_mix {n : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (z w : Bits n) :
    permuteBits p (mix S z w) =
      mix (S.map p.toEmbedding) (permuteBits p z) (permuteBits p w) := by
  funext j
  have hmem : j ∈ S.map p.toEmbedding ↔ p.symm j ∈ S := by
    simp
  simp only [permuteBits, Equiv.coe_fn_mk, mix, hmem]

theorem cutPurity_permute {n : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (ψ : Vec n) :
    cutPurity S (permute p ψ) = cutPurity (S.map p.toEmbedding) ψ := by
  rw [cutPurity_eq_swap_sum, cutPurity_eq_swap_sum]
  simp only [permute, permuteBits_mix]
  have hw (z : Bits n) := (permuteBits p).sum_comp (fun w =>
    ψ (permuteBits p z) * ψ w *
      star (ψ (mix (S.map p.toEmbedding) (permuteBits p z) w)) *
      star (ψ (mix (S.map p.toEmbedding) w (permuteBits p z))))
  simp_rw [hw]
  exact (permuteBits p).sum_comp (fun z => ∑ w : Bits n,
    ψ z * ψ w * star (ψ (mix (S.map p.toEmbedding) z w)) *
      star (ψ (mix (S.map p.toEmbedding) w z)))

/-- 对全部无序物理比特对求和，n=6时共有15项。 -/
def twoBodyPurity {n : ℕ} (ψ : Vec n) : ℂ :=
  ∑ S : Finset (Fin n), if S.card = 2 then cutPurity S ψ else 0

theorem twoBodyPurity_localAction {n : ℕ}
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1) (ψ : Vec n) :
    twoBodyPurity (localAction U ψ) = twoBodyPurity ψ := by
  simp only [twoBodyPurity, cutPurity_localAction _ U hU]

theorem twoBodyPurity_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (ψ : Vec n) :
    twoBodyPurity (permute p ψ) = twoBodyPurity ψ := by
  unfold twoBodyPurity
  simp_rw [cutPurity_permute]
  simpa only [Equiv.finsetCongr_apply, Finset.card_map] using
    (Equiv.finsetCongr p).sum_comp
      (fun S : Finset (Fin n) => if S.card = 2 then cutPurity S ψ else 0)

theorem twoBodyPurity_phase {n : ℕ} (c : ℂ) (hc : star c * c = 1) (ψ : Vec n) :
    twoBodyPurity (c • ψ) = twoBodyPurity ψ := by
  simp only [twoBodyPurity, cutPurity_phase _ c hc]

theorem twoBodyPurity_measurement {n : ℕ} (hn : 0 < n)
    (u : Bits n → ℂ) (label : Bits n) :
    twoBodyPurity (Physical.measurement u label) = twoBodyPurity (Physical.seed u) := by
  simp only [twoBodyPurity, cutPurity_measurement hn]

/-- 完整测量等价使用同一个局域酉与物理位置换，允许结果重标和列相位。 -/
def EquivalentMeasurements {n : ℕ} (u v : Bits n → ℂ) : Prop :=
  ∃ U : Fin n → Matrix Bit Bit ℂ, (∀ j, (U j)ᴴ * U j = 1) ∧
    ∃ p : Equiv.Perm (Fin n), ∃ σ : Equiv.Perm (Bits n), ∃ c : Bits n → ℂ,
      (∀ label, star (c label) * c label = 1) ∧
      ∀ label, Physical.measurement v label =
        c label • localAction U (permute p (Physical.measurement u (σ label)))

theorem equivalent_measurements_twoBodyPurity {n : ℕ} (hn : 0 < n)
    (u v : Bits n → ℂ) (heq : EquivalentMeasurements u v) :
    twoBodyPurity (Physical.seed u) = twoBodyPurity (Physical.seed v) := by
  obtain ⟨U,hU,p,σ,c,hc,h⟩ := heq
  have he := congrArg twoBodyPurity (h 0)
  rw [twoBodyPurity_phase _ (hc 0), twoBodyPurity_localAction _ hU,
    twoBodyPurity_permute, twoBodyPurity_measurement hn,
    twoBodyPurity_measurement hn] at he
  exact he.symm

/-- 两体纯度和不同即排除上述完整测量等价，不把结论作为定义。 -/
theorem not_equivalent_of_twoBodyPurity {n : ℕ} (hn : 0 < n)
    (u v : Bits n → ℂ)
    (h : twoBodyPurity (Physical.seed u) ≠ twoBodyPurity (Physical.seed v)) :
    ¬ EquivalentMeasurements u v := by
  intro heq
  exact h (equivalent_measurements_twoBodyPurity hn u v heq)

/-- 所有非平凡物理二分割；保留互补重复不会改变最小值。 -/
def cuts (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ)

theorem cuts_nonempty {n : ℕ} (hn : 2 ≤ n) : (cuts n).Nonempty := by
  let j : Fin n := ⟨0, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  refine ⟨{j}, ?_⟩
  simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact Finset.singleton_ne_empty j
  intro h
  have hk : k ∈ ({j} : Finset (Fin n)) := by rw [h]; simp
  have hkj : k = j := by simpa using hk
  have := congrArg Fin.val hkj
  simp [j,k] at this

/-- 纯态GME concurrence直接是全部非平凡分割的concurrence最小值。 -/
def gme {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n) : ℝ :=
  ((cuts n).image (fun S => Real.sqrt (2 * (1 - (cutPurity S ψ).re)))).min'
    ((cuts_nonempty hn).image _)

/-- 全部分割纯度的上界和达到者给出GME的精确值。 -/
theorem gme_of_max_purity {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n) (p : ℝ)
    (hupper : ∀ S ∈ cuts n, (cutPurity S ψ).re ≤ p)
    (hattain : ∃ S ∈ cuts n, (cutPurity S ψ).re = p) :
    gme hn ψ = Real.sqrt (2 * (1 - p)) := by
  unfold gme
  apply le_antisymm
  · obtain ⟨S,hS,hSp⟩ := hattain
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨S,hS,by rw [hSp]⟩
  · apply Finset.le_min'
    intro y hy
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hy
    apply Real.sqrt_le_sqrt
    have := hupper S hS
    linarith

theorem gme_localAction {n : ℕ} (hn : 2 ≤ n)
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1) (ψ : Vec n) :
    gme hn (localAction U ψ) = gme hn ψ := by
  simp only [gme, cutPurity_localAction _ U hU]

theorem gme_measurement {n : ℕ} (hn : 2 ≤ n)
    (u : Bits n → ℂ) (label : Bits n) :
    gme hn (Physical.measurement u label) = gme hn (Physical.seed u) := by
  simp only [gme, cutPurity_measurement (by omega : 0 < n)]

/-- n对最大纠缠对的真实联合振幅。 -/
def eprPairs (n : ℕ) (z w : Bits n) : ℂ := if z = w then normFactor n else 0

/-- 中心对基矢作投影后，外围的未归一化纯态振幅。 -/
def eprPostselect {n : ℕ} (ψ : Vec n) : Vec n :=
  fun w => ∑ z : Bits n, star (ψ z) * eprPairs n z w

theorem eprPostselect_eq {n : ℕ} (ψ : Vec n) :
    eprPostselect ψ = fun w => normFactor n * star (ψ w) := by
  funext w
  simp [eprPostselect,eprPairs,mul_comm]

theorem eprPostselect_probability {n : ℕ} (ψ : Vec n) (hψ : inner ψ ψ = 1) :
    inner (eprPostselect ψ) (eprPostselect ψ) = (2 : ℂ)⁻¹ ^ n := by
  rw [eprPostselect_eq]
  have hsum : inner (fun w => normFactor n * star (ψ w))
      (fun w => normFactor n * star (ψ w)) =
      (star (normFactor n) * normFactor n) * inner ψ ψ := by
    unfold OddEJM.inner
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [star_mul,star_star]
    ring
  rw [hsum,hψ,mul_one]
  have hp := normFactor_card n
  have hpow : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (mul_right_cancel₀ hpow)
  rw [hp, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_pow]

theorem epr_measurement_probability {n : ℕ} (hn : 0 < n)
    (u : Bits n → ℂ) (hu : ∀ z, star (u z) * u z = 1) (label : Bits n) :
    inner (eprPostselect (Physical.measurement u label))
      (eprPostselect (Physical.measurement u label)) = (2 : ℂ)⁻¹ ^ n :=
  eprPostselect_probability _ (Physical.measurement_normalized hn u hu label)

/-- Pauli轨道结果的共轭态仍由单比特Pauli张量作用关联。 -/
theorem conjugate_measurement_orbit {n : ℕ} (hn : 0 < n)
    (u : Bits n → ℂ) (label : Bits n) :
    (fun z => star (Physical.measurement u label z)) =
      pauliAction (orbitX label) (orbitZ label) 1
        (fun z => star (Physical.seed u z)) := by
  rw [Physical.measurement_orbit hn]
  funext z
  simp [pauliAction]

theorem pauliAction_square {n : ℕ} (a b : Bits n) (ψ : Vec n) :
    pauliAction a b 1 (pauliAction a b 1 ψ) =
      fun z => character b a * ψ z := by
  funext z
  simp only [pauliAction, one_mul, add_assoc, bits_add_self, add_zero,
    character_add]
  have h := character_mul_self b z
  linear_combination character b a * ψ z * h

/-- 已知结果的局域Pauli校正把外围归一化态恢复为共同共轭种子。 -/
theorem epr_measurement_local_correction {n : ℕ} (hn : 0 < n)
    (u : Bits n → ℂ) (label : Bits n) :
    pauliAction (orbitX label) (orbitZ label) 1
      (fun z => star (Physical.measurement u label z)) =
        (fun z => star (Physical.seed u z)) := by
  rw [conjugate_measurement_orbit hn, pauliAction_square]
  simp only [orbit_character_self hn, one_mul]

def singletonSide {n : ℕ} (j : Fin n) : Bit ≃ Side ({j} : Finset (Fin n)) where
  toFun a := fun _ => a
  invFun a := a ⟨j,by simp⟩
  left_inv a := rfl
  right_inv a := by
    funext k
    have hk : k.val = j := Finset.mem_singleton.mp k.property
    have heq : k = ⟨j,by simp⟩ := Subtype.ext hk
    rw [heq]

def singletonRest {n : ℕ} (j : Fin n) : BitRest j ≃ OtherSide ({j} : Finset (Fin n)) where
  toFun r := fun k => r ⟨k.val,by simpa using k.property⟩
  invFun r := fun k => r ⟨k.val,by simpa using k.property⟩
  left_inv r := by funext k; rfl
  right_inv r := by funext k; rfl

theorem merge_singleton {n : ℕ} (j : Fin n) (a : Bit) (r : BitRest j) :
    (split {j}).symm (singletonSide j a, singletonRest j r) = joinBit j a r := by
  funext k
  by_cases hk : k = j <;>
    simp [split,Equiv.piEquivPiSubtypeProd,singletonSide,singletonRest,joinBit,hk]

/-- 单元素分割与已形式化的真实单比特偏迹完全一致。 -/
theorem cutPurity_singleton {n : ℕ} (j : Fin n) (ψ : Vec n) :
    cutPurity {j} ψ = Matrix.trace (OddEJM.reduced ψ j * OddEJM.reduced ψ j) := by
  let A : Matrix Bit (BitRest j) ℂ := fun a r => ψ (joinBit j a r)
  have hA : (reshape {j} ψ).submatrix (singletonSide j) (singletonRest j) = A := by
    ext a r
    simp [Matrix.submatrix,reshape,A,merge_singleton]
  have hR : A * Aᴴ = OddEJM.reduced ψ j := by
    ext a b
    simp [A,Matrix.mul_apply,Matrix.conjTranspose_apply,OddEJM.reduced]
  have hp := purity_equiv (reshape {j} ψ) (singletonSide j) (singletonRest j)
  rw [hA] at hp
  change PurityInvariant.purity (reshape {j} ψ) = _
  rw [← hp]
  unfold PurityInvariant.purity
  rw [hR]

theorem purity_product {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k] (a : m → ℂ) (b : k → ℂ)
    (ha : ∑ i, star (a i) * a i = 1) (hb : ∑ j, star (b j) * b j = 1) :
    PurityInvariant.purity (fun i j => a i * b j) = 1 := by
  have hR : (show Matrix m k ℂ from fun i j => a i * b j) *
      (show Matrix m k ℂ from fun i j => a i * b j)ᴴ =
      (fun i j => a i * star (a j)) := by
    ext i j
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_mul]
    calc
      _ = (a i * star (a j)) * (∑ l, star (b l) * b l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = _ := by rw [hb]; ring
  unfold PurityInvariant.purity
  rw [hR]
  have hsquare : (show Matrix m m ℂ from fun i j => a i * star (a j)) *
      (show Matrix m m ℂ from fun i j => a i * star (a j)) =
      (fun i j => a i * star (a j)) := by
    ext i j
    simp only [Matrix.mul_apply]
    calc
      _ = (a i * star (a j)) * (∑ l, star (a l) * a l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = _ := by rw [ha]; ring
  rw [hsquare]
  simpa only [Matrix.trace,Matrix.diag_apply,mul_comm] using ha

/-- 两侧均为归一化纯态的实际张量积。 -/
def ProductAcross {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) : Prop :=
  ∃ a : Side S → ℂ, ∃ b : OtherSide S → ℂ,
    (∑ i, star (a i) * a i = 1) ∧ (∑ j, star (b j) * b j = 1) ∧
    reshape S ψ = (fun i j => a i * b j)

theorem cutPurity_of_product {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n)
    (h : ProductAcross S ψ) : cutPurity S ψ = 1 := by
  obtain ⟨a,b,ha,hb,hab⟩ := h
  unfold cutPurity
  rw [hab]
  exact purity_product a b ha hb

/-- 全部单比特纯度小于一排除任意局域酉、位置换后的纯比特因子。 -/
theorem no_pure_qubit_factor {n : ℕ} (ψ : Vec n)
    (hψ : ∀ j, (Matrix.trace (OddEJM.reduced ψ j * OddEJM.reduced ψ j)).re < 1)
    (U : Fin n → Matrix Bit Bit ℂ) (hU : ∀ j, (U j)ᴴ * U j = 1)
    (p : Equiv.Perm (Fin n)) (c : ℂ) (hc : star c * c = 1) (j : Fin n) :
    ¬ ProductAcross {j} (c • localAction U (permute p ψ)) := by
  intro hprod
  have hp := cutPurity_of_product {j} _ hprod
  rw [cutPurity_phase _ c hc, cutPurity_localAction _ U hU,
    cutPurity_permute, Finset.map_singleton, cutPurity_singleton] at hp
  have hpre := congrArg Complex.re hp
  have hlt := hψ ((p.toEmbedding) j)
  simp only [Complex.one_re] at hpre
  exact (ne_of_lt hlt) hpre

/-- 互补的实际物理子系统给出相同纯度。 -/
theorem cutPurity_compl {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    cutPurity Sᶜ ψ = cutPurity S ψ := by
  have hm (z w : Bits n) : mix Sᶜ z w = mix S w z := by
    funext j
    by_cases hj : j ∈ S <;> simp [mix,hj]
  simp only [cutPurity_eq_swap_sum,hm]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  ring

/-- 复共轭保持每个实际子系统的实纯度。 -/
theorem cutPurity_conjugate {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    cutPurity S (fun z => star (ψ z)) = star (cutPurity S ψ) := by
  simp only [cutPurity_eq_swap_sum,star_sum,star_mul,star_star]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem cutPurity_conjugate_re {n : ℕ} (S : Finset (Fin n)) (ψ : Vec n) :
    (cutPurity S (fun z => star (ψ z))).re = (cutPurity S ψ).re := by
  rw [cutPurity_conjugate]
  rfl

theorem gme_conjugate {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n) :
    gme hn (fun z => star (ψ z)) = gme hn ψ := by
  simp only [gme,cutPurity_conjugate_re]

/-- 正的纯态GME排除每个非平凡二分割上的纯态张量积。 -/
theorem gme_pos_no_product {n : ℕ} (hn : 2 ≤ n) (ψ : Vec n)
    (hpos : 0 < gme hn ψ) (S : Finset (Fin n)) (hS : S ∈ cuts n) :
    ¬ ProductAcross S ψ := by
  intro hprod
  have hp := cutPurity_of_product S ψ hprod
  have hle : gme hn ψ ≤ Real.sqrt (2 * (1 - (cutPurity S ψ).re)) :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
  rw [hp] at hle
  norm_num at hle
  exact (not_le_of_gt hpos) hle

end UnifiedEJM.Multipartite

