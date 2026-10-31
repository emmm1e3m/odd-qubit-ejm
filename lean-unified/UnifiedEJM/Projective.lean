import UnifiedEJM.Physical

namespace UnifiedEJM.Physical
open OddEJM
open scoped BigOperators

/-- 实际振幅的秩一投影矩阵。 -/
def projector {n : ℕ} (ψ : Vec n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of (fun z w => ψ z * star (ψ w))

theorem circuit_scale {n : ℕ} (c : ℂ) (ψ : Vec n) :
    circuit (fun z => c * ψ z) = fun z => c * circuit ψ z := by
  funext z
  simp only [circuit, chain, hadamardAt]
  ring

/-- 内积保持性给出实际电路的单射性。 -/
theorem circuit_injective {n : ℕ} (hn : 0 < n) : Function.Injective (@circuit n) := by
  intro ψ φ h
  funext z
  have hi : inner (ket z) ψ = inner (ket z) φ := by
    calc
      _ = inner (circuit (ket z)) (circuit ψ) := (circuit_inner hn _ _).symm
      _ = inner (circuit (ket z)) (circuit φ) := by rw [h]
      _ = _ := circuit_inner hn _ _
  simpa [OddEJM.inner, ket] using hi

theorem inner_scale_both {n : ℕ} (c : ℂ) (ψ : Vec n) :
    inner (fun z => c * ψ z) (fun z => c * ψ z) = star c * c * inner ψ ψ := by
  simp only [OddEJM.inner, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- 归一化实际态的投影相等，当且仅当相差一个单位复相位。 -/
theorem projector_eq_iff {n : ℕ} (ψ φ : Vec n)
    (hψ : inner ψ ψ = 1) (hφ : inner φ φ = 1) :
    projector ψ = projector φ ↔
      ∃ c : ℂ, star c * c = 1 ∧ ψ = fun z => c * φ z := by
  constructor
  · intro hp
    let c := inner φ ψ
    have hstate : ψ = fun z => c * φ z := by
      funext z
      calc
        ψ z = ψ z * inner ψ ψ := by rw [hψ]; ring
        _ = ∑ w, (ψ z * star (ψ w)) * ψ w := by
          simp only [OddEJM.inner, Finset.mul_sum, mul_assoc]
        _ = ∑ w, (φ z * star (φ w)) * ψ w := by
          apply Finset.sum_congr rfl
          intro w _
          have he := congrArg (fun M : Matrix (Bits n) (Bits n) ℂ => M z w) hp
          exact congrArg (fun a => a * ψ w) he
        _ = c * φ z := by
          simp only [c, OddEJM.inner, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro w _
          ring
    refine ⟨c, ?_, hstate⟩
    rw [hstate, inner_scale_both, hφ, mul_one] at hψ
    exact hψ
  · rintro ⟨c, hc, rfl⟩
    ext z w
    simp only [projector, Matrix.of_apply, star_mul]
    calc
      c * φ z * (star (φ w) * star c) = (star c * c) * (φ z * star (φ w)) := by ring
      _ = φ z * star (φ w) := by rw [hc, one_mul]

theorem normFactor_ne_zero (n : ℕ) : normFactor n ≠ 0 := by
  unfold normFactor
  apply inv_ne_zero
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < (2 : ℝ) ^ n)))

/-- 种子投影识别整个输入相位，唯一自由度为公共复相位。 -/
theorem seed_projector_eq_iff_phase {n : ℕ} (hn : 0 < n) (u v : Bits n → ℂ)
    (hu : ∀ z, star (u z) * u z = 1) (hv : ∀ z, star (v z) * v z = 1) :
    projector (seed u) = projector (seed v) ↔
      ∃ c : ℂ, star c * c = 1 ∧ u = fun z => c * v z := by
  rw [projector_eq_iff _ _ (seed_normalized hn u hu) (seed_normalized hn v hv)]
  constructor
  · rintro ⟨c, hc, he⟩
    refine ⟨c, hc, ?_⟩
    have he' : circuit (fun z => normFactor n * u z) =
        circuit (fun z => c * (normFactor n * v z)) := by
      calc
        _ = fun z => c * seed v z := he
        _ = _ := (circuit_scale c (fun z => normFactor n * v z)).symm
    have hi := circuit_injective hn he'
    funext z
    have hz := congrFun hi z
    apply mul_left_cancel₀ (normFactor_ne_zero n)
    calc
      normFactor n * u z = c * (normFactor n * v z) := hz
      _ = normFactor n * (c * v z) := by ring
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c, hc, ?_⟩
    unfold seed
    rw [← circuit_scale]
    congr 1
    funext z
    ring

/-- 固定物理零串相位为一后，种子投影已能唯一识别整个有序测量。 -/
theorem seed_projector_injective_fixed_origin {n : ℕ} (hn : 0 < n)
    (u v : Bits n → ℂ) (hu : ∀ z, star (u z) * u z = 1)
    (hv : ∀ z, star (v z) * v z = 1) (hu0 : u 0 = 1) (hv0 : v 0 = 1) :
    projector (seed u) = projector (seed v) ↔ u = v := by
  constructor
  · intro hp
    obtain ⟨c, _, he⟩ := (seed_projector_eq_iff_phase hn u v hu hv).mp hp
    have h0 := congrFun he 0
    simp only [hu0, hv0, mul_one] at h0
    simpa only [← h0, one_mul] using he
  · rintro rfl
    rfl

theorem ordered_projectors_injective_fixed_origin {n : ℕ} (hn : 0 < n)
    (u v : Bits n → ℂ) (hu : ∀ z, star (u z) * u z = 1)
    (hv : ∀ z, star (v z) * v z = 1) (hu0 : u 0 = 1) (hv0 : v 0 = 1) :
    (∀ label, projector (measurement u label) = projector (measurement v label)) ↔ u = v := by
  constructor
  · intro h
    apply (seed_projector_injective_fixed_origin hn u v hu hv hu0 hv0).mp
    simpa using h 0
  · rintro rfl
    intro label
    rfl

end UnifiedEJM.Physical
