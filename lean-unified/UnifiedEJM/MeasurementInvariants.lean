import UnifiedEJM.SingleInvariant
import UnifiedEJM.FourQubitPauli

noncomputable section
open scoped BigOperators Matrix
open OddEJM OddEJM.CircuitPauli

namespace UnifiedEJM.BipartiteInvariant
open FiniteInvariants

/-- 只把实际四比特振幅重新索引为十六项数组。 -/
def measurementState (u : Bits 4 → ℂ) (label : Bits 4) : State :=
  fun k => Physical.measurement u label (decode4 k)

def seedState (u : Bits 4 → ℂ) : State :=
  fun k => Physical.seed u (decode4 k)

theorem measurementState_as_localAction (u : Bits 4 → ℂ) (label : Bits 4) :
    measurementState u label =
      localAction (fun j => Physical.pauliMatrix (orbitX label j) (orbitZ label j))
        (seedState u) := by
  funext k
  exact Physical.measurement_tensor_fin16 u label k

/-- 每个真实测量列均与种子共享三种二二划分的纯度和。 -/
theorem sumPurity_measurement_columns (u : Bits 4 → ℂ) (label : Bits 4) :
    sumPurity (measurementState u label) = sumPurity (seedState u) := by
  rw [measurementState_as_localAction]
  exact sumPurity_localAction _ (fun j => Physical.pauliMatrix_unitary _ _) _

/-- 每个真实测量列均与种子共享四种一三划分的纯度和。 -/
theorem singlePuritySum_measurement_columns (u : Bits 4 → ℂ) (label : Bits 4) :
    singlePuritySum (measurementState u label) = singlePuritySum (seedState u) := by
  rw [measurementState_as_localAction]
  exact singlePuritySum_localAction _ (fun j => Physical.pauliMatrix_unitary _ _) _

/-- 论文采用的测量等价：共同局域酉、比特置换、结果重标和各列相位。 -/
def EquivalentMeasurements (u v : Bits 4 → ℂ) : Prop :=
  ∃ U : Fin 4 → Matrix Bit Bit ℂ, (∀ j,(U j)ᴴ*U j=1) ∧
    ∃ p : Equiv.Perm (Fin 4), ∃ σ : Equiv.Perm (Bits 4), ∃ c : Bits 4 → ℂ,
      (∀ label,star (c label)*c label=1) ∧
      ∀ label,measurementState v label =
        c label • localAction U (permute p (measurementState u (σ label)))

/-- 两个真实测量若等价，两种种子谱不变量都必须相同。 -/
theorem equivalent_measurements_invariants (u v : Bits 4 → ℂ)
    (heq : EquivalentMeasurements u v) :
    sumPurity (seedState u)=sumPurity (seedState v) ∧
    singlePuritySum (seedState u)=singlePuritySum (seedState v) := by
  obtain ⟨U,hU,p,σ,c,hc,heq⟩ := heq
  have h₂ := sumPurity_of_equivalence U hU p (c 0) (hc 0)
    (measurementState u (σ 0)) (measurementState v 0) (heq 0)
  have h₁ := singlePuritySum_of_equivalence U hU p (c 0) (hc 0)
    (measurementState u (σ 0)) (measurementState v 0) (heq 0)
  rw [sumPurity_measurement_columns,sumPurity_measurement_columns] at h₂
  rw [singlePuritySum_measurement_columns,singlePuritySum_measurement_columns] at h₁
  exact ⟨h₂.symm,h₁.symm⟩

end UnifiedEJM.BipartiteInvariant
