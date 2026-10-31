import UnifiedEJM.Projective
import Mathlib.Topology.Instances.Matrix

namespace UnifiedEJM.Physical
open OddEJM
open scoped BigOperators

theorem seed_continuous {α : Type*} [TopologicalSpace α] {n : ℕ}
    (u : α → Bits n → ℂ) (hu : ∀ z, Continuous (fun t => u t z)) :
    Continuous (fun t => seed (u t)) := by
  apply continuous_pi
  intro z
  simp only [seed, circuit, chain, hadamardAt]
  fun_prop

/-- 输入对角相位逐振幅连续，推出实际有序测量列连续。 -/
theorem measurement_continuous {α : Type*} [TopologicalSpace α] {n : ℕ}
    (u : α → Bits n → ℂ) (hu : ∀ z, Continuous (fun t => u t z)) (label : Bits n) :
    Continuous (fun t => measurement (u t) label) := by
  apply continuous_pi
  intro z
  simp only [measurement, circuit, chain, hadamardAt]
  fun_prop

theorem projector_continuous {α : Type*} [TopologicalSpace α] {n : ℕ}
    (ψ : α → Vec n) (hψ : Continuous ψ) : Continuous (fun t => projector (ψ t)) := by
  apply continuous_pi
  intro z
  apply continuous_pi
  intro w
  simp only [projector, Matrix.of_apply]
  fun_prop

/-- 连续性落实到测量投影，而不依赖列向量的规范选择。 -/
theorem measurement_projector_continuous {α : Type*} [TopologicalSpace α] {n : ℕ}
    (u : α → Bits n → ℂ) (hu : ∀ z, Continuous (fun t => u t z)) (label : Bits n) :
    Continuous (fun t => projector (measurement (u t) label)) :=
  projector_continuous _ (measurement_continuous u hu label)

theorem reduced_continuous {α : Type*} [TopologicalSpace α] {n : ℕ}
    (ψ : α → Vec n) (hψ : Continuous ψ) (j : Fin n) :
    Continuous (fun t => reduced (ψ t) j) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [reduced, Matrix.of_apply]
  fun_prop

end UnifiedEJM.Physical
