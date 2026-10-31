import UnifiedEJM.FourQubit
import UnifiedEJM.Inequivalence

noncomputable section
open scoped BigOperators Matrix
open Complex
namespace UnifiedEJM.FiniteInvariants

/-- 四比特末位Hadamard后的实际归一化常数。 -/
def normalization : ℂ := (4:ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹

def state159 (x : ℂ) : State := fun k => normalization * numerator159 x k

def phaseBase : State :=
  ![1,1,1,I,1,I,I,-1,1,I,I,-1,I,-1,-1,-I]

def numeratorBase : State := gateNumerator phaseBase

def stateBase : State := fun k => normalization * numeratorBase k

theorem purity_smul (A : Mat) (s : ℂ) :
    purity (s • A) = (s * star s)^2 * purity A := by
  unfold purity reduced
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,Matrix.trace_smul,smul_eq_mul]
  ring

theorem sumPurity_smul (v : State) (s : ℂ) :
    sumPurity (fun k => s * v k) = (s * star s)^2 * sumPurity v := by
  have h12 : reshape12 (fun k => s * v k) = s • reshape12 v := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h13 : reshape13 (fun k => s * v k) = s • reshape13 v := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h14 : reshape14 (fun k => s * v k) = s • reshape14 v := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  simp only [sumPurity,h12,h13,h14,purity_smul]
  ring

theorem normalization_norm : normalization * star normalization = (1:ℂ)/32 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  simp only [normalization, star_mul, star_inv₀, Complex.star_def,
    Complex.conj_ofReal, map_ofNat]
  field_simp
  linear_combination -16 * hs

/-- 常数乘子与真实电路交换。 -/
theorem circuit_const_mul {n : ℕ} (s : ℂ) (v : OddEJM.Vec n) :
    OddEJM.circuit (fun z => s * v z) = fun z => s * OddEJM.circuit v z := by
  funext z
  simp only [OddEJM.circuit, OddEJM.chain, OddEJM.hadamardAt]
  ring

theorem state159_actual_seed (x : ℂ) (k : Fin 16) :
    state159 x k = OddEJM.circuit
      (fun z => OddEJM.normFactor 4 * phase159 x (encode4 z)) (decode4 k) := by
  rw [circuit_const_mul]
  simp only [gateNumerator_circuit,← numerator159_eq_gates]
  have hn : OddEJM.normFactor 4 = (4:ℂ)⁻¹ := by norm_num [OddEJM.normFactor]
  rw [hn]
  unfold state159 normalization
  ring

end UnifiedEJM.FiniteInvariants

