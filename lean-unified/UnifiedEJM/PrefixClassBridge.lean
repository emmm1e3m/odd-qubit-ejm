import UnifiedEJM.PrefixCounts
import UnifiedEJM.PrefixKernel

open OddEJM
open scoped BigOperators

namespace UnifiedEJM.PrefixCounts

/-- 计算证书采用的类别奇偶确为原始自由位串总奇偶。 -/
theorem catParity_wordClass {L : ℕ} (x : Bits L) :
    PrefixKernel.catParity (L : Bit) (wordClass x) = parityHom L x := by
  by_cases hx0 : x = 0
  · subst x
    simp [wordClass, PrefixKernel.catParity]
  · by_cases hx1 : x = 1
    · subst x
      simp [wordClass, PrefixKernel.catParity, hx0]
    · rcases bit_cases (parityHom L x) with hp | hp <;>
        simp [wordClass, PrefixKernel.catParity, hx0, hx1, hp]

/-- 混合类确实不可能与任何常量串相同。 -/
theorem catMatches_wordClass {L : ℕ} (hL : 1 ≤ L) (x : Bits L) (b : Bit) :
    PrefixKernel.catMatches (wordClass x) b = decide (∀ j, x j = b) := by
  letI : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  have h01 := zero_ne_one_word hL
  have h0 : (∀ j, x j = (0 : Bit)) ↔ x = 0 := by
    constructor
    · exact fun h => funext h
    · intro h; subst x; simp
  have h1 : (∀ j, x j = (1 : Bit)) ↔ x = 1 := by
    constructor
    · exact fun h => funext h
    · intro h; subst x; simp
  rcases bit_cases b with hb | hb <;> subst b
  all_goals
    by_cases hx0 : x = 0
    · subst x
      simp [wordClass, PrefixKernel.catMatches, h0, h1, h01]
    · by_cases hx1 : x = 1
      · subst x
        simp [wordClass, PrefixKernel.catMatches, h0, h1, h01, hx0]
      · by_cases hp : parityHom L x = 0 <;>
          simp [wordClass, PrefixKernel.catMatches, h0, h1, hx0, hx1, hp]

theorem catWeight_eq (lp : Bit) (X : ℤ) (c : Fin 4) :
    PrefixKernel.catWeight X lp c = classWeight lp X c := by
  fin_cases c <;> simp [PrefixKernel.catWeight, PrefixKernel.catCoeff, classWeight] <;> ring

/-- 两条任意长自由组在两份独立原串上的精确四重计数。 -/
theorem sum_four_wordClass {R : Type*} [CommRing R]
    {LA LB : ℕ} (hA : 1 ≤ LA) (hB : 1 ≤ LB)
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) :
    (∑ ay : Bits LA, ∑ av : Bits LA, ∑ byy : Bits LB, ∑ bv : Bits LB,
      f (wordClass ay) (wordClass av) (wordClass byy) (wordClass bv)) =
      ∑ ca : Fin 4, ∑ da : Fin 4, ∑ cb : Fin 4, ∑ db : Fin 4,
        (classWeight (LA : Bit) (2^(LA-1) : R) ca *
          classWeight (LA : Bit) (2^(LA-1) : R) da *
          classWeight (LB : Bit) (2^(LB-1) : R) cb *
          classWeight (LB : Bit) (2^(LB-1) : R) db) * f ca da cb db := by
  let wa : Fin 4 → R := classWeight (LA : Bit) (2^(LA-1) : R)
  let wb : Fin 4 → R := classWeight (LB : Bit) (2^(LB-1) : R)
  have hb1 (ca da cb : Fin 4) :
      (∑ bv : Bits LB, f ca da cb (wordClass bv)) =
        ∑ db : Fin 4, wb db * f ca da cb db :=
    sum_wordClass hB (fun db => f ca da cb db)
  have hb2 (ca da : Fin 4) :
      (∑ byy : Bits LB, ∑ bv : Bits LB, f ca da (wordClass byy) (wordClass bv)) =
        ∑ cb : Fin 4, wb cb * ∑ db : Fin 4, wb db * f ca da cb db := by
    simp_rw [hb1]
    exact sum_wordClass hB (fun cb => ∑ db : Fin 4, wb db * f ca da cb db)
  have ha1 (ca : Fin 4) :
      (∑ av : Bits LA, ∑ byy : Bits LB, ∑ bv : Bits LB,
        f ca (wordClass av) (wordClass byy) (wordClass bv)) =
        ∑ da : Fin 4, wa da * ∑ cb : Fin 4, wb cb * ∑ db : Fin 4,
          wb db * f ca da cb db := by
    simp_rw [hb2]
    exact sum_wordClass hA (fun da =>
      ∑ cb : Fin 4, wb cb * ∑ db : Fin 4, wb db * f ca da cb db)
  simp_rw [ha1]
  rw [sum_wordClass hA (fun ca =>
    ∑ da : Fin 4, wa da * ∑ cb : Fin 4, wb cb * ∑ db : Fin 4, wb db * f ca da cb db)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ca _
  apply Finset.sum_congr rfl
  intro da _
  apply Finset.sum_congr rfl
  intro cb _
  apply Finset.sum_congr rfl
  intro db _
  dsimp [wa, wb]
  ring

/-- 空组只有空串，不能误套正长度类别重数。 -/
theorem sum_empty_word {R : Type*} [AddCommMonoid R] (f : Bits 0 → R) :
    (∑ x : Bits 0, f x) = f 0 := by
  have hu : (Finset.univ : Finset (Bits 0)) = {0} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [hu, Finset.sum_singleton]

/-- 空组与正长度组使用同一个接口，空组不会破坏常量串。 -/
def runInfo (L : ℕ) : Option Bit := if L = 0 then none else some (L : Bit)

@[simp] theorem runInfo_getD (L : ℕ) : (runInfo L).getD 0 = (L : Bit) := by
  by_cases h : L = 0 <;> simp [runInfo, h]

theorem runParity_wordClass {L : ℕ} (x : Bits L) :
    PrefixKernel.runParity (runInfo L) (wordClass x) = parityHom L x := by
  by_cases h : L = 0
  · subst L
    simp [runInfo, PrefixKernel.runParity, parityHom]
  · simpa [runInfo, h, PrefixKernel.runParity] using catParity_wordClass x

theorem runMatches_wordClass {L : ℕ} (x : Bits L) (b : Bit) :
    PrefixKernel.runMatches (runInfo L) (wordClass x) b = decide (∀ j, x j = b) := by
  by_cases h : L = 0
  · subst L
    simp [runInfo, PrefixKernel.runMatches]
  · simpa [runInfo, h, PrefixKernel.runMatches] using
      catMatches_wordClass (by omega : 1 ≤ L) x b

theorem sum_runClass {L : ℕ} (f : Fin 4 → ℤ) :
    (∑ x : Bits L, f (wordClass x)) =
      ∑ c : Fin 4, PrefixKernel.runWeight (2^(L-1)) (runInfo L) c * f c := by
  by_cases h : L = 0
  · subst L
    rw [sum_empty_word]
    simp [runInfo, wordClass, PrefixKernel.runWeight, PrefixKernel.runCoeff,
      Fin.sum_univ_succ]
  · rw [sum_wordClass (by omega : 1 ≤ L)]
    apply Finset.sum_congr rfl
    intro c _
    rw [show PrefixKernel.runWeight (2^(L-1)) (runInfo L) c =
      PrefixKernel.catWeight (2^(L-1)) (L : Bit) c by
      simp [runInfo, h, PrefixKernel.runWeight, PrefixKernel.runCoeff,
        PrefixKernel.catWeight]]
    rw [catWeight_eq]

theorem sum_runClass_ring {R : Type*} [CommRing R] {L : ℕ} (f : Fin 4 → R) :
    (∑ x : Bits L, f (wordClass x)) =
      ∑ c : Fin 4, (PrefixKernel.runWeight (2^(L-1)) (runInfo L) c : R) * f c := by
  by_cases h : L = 0
  · subst L
    rw [sum_empty_word]
    simp [runInfo, wordClass, PrefixKernel.runWeight, PrefixKernel.runCoeff,
      Fin.sum_univ_succ]
  · rw [sum_wordClass (by omega : 1 ≤ L)]
    apply Finset.sum_congr rfl
    intro c _
    have hw : (PrefixKernel.runWeight (2^(L-1)) (runInfo L) c : R) =
        classWeight (L : Bit) (2^(L-1) : R) c := by
      simp only [runInfo, h, if_false, PrefixKernel.runWeight, PrefixKernel.runCoeff]
      fin_cases c <;> simp [PrefixKernel.catCoeff, classWeight] <;> ring
    rw [hw]

end UnifiedEJM.PrefixCounts
