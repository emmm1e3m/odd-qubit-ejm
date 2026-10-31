import UnifiedEJM.BooleanLines

/-! 指定基点的精确字符和，供模型上界的低维达到性使用。 -/
namespace UnifiedEJM.BooleanLines
open OddEJM Complex
open scoped BigOperators

def qDelta {n : ℕ} (z : Bits n) : Bit := if z=0 then 1 else 0

@[simp] theorem qDelta_zero (n : ℕ) : qDelta (0:Bits n)=1 := by simp [qDelta]

theorem delta_walsh {n : ℕ} (h : Bits n) (hh : h≠0) : walsh qDelta h = -2 := by
  have hp (z : Bits n) : bitSign (qDelta z+dot h z)=
      character h z-2*(if z=0 then 1 else 0:ℂ) := by
    by_cases hz : z=0
    · subst z
      norm_num [qDelta,character,dot,bitSign]
    · simp [qDelta,hz,character]
  unfold walsh
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,character_sum,ite_eq_right hh]
  simp

theorem delta_derivative_walsh {n : ℕ} (a h : Bits n) (ha : a≠0) (hh : h≠0)
    (hd : dot h a=0) : walsh (derivative qDelta a) h = -4 := by
  have hp (z : Bits n) : bitSign (derivative qDelta a z+dot h z)=
      character h z-2*(if z=0 then 1 else 0:ℂ)-
        2*(if z=a then character h a else 0) := by
    by_cases hz : z=0
    · subst z
      norm_num [derivative,qDelta,ha,Ne.symm ha,character,dot,bitSign]
    · by_cases hza : z=a
      · subst z
        simp [derivative,qDelta,ha,character,bitSign_add]
        ring
      · have hsum : z+a≠0 := by
          intro he
          apply hza
          have he' := congrArg (fun w:Bits n=>w+a) he
          simpa [add_assoc] using he'
        simp [derivative,qDelta,hz,hza,hsum,character]
  unfold walsh
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ←Finset.mul_sum,←Finset.mul_sum,character_sum,ite_eq_right hh]
  simp [character,hd]
  norm_num

theorem delta_I_value {n : ℕ} {a b : Bits n} {c : ℂ} (hp : PullI a b c) (t : ℝ) :
    (pauliExpectation (raw qDelta (anglePhase t)) a b c).re=2 := by
  rw [raw_I_coeff qDelta (qDelta_zero n) hp,delta_walsh (a+b) hp.hh]
  simp [qDelta,hp.ha,coeffI,Trig.eval]

theorem delta_II_value {n : ℕ} {a b : Bits n} {c : ℂ} (hp : PullII a b c) (t : ℝ) :
    (pauliExpectation (raw qDelta (anglePhase t)) a b c).re=2 := by
  rw [raw_II_coeff qDelta (qDelta_zero n) hp,
    delta_derivative_walsh a (a+b) hp.ha hp.hh hp.hd]
  simp [qDelta,hp.ha,coeffII,Trig.eval]
  norm_num

end UnifiedEJM.BooleanLines
