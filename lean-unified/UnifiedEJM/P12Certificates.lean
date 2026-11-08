import UnifiedEJM.P12Block0000
import UnifiedEJM.P12Block0001
import UnifiedEJM.P12Block0002
import UnifiedEJM.P12Block0003
import UnifiedEJM.P12Block0010
import UnifiedEJM.P12Block0011
import UnifiedEJM.P12Block0012
import UnifiedEJM.P12Block0013
import UnifiedEJM.P12Block0020
import UnifiedEJM.P12Block0021
import UnifiedEJM.P12Block0022
import UnifiedEJM.P12Block0023
import UnifiedEJM.P12Block0030
import UnifiedEJM.P12Block0031
import UnifiedEJM.P12Block0032
import UnifiedEJM.P12Block0033
import UnifiedEJM.P12Block0100
import UnifiedEJM.P12Block0101
import UnifiedEJM.P12Block0102
import UnifiedEJM.P12Block0103
import UnifiedEJM.P12Block0110
import UnifiedEJM.P12Block0111
import UnifiedEJM.P12Block0112
import UnifiedEJM.P12Block0113
import UnifiedEJM.P12Block0120
import UnifiedEJM.P12Block0121
import UnifiedEJM.P12Block0122
import UnifiedEJM.P12Block0123
import UnifiedEJM.P12Block0130
import UnifiedEJM.P12Block0131
import UnifiedEJM.P12Block0132
import UnifiedEJM.P12Block0133
import UnifiedEJM.P12Block1000
import UnifiedEJM.P12Block1001
import UnifiedEJM.P12Block1002
import UnifiedEJM.P12Block1003
import UnifiedEJM.P12Block1010
import UnifiedEJM.P12Block1011
import UnifiedEJM.P12Block1012
import UnifiedEJM.P12Block1013
import UnifiedEJM.P12Block1020
import UnifiedEJM.P12Block1021
import UnifiedEJM.P12Block1022
import UnifiedEJM.P12Block1023
import UnifiedEJM.P12Block1030
import UnifiedEJM.P12Block1031
import UnifiedEJM.P12Block1032
import UnifiedEJM.P12Block1033
import UnifiedEJM.P12Block1100
import UnifiedEJM.P12Block1101
import UnifiedEJM.P12Block1102
import UnifiedEJM.P12Block1103
import UnifiedEJM.P12Block1110
import UnifiedEJM.P12Block1111
import UnifiedEJM.P12Block1112
import UnifiedEJM.P12Block1113
import UnifiedEJM.P12Block1120
import UnifiedEJM.P12Block1121
import UnifiedEJM.P12Block1122
import UnifiedEJM.P12Block1123
import UnifiedEJM.P12Block1130
import UnifiedEJM.P12Block1131
import UnifiedEJM.P12Block1132
import UnifiedEJM.P12Block1133
import UnifiedEJM.PrefixExpansion

open OddEJM UnifiedEJM.PhysicsFinite
open scoped BigOperators
namespace UnifiedEJM.PrefixKernel

def p12Expected : Fin 3 → Fin 5 → G :=
  ![![⟨-2,0⟩,⟨0,-32⟩,⟨60,0⟩,⟨0,32⟩,⟨-2,0⟩],
    ![⟨-32,0⟩,⟨-64,0⟩,⟨-64,0⟩,⟨-64,0⟩,⟨-32,0⟩],
    ![⟨256,0⟩,⟨1024,0⟩,⟨5632,0⟩,⟨1024,0⟩,⟨256,0⟩]]

/-- 只含已核验原块的字面expected表，不含原求和定义。 -/
def p12BlockExpected00 : Fin 4 → Fin 4 → Fin 3 → Fin 5 → G :=
  ![![P12Block0000.expected, P12Block0001.expected, P12Block0002.expected, P12Block0003.expected], ![P12Block0010.expected, P12Block0011.expected, P12Block0012.expected, P12Block0013.expected], ![P12Block0020.expected, P12Block0021.expected, P12Block0022.expected, P12Block0023.expected], ![P12Block0030.expected, P12Block0031.expected, P12Block0032.expected, P12Block0033.expected]]

/-- 在枚举求和下标前，先把任意f,s的原块替换为已证expected。 -/
theorem p12Block_expected00 (f s : Fin 4) (i : Fin 3) (k : Fin 5) :
    p12Block 0 false f s i k = p12BlockExpected00 f s i k := by
  fin_cases f <;> fin_cases s
  · exact P12Block0000.checked i k
  · exact P12Block0001.checked i k
  · exact P12Block0002.checked i k
  · exact P12Block0003.checked i k
  · exact P12Block0010.checked i k
  · exact P12Block0011.checked i k
  · exact P12Block0012.checked i k
  · exact P12Block0013.checked i k
  · exact P12Block0020.checked i k
  · exact P12Block0021.checked i k
  · exact P12Block0022.checked i k
  · exact P12Block0023.checked i k
  · exact P12Block0030.checked i k
  · exact P12Block0031.checked i k
  · exact P12Block0032.checked i k
  · exact P12Block0033.checked i k

/-- 这里只计算16张小expected表的和；内核归约不会到达p12Block。 -/
theorem p12BlockExpected00_sum (i : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, p12BlockExpected00 f s i k) = p12Expected i k := by
  revert i k
  decide +kernel

theorem p12Coeff_checked00 (i : Fin 3) (k : Fin 5) :
    p12Coeff 0 false i k = p12Expected i k := by
  rw [p12Coeff_blocks]
  simp only [p12Block_expected00]
  exact p12BlockExpected00_sum i k

/-- 只含已核验原块的字面expected表，不含原求和定义。 -/
def p12BlockExpected01 : Fin 4 → Fin 4 → Fin 3 → Fin 5 → G :=
  ![![P12Block0100.expected, P12Block0101.expected, P12Block0102.expected, P12Block0103.expected], ![P12Block0110.expected, P12Block0111.expected, P12Block0112.expected, P12Block0113.expected], ![P12Block0120.expected, P12Block0121.expected, P12Block0122.expected, P12Block0123.expected], ![P12Block0130.expected, P12Block0131.expected, P12Block0132.expected, P12Block0133.expected]]

/-- 在枚举求和下标前，先把任意f,s的原块替换为已证expected。 -/
theorem p12Block_expected01 (f s : Fin 4) (i : Fin 3) (k : Fin 5) :
    p12Block 0 true f s i k = p12BlockExpected01 f s i k := by
  fin_cases f <;> fin_cases s
  · exact P12Block0100.checked i k
  · exact P12Block0101.checked i k
  · exact P12Block0102.checked i k
  · exact P12Block0103.checked i k
  · exact P12Block0110.checked i k
  · exact P12Block0111.checked i k
  · exact P12Block0112.checked i k
  · exact P12Block0113.checked i k
  · exact P12Block0120.checked i k
  · exact P12Block0121.checked i k
  · exact P12Block0122.checked i k
  · exact P12Block0123.checked i k
  · exact P12Block0130.checked i k
  · exact P12Block0131.checked i k
  · exact P12Block0132.checked i k
  · exact P12Block0133.checked i k

/-- 这里只计算16张小expected表的和；内核归约不会到达p12Block。 -/
theorem p12BlockExpected01_sum (i : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, p12BlockExpected01 f s i k) = p12Expected i k := by
  revert i k
  decide +kernel

theorem p12Coeff_checked01 (i : Fin 3) (k : Fin 5) :
    p12Coeff 0 true i k = p12Expected i k := by
  rw [p12Coeff_blocks]
  simp only [p12Block_expected01]
  exact p12BlockExpected01_sum i k

/-- 只含已核验原块的字面expected表，不含原求和定义。 -/
def p12BlockExpected10 : Fin 4 → Fin 4 → Fin 3 → Fin 5 → G :=
  ![![P12Block1000.expected, P12Block1001.expected, P12Block1002.expected, P12Block1003.expected], ![P12Block1010.expected, P12Block1011.expected, P12Block1012.expected, P12Block1013.expected], ![P12Block1020.expected, P12Block1021.expected, P12Block1022.expected, P12Block1023.expected], ![P12Block1030.expected, P12Block1031.expected, P12Block1032.expected, P12Block1033.expected]]

/-- 在枚举求和下标前，先把任意f,s的原块替换为已证expected。 -/
theorem p12Block_expected10 (f s : Fin 4) (i : Fin 3) (k : Fin 5) :
    p12Block 1 false f s i k = p12BlockExpected10 f s i k := by
  fin_cases f <;> fin_cases s
  · exact P12Block1000.checked i k
  · exact P12Block1001.checked i k
  · exact P12Block1002.checked i k
  · exact P12Block1003.checked i k
  · exact P12Block1010.checked i k
  · exact P12Block1011.checked i k
  · exact P12Block1012.checked i k
  · exact P12Block1013.checked i k
  · exact P12Block1020.checked i k
  · exact P12Block1021.checked i k
  · exact P12Block1022.checked i k
  · exact P12Block1023.checked i k
  · exact P12Block1030.checked i k
  · exact P12Block1031.checked i k
  · exact P12Block1032.checked i k
  · exact P12Block1033.checked i k

/-- 这里只计算16张小expected表的和；内核归约不会到达p12Block。 -/
theorem p12BlockExpected10_sum (i : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, p12BlockExpected10 f s i k) = p12Expected i k := by
  revert i k
  decide +kernel

theorem p12Coeff_checked10 (i : Fin 3) (k : Fin 5) :
    p12Coeff 1 false i k = p12Expected i k := by
  rw [p12Coeff_blocks]
  simp only [p12Block_expected10]
  exact p12BlockExpected10_sum i k

/-- 只含已核验原块的字面expected表，不含原求和定义。 -/
def p12BlockExpected11 : Fin 4 → Fin 4 → Fin 3 → Fin 5 → G :=
  ![![P12Block1100.expected, P12Block1101.expected, P12Block1102.expected, P12Block1103.expected], ![P12Block1110.expected, P12Block1111.expected, P12Block1112.expected, P12Block1113.expected], ![P12Block1120.expected, P12Block1121.expected, P12Block1122.expected, P12Block1123.expected], ![P12Block1130.expected, P12Block1131.expected, P12Block1132.expected, P12Block1133.expected]]

/-- 在枚举求和下标前，先把任意f,s的原块替换为已证expected。 -/
theorem p12Block_expected11 (f s : Fin 4) (i : Fin 3) (k : Fin 5) :
    p12Block 1 true f s i k = p12BlockExpected11 f s i k := by
  fin_cases f <;> fin_cases s
  · exact P12Block1100.checked i k
  · exact P12Block1101.checked i k
  · exact P12Block1102.checked i k
  · exact P12Block1103.checked i k
  · exact P12Block1110.checked i k
  · exact P12Block1111.checked i k
  · exact P12Block1112.checked i k
  · exact P12Block1113.checked i k
  · exact P12Block1120.checked i k
  · exact P12Block1121.checked i k
  · exact P12Block1122.checked i k
  · exact P12Block1123.checked i k
  · exact P12Block1130.checked i k
  · exact P12Block1131.checked i k
  · exact P12Block1132.checked i k
  · exact P12Block1133.checked i k

/-- 这里只计算16张小expected表的和；内核归约不会到达p12Block。 -/
theorem p12BlockExpected11_sum (i : Fin 3) (k : Fin 5) :
    (∑ f : Fin 4, ∑ s : Fin 4, p12BlockExpected11 f s i k) = p12Expected i k := by
  revert i k
  decide +kernel

theorem p12Coeff_checked11 (i : Fin 3) (k : Fin 5) :
    p12Coeff 1 true i k = p12Expected i k := by
  rw [p12Coeff_blocks]
  simp only [p12Block_expected11]
  exact p12BlockExpected11_sum i k

theorem p12Coeff_checked (nu : Bit) (suffix : Bool) (i : Fin 3) (k : Fin 5) :
    p12Coeff nu suffix i k = p12Expected i k := by
  rcases bit_cases nu with rfl | rfl <;> cases suffix
  · exact p12Coeff_checked00 i k
  · exact p12Coeff_checked01 i k
  · exact p12Coeff_checked10 i k
  · exact p12Coeff_checked11 i k

/-- 全部整数K的精确Laurent系数恒等式，由64个原始有限sum证书推出。 -/
theorem p12Sum_checked (nu : Bit) (suffix : Bool) (K : ℤ) (k : Fin 5) :
    p12Sum nu suffix K k = p12Expected 0 k + (K : G) * p12Expected 1 k +
      (K : G)^2 * p12Expected 2 k := by
  rw [p12Sum_expansion]
  simp only [p12Coeff_checked]

#print axioms p12Coeff_checked
#print axioms p12Sum_checked
end UnifiedEJM.PrefixKernel
