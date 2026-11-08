import UnifiedEJM.PrefixEndpointContext

open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongContext222

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights0 : List (ℕ × WeightData) :=
  [(0, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, 0, 0), (0, 0, 16)))]

theorem weights0_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 0) = weights0 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights1 : List (ℕ × WeightData) :=
  [(0, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (16, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (26, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (22, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (28, ((0, 0, 0), (0, 2, 0), (0, 0, 0)))]

theorem weights1_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 1) = weights1 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights2 : List (ℕ × WeightData) :=
  [(0, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (32, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (41, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 2, 0), (0, 0, 0)))]

theorem weights2_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 2) = weights2 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights3 : List (ℕ × WeightData) :=
  [(0, ((-1, 0, 0), (0, -4, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, -4, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (16, ((1, 0, 0), (0, 2, 0), (0, 0, 0))),
   (26, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (22, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (28, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (32, ((1, 0, 0), (0, 2, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (41, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (48, ((-1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights3_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 3) = weights3 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights4 : List (ℕ × WeightData) :=
  [(0, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (64, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (73, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 2, 0), (0, 0, 0)))]

theorem weights4_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 4) = weights4 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights6 : List (ℕ × WeightData) :=
  [(0, ((0, 0, 0), (2, -4, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (2, -4, 0), (0, 0, 16))),
   (32, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (41, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (64, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (73, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (96, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (105, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights6_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 6) = weights6 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights8 : List (ℕ × WeightData) :=
  [(0, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (128, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (133, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (134, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (131, ((0, 0, 0), (0, 2, 0), (0, 0, 0)))]

theorem weights8_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 8) = weights8 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights9 : List (ℕ × WeightData) :=
  [(0, ((0, 0, 0), (2, -4, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (2, -4, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (128, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (133, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (16, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (26, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (144, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (134, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (131, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (22, ((0, 0, 0), (-2, 2, 0), (0, 0, 0))),
   (28, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (150, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights9_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 9) = weights9 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights12 : List (ℕ × WeightData) :=
  [(0, ((-1, 0, 0), (0, -4, 0), (0, 0, 16))),
   (10, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (5, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (15, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (6, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 16))),
   (3, ((0, 0, 0), (0, -4, 0), (0, 0, 16))),
   (9, ((0, 0, 0), (0, -2, 0), (0, 0, 16))),
   (128, ((1, 0, 0), (0, 2, 0), (0, 0, 0))),
   (133, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (134, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (131, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (64, ((1, 0, 0), (0, 2, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (73, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 2, 0), (0, 0, 0))),
   (192, ((-1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights12_checked :
    collectWeights (longBlockContextList (some 1) (some 1) 2 12) = weights12 := by
  decide +kernel

def weights (s p l : Fin 4) : List (ℕ × WeightData) :=
  ![![![weights6, weights4, weights2, weights0], ![weights4, weights4, weights0, weights0], ![weights2, weights0, weights2, weights0], ![weights0, weights0, weights0, weights0]], ![![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0]], ![![weights6, weights4, weights2, weights0], ![weights4, weights12, weights0, weights8], ![weights2, weights0, weights3, weights1], ![weights0, weights8, weights1, weights9]], ![![weights0, weights0, weights0, weights0], ![weights0, weights8, weights0, weights8], ![weights0, weights0, weights1, weights1], ![weights0, weights8, weights1, weights9]]] s p l

/-- 64个实际端点组合只做四位上下文判定，复用上述已证表。 -/
theorem weights_checked (s p l : Fin 4) :
    collectWeights (longBlockCodeClassList (some 1) (some 1) 2 s p l) = weights s p l := by
  rw [longBlockCodeClassList_eq_context]
  fin_cases s <;> fin_cases p <;> fin_cases l
  · exact weights6_checked
  · exact weights4_checked
  · exact weights2_checked
  · exact weights0_checked
  · exact weights4_checked
  · exact weights4_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights2_checked
  · exact weights0_checked
  · exact weights2_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights6_checked
  · exact weights4_checked
  · exact weights2_checked
  · exact weights0_checked
  · exact weights4_checked
  · exact weights12_checked
  · exact weights0_checked
  · exact weights8_checked
  · exact weights2_checked
  · exact weights0_checked
  · exact weights3_checked
  · exact weights1_checked
  · exact weights0_checked
  · exact weights8_checked
  · exact weights1_checked
  · exact weights9_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights8_checked
  · exact weights0_checked
  · exact weights8_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights1_checked
  · exact weights1_checked
  · exact weights0_checked
  · exact weights8_checked
  · exact weights1_checked
  · exact weights9_checked

#print axioms weights_checked

end UnifiedEJM.PrefixKernel.LongContext222



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2220

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-2, 0⟩, ⟨0, -12⟩, ⟨20, 0⟩, ⟨0, 12⟩, ⟨-2, 0⟩], ![⟨-8, -8⟩, ⟨0, -16⟩, ⟨16, 0⟩, ⟨0, 16⟩, ⟨-8, 8⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨832, 0⟩, ⟨1792, 0⟩, ⟨2944, 0⟩, ⟨1792, 0⟩, ⟨832, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-2, 0⟩ : G), (⟨0, -12⟩ : G), (⟨20, 0⟩ : G), (⟨0, 12⟩ : G), (⟨-2, 0⟩ : G)), ((⟨-8, -8⟩ : G), (⟨0, -16⟩ : G), (⟨16, 0⟩ : G), (⟨0, 16⟩ : G), (⟨-8, 8⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨832, 0⟩ : G), (⟨1792, 0⟩ : G), (⟨2944, 0⟩ : G), (⟨1792, 0⟩ : G), (⟨832, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) (some 1) 2 0 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext222.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) (some 1) 2 0 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2220



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2221

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨896, 0⟩, ⟨1536, 0⟩, ⟨3328, 0⟩, ⟨1536, 0⟩, ⟨896, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨896, 0⟩ : G), (⟨1536, 0⟩ : G), (⟨3328, 0⟩ : G), (⟨1536, 0⟩ : G), (⟨896, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) (some 1) 2 1 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext222.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) (some 1) 2 1 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2221



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2222

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, -16⟩, ⟨32, 0⟩, ⟨0, 16⟩, ⟨0, 0⟩], ![⟨-24, 24⟩, ⟨-64, 16⟩, ⟨-80, 0⟩, ⟨-64, -16⟩, ⟨-24, -24⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨896, 0⟩, ⟨1536, 0⟩, ⟨3328, 0⟩, ⟨1536, 0⟩, ⟨896, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, -16⟩ : G), (⟨32, 0⟩ : G), (⟨0, 16⟩ : G), (⟨0, 0⟩ : G)), ((⟨-24, 24⟩ : G), (⟨-64, 16⟩ : G), (⟨-80, 0⟩ : G), (⟨-64, -16⟩ : G), (⟨-24, -24⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨896, 0⟩ : G), (⟨1536, 0⟩ : G), (⟨3328, 0⟩ : G), (⟨1536, 0⟩ : G), (⟨896, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) (some 1) 2 2 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext222.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) (some 1) 2 2 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2222



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2223

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨2, 0⟩, ⟨0, -4⟩, ⟨12, 0⟩, ⟨0, 4⟩, ⟨2, 0⟩], ![⟨-32, 8⟩, ⟨-48, 16⟩, ⟨-96, 0⟩, ⟨-48, -16⟩, ⟨-32, -8⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨832, 0⟩, ⟨1792, 0⟩, ⟨2944, 0⟩, ⟨1792, 0⟩, ⟨832, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨2, 0⟩ : G), (⟨0, -4⟩ : G), (⟨12, 0⟩ : G), (⟨0, 4⟩ : G), (⟨2, 0⟩ : G)), ((⟨-32, 8⟩ : G), (⟨-48, 16⟩ : G), (⟨-96, 0⟩ : G), (⟨-48, -16⟩ : G), (⟨-32, -8⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨832, 0⟩ : G), (⟨1792, 0⟩ : G), (⟨2944, 0⟩ : G), (⟨1792, 0⟩ : G), (⟨832, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) (some 1) 2 3 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext222.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) (some 1) 2 3 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2223
