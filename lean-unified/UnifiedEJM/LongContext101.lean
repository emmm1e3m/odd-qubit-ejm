import UnifiedEJM.PrefixEndpointContext

open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongContext101

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights0 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights0_checked :
    collectWeights (longBlockContextList (some 0) none 1 0) = weights0 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights1 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (26, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (28, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (16, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (22, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights1_checked :
    collectWeights (longBlockContextList (some 0) none 1 1) = weights1 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights2 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (41, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (32, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights2_checked :
    collectWeights (longBlockContextList (some 0) none 1 2) = weights2 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights3 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (41, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (32, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (44, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (26, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (28, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (60, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (16, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (22, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights3_checked :
    collectWeights (longBlockContextList (some 0) none 1 3) = weights3 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights4 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (73, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (64, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights4_checked :
    collectWeights (longBlockContextList (some 0) none 1 4) = weights4 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights6 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (105, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (96, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights6_checked :
    collectWeights (longBlockContextList (some 0) none 1 6) = weights6 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights8 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (133, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (131, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (128, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (134, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights8_checked :
    collectWeights (longBlockContextList (some 0) none 1 8) = weights8 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights9 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (133, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (131, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (26, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (28, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (144, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (150, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights9_checked :
    collectWeights (longBlockContextList (some 0) none 1 9) = weights9 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights12 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (73, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (64, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (67, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (133, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (131, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (195, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (128, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (134, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights12_checked :
    collectWeights (longBlockContextList (some 0) none 1 12) = weights12 := by
  decide +kernel

def weights (s p l : Fin 4) : List (ℕ × WeightData) :=
  ![![![weights9, weights1, weights8, weights0], ![weights1, weights1, weights0, weights0], ![weights8, weights0, weights8, weights0], ![weights0, weights0, weights0, weights0]], ![![weights9, weights1, weights8, weights0], ![weights1, weights3, weights0, weights2], ![weights8, weights0, weights12, weights4], ![weights0, weights2, weights4, weights6]], ![![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0]], ![![weights0, weights0, weights0, weights0], ![weights0, weights2, weights0, weights2], ![weights0, weights0, weights4, weights4], ![weights0, weights2, weights4, weights6]]] s p l

/-- 64个实际端点组合只做四位上下文判定，复用上述已证表。 -/
theorem weights_checked (s p l : Fin 4) :
    collectWeights (longBlockCodeClassList (some 0) none 1 s p l) = weights s p l := by
  rw [longBlockCodeClassList_eq_context]
  fin_cases s <;> fin_cases p <;> fin_cases l
  · exact weights9_checked
  · exact weights1_checked
  · exact weights8_checked
  · exact weights0_checked
  · exact weights1_checked
  · exact weights1_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights8_checked
  · exact weights0_checked
  · exact weights8_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights9_checked
  · exact weights1_checked
  · exact weights8_checked
  · exact weights0_checked
  · exact weights1_checked
  · exact weights3_checked
  · exact weights0_checked
  · exact weights2_checked
  · exact weights8_checked
  · exact weights0_checked
  · exact weights12_checked
  · exact weights4_checked
  · exact weights0_checked
  · exact weights2_checked
  · exact weights4_checked
  · exact weights6_checked
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
  · exact weights2_checked
  · exact weights0_checked
  · exact weights2_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights4_checked
  · exact weights4_checked
  · exact weights0_checked
  · exact weights2_checked
  · exact weights4_checked
  · exact weights6_checked

#print axioms weights_checked

end UnifiedEJM.PrefixKernel.LongContext101



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1010

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-6, -12⟩, ⟨8, -12⟩, ⟨12, 0⟩, ⟨8, 12⟩, ⟨-6, 12⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨144, -32⟩, ⟨384, 64⟩, ⟨992, 0⟩, ⟨384, -64⟩, ⟨144, 32⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-6, -12⟩ : G), (⟨8, -12⟩ : G), (⟨12, 0⟩ : G), (⟨8, 12⟩ : G), (⟨-6, 12⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨144, -32⟩ : G), (⟨384, 64⟩ : G), (⟨992, 0⟩ : G), (⟨384, -64⟩ : G), (⟨144, 32⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 1 0 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext101.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 1 0 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1010



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1011

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-8, 4⟩, ⟨-16, 16⟩, ⟨-48, 0⟩, ⟨-16, -16⟩, ⟨-8, -4⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨176, 0⟩, ⟨256, 0⟩, ⟨1184, 0⟩, ⟨256, 0⟩, ⟨176, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-8, 4⟩ : G), (⟨-16, 16⟩ : G), (⟨-48, 0⟩ : G), (⟨-16, -16⟩ : G), (⟨-8, -4⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨176, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1184, 0⟩ : G), (⟨256, 0⟩ : G), (⟨176, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 1 1 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext101.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 1 1 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1011



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1012

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨176, 0⟩, ⟨256, 0⟩, ⟨1184, 0⟩, ⟨256, 0⟩, ⟨176, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨176, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1184, 0⟩ : G), (⟨256, 0⟩ : G), (⟨176, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 1 2 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext101.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 1 2 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1012



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1013

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-10, 8⟩, ⟨-24, 12⟩, ⟨-44, 0⟩, ⟨-24, -12⟩, ⟨-10, -8⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨144, 32⟩, ⟨384, -64⟩, ⟨992, 0⟩, ⟨384, 64⟩, ⟨144, -32⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-10, 8⟩ : G), (⟨-24, 12⟩ : G), (⟨-44, 0⟩ : G), (⟨-24, -12⟩ : G), (⟨-10, -8⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨144, 32⟩ : G), (⟨384, -64⟩ : G), (⟨992, 0⟩ : G), (⟨384, 64⟩ : G), (⟨144, -32⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 1 3 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext101.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 1 3 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1013
