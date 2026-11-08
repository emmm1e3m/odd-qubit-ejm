import UnifiedEJM.PrefixEndpointContext

open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongContext100

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
    collectWeights (longBlockContextList (some 0) none 0 0) = weights0 := by
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
    collectWeights (longBlockContextList (some 0) none 0 1) = weights1 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights2 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (32, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (41, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights2_checked :
    collectWeights (longBlockContextList (some 0) none 0 2) = weights2 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights4 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (64, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (73, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights4_checked :
    collectWeights (longBlockContextList (some 0) none 0 4) = weights4 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights5 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((1, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (74, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (64, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (73, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (26, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (28, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (16, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (22, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (90, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (80, ((1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights5_checked :
    collectWeights (longBlockContextList (some 0) none 0 5) = weights5 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights6 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (37, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (74, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (96, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (105, ((0, 0, 0), (2, 0, 0), (0, 0, 0)))]

theorem weights6_checked :
    collectWeights (longBlockContextList (some 0) none 0 6) = weights6 := by
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
    collectWeights (longBlockContextList (some 0) none 0 8) = weights8 := by
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
    collectWeights (longBlockContextList (some 0) none 0 9) = weights9 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights10 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((1, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (5, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (37, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (32, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (41, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (133, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (131, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (128, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (134, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (165, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (160, ((1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights10_checked :
    collectWeights (longBlockContextList (some 0) none 0 10) = weights10 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights15 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((1, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (5, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (37, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (44, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (74, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (67, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (96, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (105, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (133, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (131, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (26, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (28, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (144, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (150, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (165, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (90, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (240, ((1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights15_checked :
    collectWeights (longBlockContextList (some 0) none 0 15) = weights15 := by
  decide +kernel

def weights (s p l : Fin 4) : List (ℕ × WeightData) :=
  ![![![weights15, weights5, weights10, weights0], ![weights5, weights5, weights0, weights0], ![weights10, weights0, weights10, weights0], ![weights0, weights0, weights0, weights0]], ![![weights9, weights1, weights8, weights0], ![weights1, weights1, weights0, weights0], ![weights8, weights0, weights8, weights0], ![weights0, weights0, weights0, weights0]], ![![weights6, weights4, weights2, weights0], ![weights4, weights4, weights0, weights0], ![weights2, weights0, weights2, weights0], ![weights0, weights0, weights0, weights0]], ![![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0]]] s p l

/-- 64个实际端点组合只做四位上下文判定，复用上述已证表。 -/
theorem weights_checked (s p l : Fin 4) :
    collectWeights (longBlockCodeClassList (some 0) none 0 s p l) = weights s p l := by
  rw [longBlockCodeClassList_eq_context]
  fin_cases s <;> fin_cases p <;> fin_cases l
  · exact weights15_checked
  · exact weights5_checked
  · exact weights10_checked
  · exact weights0_checked
  · exact weights5_checked
  · exact weights5_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights10_checked
  · exact weights0_checked
  · exact weights10_checked
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

#print axioms weights_checked

end UnifiedEJM.PrefixKernel.LongContext100



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1000

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨-3, 0⟩, ⟨0, -36⟩, ⟨66, 0⟩, ⟨0, 36⟩, ⟨-3, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨8, 4⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨8, -4⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-16, 0⟩, ⟨256, 0⟩, ⟨1568, 0⟩, ⟨256, 0⟩, ⟨-16, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨-3, 0⟩ : G), (⟨0, -36⟩ : G), (⟨66, 0⟩ : G), (⟨0, 36⟩ : G), (⟨-3, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨8, 4⟩ : G), (⟨0, 0⟩ : G), (⟨16, 0⟩ : G), (⟨0, 0⟩ : G), (⟨8, -4⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-16, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1568, 0⟩ : G), (⟨256, 0⟩ : G), (⟨-16, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 0 0 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext100.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 0 0 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1000



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1001

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨2, 6⟩, ⟨8, 4⟩, ⟨-4, 0⟩, ⟨8, -4⟩, ⟨2, -6⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨16, 0⟩, ⟨384, 0⟩, ⟨1248, 0⟩, ⟨384, 0⟩, ⟨16, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨2, 6⟩ : G), (⟨8, 4⟩ : G), (⟨-4, 0⟩ : G), (⟨8, -4⟩ : G), (⟨2, -6⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨16, 0⟩ : G), (⟨384, 0⟩ : G), (⟨1248, 0⟩ : G), (⟨384, 0⟩ : G), (⟨16, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 0 1 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext100.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 0 1 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1001



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1002

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨2, 6⟩, ⟨8, 4⟩, ⟨-4, 0⟩, ⟨8, -4⟩, ⟨2, -6⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨16, 0⟩, ⟨384, 0⟩, ⟨1248, 0⟩, ⟨384, 0⟩, ⟨16, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨2, 6⟩ : G), (⟨8, 4⟩ : G), (⟨-4, 0⟩ : G), (⟨8, -4⟩ : G), (⟨2, -6⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨16, 0⟩ : G), (⟨384, 0⟩ : G), (⟨1248, 0⟩ : G), (⟨384, 0⟩ : G), (⟨16, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 0 2 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext100.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 0 2 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1002



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock1003

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-16, 0⟩, ⟨256, 0⟩, ⟨1568, 0⟩, ⟨256, 0⟩, ⟨-16, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-16, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1568, 0⟩ : G), (⟨256, 0⟩ : G), (⟨-16, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 0) none 0 3 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext100.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 0) none 0 3 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock1003
