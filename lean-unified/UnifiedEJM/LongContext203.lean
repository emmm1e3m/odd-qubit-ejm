import UnifiedEJM.PrefixEndpointContext

open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongContext203

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
    collectWeights (longBlockContextList (some 1) none 3 0) = weights0 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights1 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (31, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (25, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (21, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (19, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights1_checked :
    collectWeights (longBlockContextList (some 1) none 3 1) = weights1 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights2 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (47, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (38, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (42, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (35, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights2_checked :
    collectWeights (longBlockContextList (some 1) none 3 2) = weights2 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights4 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (79, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (70, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (69, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (76, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights4_checked :
    collectWeights (longBlockContextList (some 1) none 3 4) = weights4 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights5 : List (ℕ × WeightData) :=
  [(15, ((1, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (79, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (70, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (31, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (25, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (95, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (5, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (69, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (76, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (21, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (19, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (85, ((1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights5_checked :
    collectWeights (longBlockContextList (some 1) none 3 5) = weights5 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights6 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (111, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (102, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (69, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (76, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (42, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (35, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights6_checked :
    collectWeights (longBlockContextList (some 1) none 3 6) = weights6 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights8 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (143, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (137, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (138, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (140, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights8_checked :
    collectWeights (longBlockContextList (some 1) none 3 8) = weights8 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights9 : List (ℕ × WeightData) :=
  [(15, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (6, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (159, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (153, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (21, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (19, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (138, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (140, ((0, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights9_checked :
    collectWeights (longBlockContextList (some 1) none 3 9) = weights9 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights10 : List (ℕ × WeightData) :=
  [(15, ((1, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (47, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (38, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (143, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (137, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (175, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (5, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (42, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (35, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (138, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (140, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (170, ((1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights10_checked :
    collectWeights (longBlockContextList (some 1) none 3 10) = weights10 := by
  decide +kernel

/-- 该上下文的整数表由原4096类收集直接核验。 -/
def weights15 : List (ℕ × WeightData) :=
  [(15, ((1, 0, 0), (-4, 0, 0), (8, 0, 0))),
   (9, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (111, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (6, ((0, 0, 0), (-2, 0, 0), (8, 0, 0))),
   (0, ((0, 0, 0), (0, 0, 0), (8, 0, 0))),
   (102, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (159, ((-1, 0, 0), (2, 0, 0), (0, 0, 0))),
   (153, ((0, 0, 0), (2, 0, 0), (0, 0, 0))),
   (255, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (5, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (3, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (69, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (12, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (10, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (76, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (21, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (19, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (85, ((1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (42, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (35, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (138, ((-1, 0, 0), (0, 0, 0), (0, 0, 0))),
   (140, ((0, 0, 0), (0, 0, 0), (0, 0, 0))),
   (170, ((1, 0, 0), (0, 0, 0), (0, 0, 0)))]

theorem weights15_checked :
    collectWeights (longBlockContextList (some 1) none 3 15) = weights15 := by
  decide +kernel

def weights (s p l : Fin 4) : List (ℕ × WeightData) :=
  ![![![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0], ![weights0, weights0, weights0, weights0]], ![![weights0, weights0, weights0, weights0], ![weights0, weights2, weights0, weights2], ![weights0, weights0, weights4, weights4], ![weights0, weights2, weights4, weights6]], ![![weights0, weights0, weights0, weights0], ![weights0, weights8, weights0, weights8], ![weights0, weights0, weights1, weights1], ![weights0, weights8, weights1, weights9]], ![![weights0, weights0, weights0, weights0], ![weights0, weights10, weights0, weights10], ![weights0, weights0, weights5, weights5], ![weights0, weights10, weights5, weights15]]] s p l

/-- 64个实际端点组合只做四位上下文判定，复用上述已证表。 -/
theorem weights_checked (s p l : Fin 4) :
    collectWeights (longBlockCodeClassList (some 1) none 3 s p l) = weights s p l := by
  rw [longBlockCodeClassList_eq_context]
  fin_cases s <;> fin_cases p <;> fin_cases l
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
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights10_checked
  · exact weights0_checked
  · exact weights10_checked
  · exact weights0_checked
  · exact weights0_checked
  · exact weights5_checked
  · exact weights5_checked
  · exact weights0_checked
  · exact weights10_checked
  · exact weights5_checked
  · exact weights15_checked

#print axioms weights_checked

end UnifiedEJM.PrefixKernel.LongContext203



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2030

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨48, 0⟩, ⟨256, 0⟩, ⟨1440, 0⟩, ⟨256, 0⟩, ⟨48, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨48, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1440, 0⟩ : G), (⟨256, 0⟩ : G), (⟨48, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) none 3 0 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext203.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) none 3 0 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2030



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2031

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-10, 2⟩, ⟨-16, 20⟩, ⟨-60, 0⟩, ⟨-16, -20⟩, ⟨-10, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨112, 0⟩, ⟨256, 0⟩, ⟨1312, 0⟩, ⟨256, 0⟩, ⟨112, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-10, 2⟩ : G), (⟨-16, 20⟩ : G), (⟨-60, 0⟩ : G), (⟨-16, -20⟩ : G), (⟨-10, -2⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨112, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1312, 0⟩ : G), (⟨256, 0⟩ : G), (⟨112, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) none 3 1 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext203.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) none 3 1 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2031



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2032

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-10, 2⟩, ⟨-16, 20⟩, ⟨-60, 0⟩, ⟨-16, -20⟩, ⟨-10, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨112, 0⟩, ⟨256, 0⟩, ⟨1312, 0⟩, ⟨256, 0⟩, ⟨112, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-10, 2⟩ : G), (⟨-16, 20⟩ : G), (⟨-60, 0⟩ : G), (⟨-16, -20⟩ : G), (⟨-10, -2⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨112, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1312, 0⟩ : G), (⟨256, 0⟩ : G), (⟨112, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) none 3 2 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext203.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) none 3 2 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2032



open OddEJM UnifiedEJM.PhysicsFinite UnifiedEJM.PrefixKernel
open scoped BigOperators

namespace UnifiedEJM.PrefixKernel.LongBlock2033

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

def expected : Fin 3 → Fin 3 → Fin 5 → G := ![![![⟨1, 0⟩, ⟨0, -28⟩, ⟨58, 0⟩, ⟨0, 28⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-8, 4⟩, ⟨-32, 64⟩, ⟨-144, 0⟩, ⟨-32, -64⟩, ⟨-8, -4⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨48, 0⟩, ⟨256, 0⟩, ⟨1440, 0⟩, ⟨256, 0⟩, ⟨48, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def expectedData : Data45 := ((((⟨1, 0⟩ : G), (⟨0, -28⟩ : G), (⟨58, 0⟩ : G), (⟨0, 28⟩ : G), (⟨1, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨-8, 4⟩ : G), (⟨-32, 64⟩ : G), (⟨-144, 0⟩ : G), (⟨-32, -64⟩ : G), (⟨-8, -4⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))), (((⟨48, 0⟩ : G), (⟨256, 0⟩ : G), (⟨1440, 0⟩ : G), (⟨256, 0⟩ : G), (⟨48, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G)), ((⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G), (⟨0, 0⟩ : G))))

/-- 权重收集已经由共享表证书完成，此处只评价实际端点的H。 -/
theorem checkedData : longBlockCodeData (some 1) none 3 3 = expectedData := by
  unfold longBlockCodeData
  simp only [LongContext203.weights_checked]
  decide +kernel

theorem checked (i j : Fin 3) (k : Fin 5) :
    longBlock (some 1) none 3 3 i j k = expected i j k := by
  rw [← longBlockCodeData_spec, checkedData]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

#print axioms checked

end UnifiedEJM.PrefixKernel.LongBlock2033
