import OddEJM

/- 显示最终定理的全部参数，并审计传递依赖中的公理。 -/
#check @OddEJM.odd_ejm_family
#check @OddEJM.measurement_reduced
#check @OddEJM.measurement_purity
#print axioms OddEJM.odd_ejm_family
#print axioms OddEJM.measurement_reduced
#print axioms OddEJM.measurement_purity
#print axioms OddEJM.measurement_maximally_mixed
#print axioms OddEJM.measurement_complete
#print axioms OddEJM.rawPhase_eq_originalDiagonal
#print axioms OddEJM.measurement_basepoint_original
#print axioms OddEJM.seed_localX
#print axioms OddEJM.seed_localY
#print axioms OddEJM.seed_localZ
#print axioms OddEJM.circuit_gate_order
#print axioms OddEJM.measurement_eq_gate_column
#print axioms OddEJM.localOutcome_fiber_card

#print axioms OddEJM.measurement_reduced_multiplicity
#print axioms OddEJM.measurement_eigenvalues
#print axioms OddEJM.measurement_original_phase
