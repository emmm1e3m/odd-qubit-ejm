import UnifiedEJM

/-! 统一检查论文的主要结论类型与实际传递公理，不引入额外假设。 -/

#check UnifiedEJM.unified_ejm_family
#check UnifiedEJM.measurement_actual_spectrum
#check UnifiedEJM.measurement_vonNeumann_entropy
#check UnifiedEJM.BooleanLines.original_four_laws
#check UnifiedEJM.BooleanLines.actual_boolean_model_exact_maximum
#check UnifiedEJM.EvenLow.even_cosine_family
#check UnifiedEJM.EvenFamily.ordered_measurement_parameter_injective
#check UnifiedEJM.SixFamily.actual_local_crossing
#check UnifiedEJM.SixFamily.geometric_local_crossing
#check UnifiedEJM.Physical.measurement_eq_original_gate_sequence
#check UnifiedEJM.SixFamily.direct_regular_iff
#check UnifiedEJM.ThreeQubit.geometric_three_qubit_rigidity
#check UnifiedEJM.LowDimensional.geometric_line_iff_planes
#check UnifiedEJM.LowDimensional.geometric_real_line_measurement_radius_bound
#check UnifiedEJM.Curved.curved_ejm_family
#check UnifiedEJM.Curved.radius_hasDerivAt_zero
#check UnifiedEJM.FiniteInvariants.real_line159_not_equivalent

-- 展示最易被弱化的几何、最优值和测量等价定义。
#print UnifiedEJM.Regularity.GeometricRegular
#print UnifiedEJM.BooleanLines.geometricRadiusValues
#print UnifiedEJM.BooleanLines.modelMaximum
#print UnifiedEJM.BipartiteInvariant.EquivalentMeasurements

-- 原门列、实际偏迹与所有维数的统一构造。
#print axioms UnifiedEJM.Physical.measurement_orthonormal
#print axioms UnifiedEJM.Physical.measurement_complete
#print axioms UnifiedEJM.Physical.measurement_eq_gate_column
#print axioms UnifiedEJM.Physical.measurement_eq_original_gate_sequence
#print axioms OddEJM.circuit_gate_order
#print axioms UnifiedEJM.Regularity.geometric_iff_seed_squares
#print axioms UnifiedEJM.Regularity.geometric_column_radius
#print axioms UnifiedEJM.F_branch
#print axioms UnifiedEJM.rawPhase_exp
#print axioms UnifiedEJM.phaseSupport_card
#print axioms UnifiedEJM.seed_localX
#print axioms UnifiedEJM.seed_localY
#print axioms UnifiedEJM.seed_localZ
#print axioms UnifiedEJM.unified_ejm_family
#print axioms UnifiedEJM.measurement_purity
#print axioms UnifiedEJM.measurement_reduced_multiplicity
#print axioms UnifiedEJM.measurement_maximally_mixed
#print axioms UnifiedEJM.measurement_projector_continuous
#print axioms UnifiedEJM.measurement_actual_spectrum
#print axioms UnifiedEJM.measurement_vonNeumann_entropy
#print axioms UnifiedEJM.measurement_entropy_strictMonoOn
#print axioms UnifiedEJM.measurement_entropy_at_right

-- 模型内精确界和真实二维包含。
#print axioms UnifiedEJM.BooleanLines.original_four_laws
#print axioms UnifiedEJM.BooleanLines.two_rate_phase
#print axioms UnifiedEJM.BooleanLines.regular_global_measurement
#print axioms UnifiedEJM.BooleanLines.actual_all_column_radius
#print axioms UnifiedEJM.BooleanLines.locally_regular_iff_geometric
#print axioms UnifiedEJM.BooleanLines.actual_boolean_model_exact_maximum
#print axioms UnifiedEJM.EvenLow.even_cosine_family
#print axioms UnifiedEJM.EvenLow.qA_two
#print axioms UnifiedEJM.EvenLow.qA_four
#print axioms UnifiedEJM.EvenFamily.measurement_reduced
#print axioms UnifiedEJM.EvenFamily.measurement_orthonormal
#print axioms UnifiedEJM.EvenFamily.measurement_complete
#print axioms UnifiedEJM.EvenEmbedding.radius_image_exact
#print axioms UnifiedEJM.EvenFamily.first_axis_measurement
#print axioms UnifiedEJM.EvenFamily.second_axis_measurement
#print axioms UnifiedEJM.EvenFamily.ordered_measurement_parameter_injective
#print axioms UnifiedEJM.SixFamily.actual_local_crossing
#print axioms UnifiedEJM.SixFamily.geometric_iff_actual_of_pos
#print axioms UnifiedEJM.SixFamily.eventually_total_pos
#print axioms UnifiedEJM.SixFamily.geometric_local_crossing
#print axioms UnifiedEJM.SixFamily.measurement_reduced_of_regular
#print axioms UnifiedEJM.SixFamily.regular_component_positive
#print axioms UnifiedEJM.SixFamily.direct_regular_iff

-- 低维完整物理链和曲线初始斜率。
#print axioms UnifiedEJM.ThreeQubit.expectation_eq_physical
#print axioms UnifiedEJM.ThreeQubit.residual_derivative
#print axioms UnifiedEJM.ThreeQubit.derivative_determinant
#print axioms UnifiedEJM.ThreeQubit.geometric_three_qubit_rigidity
#print axioms UnifiedEJM.LowDimensional.physical_regular_iff_planes
#print axioms UnifiedEJM.LowDimensional.geometric_line_iff_planes
#print axioms UnifiedEJM.LowDimensional.geometric_real_line_measurement_radius_bound
#print axioms UnifiedEJM.Curved.curved_ejm_family
#print axioms UnifiedEJM.Curved.measurement_purity
#print axioms UnifiedEJM.Curved.measurement_multiplicity
#print axioms UnifiedEJM.Curved.paperDelta_hasDerivAt_zero
#print axioms UnifiedEJM.Curved.q_hasDerivAt_zero
#print axioms UnifiedEJM.Curved.radius_hasDerivAt_zero

-- 原始四比特测量、实际张量局域酉及所有置换。
#print axioms UnifiedEJM.FiniteInvariants.state159_actual_seed
#print axioms UnifiedEJM.FiniteInvariants.stateBase_actual_seed
#print axioms UnifiedEJM.FiniteInvariants.line_pair_purity
#print axioms UnifiedEJM.FiniteInvariants.line_single_purity
#print axioms UnifiedEJM.FiniteInvariants.base_pair_purity
#print axioms UnifiedEJM.FiniteInvariants.base_single_purity
#print axioms UnifiedEJM.BipartiteInvariant.sumPurity_localAction
#print axioms UnifiedEJM.BipartiteInvariant.sumPurity_permute
#print axioms UnifiedEJM.BipartiteInvariant.singlePuritySum_localAction
#print axioms UnifiedEJM.BipartiteInvariant.singlePuritySum_permute
#print axioms UnifiedEJM.Physical.measurement_tensor_fin16
#print axioms UnifiedEJM.BipartiteInvariant.sumPurity_measurement_columns
#print axioms UnifiedEJM.BipartiteInvariant.singlePuritySum_measurement_columns
#print axioms UnifiedEJM.BipartiteInvariant.equivalent_measurements_invariants
#print axioms UnifiedEJM.Inequivalence.resultant_nonzero
#print axioms UnifiedEJM.FiniteInvariants.no_matching_actual_invariants
#print axioms UnifiedEJM.FiniteInvariants.measurements159_not_equivalent
#print axioms UnifiedEJM.FiniteInvariants.real_line159_not_equivalent
#print axioms UnifiedEJM.FiniteInvariants.line159_measurement_orthonormal
