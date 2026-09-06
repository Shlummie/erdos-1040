import Erdos1040.Basic
import Erdos1040.Unbounded
import Erdos1040.LogKernel
import Erdos1040.AtomicPotential
import Erdos1040.AreaTransfer
import Erdos1040.LogContinuity
import Erdos1040.AdjointPotential
import Erdos1040.AtomicApproximation
import Erdos1040.DiscretePotential
import Erdos1040.ExteriorKernel
import Erdos1040.CircleMean
import Erdos1040.SimultaneousApproximation
import Erdos1040.AdjointCircleMean
import Erdos1040.SourcePotential
import Erdos1040.HarmonicMaximum
import Erdos1040.PotentialAsymptotics
import Erdos1040.SourceDensity
import Erdos1040.CapPolynomial
import Erdos1040.PotentialHarmonic
import Erdos1040.PotentialMoments
import Erdos1040.DensityOperator
import Erdos1040.CapRotation
import Erdos1040.AdjointUniqueness
import Erdos1040.LogEnergy
import Erdos1040.PolynomialDensity
import Erdos1040.PositiveDensity
import Erdos1040.AtomicAreaAssembly
import Erdos1040.LogEnergyIntegrability
import Erdos1040.EnergyVariation
import Erdos1040.ConditionalLemniscate
import Erdos1040.LogEnergyScale
import Erdos1040.EnergyFrostman
import Erdos1040.TruncatedEnergy
import Erdos1040.EmpiricalEnergy
import Erdos1040.GeometricDiameter
import Erdos1040.GlobalFrostman
import Erdos1040.SourceSupport
import Erdos1040.FilledHull
import Erdos1040.EnergyDiameter
import Erdos1040.PolynomialConclusion
import Erdos1040.ExteriorPositivity
import Erdos1040.NonnegativePotentialLemniscate
import Erdos1040.CompactLemniscate
import Erdos1040.FullTheorem
import Erdos1040.GeometricDiameterLimit
import Erdos1040.LogarithmicCapacity
import Erdos1040.CapacityTheorem

import Erdos1040.AreaInfimumEndpoints
import Erdos1040.AreaObstruction
import Erdos1040.CapacityDependence
import Erdos1040.CountableSources
import Erdos1040.GeometricScaling

/-!
# Admitted Erdős #1040 core

Admission: formal/admissions/2026-09-05-erdos1040-complete.json.
The original 210 theorems and 30 definitions below passed source, build, dependency,
axiom and independent version-bound correspondence gates before admission.
Both exact targets E1040-CAP1 and E1040-FULL passed the complete gate.
This index introduces no assumptions. No P versus NP claim is admitted.

* `Erdos1040.rootPolynomial` (E1040-ROOT-POLYNOMIAL).
* `Erdos1040.unitLemniscate` (E1040-FULL).
* `Erdos1040.HasArbitrarilySmallLemniscates` (E1040-FULL).
* `Erdos1040.rootPolynomial_monic` (E1040-ROOT-POLYNOMIAL).
* `Erdos1040.rootPolynomial_eval` (E1040-ROOT-POLYNOMIAL).
* `Erdos1040.rootPolynomial_natDegree` (E1040-ROOT-POLYNOMIAL).
* `Erdos1040.rootPolynomial_isRoot_iff` (E1040-ROOT-POLYNOMIAL).
* `Erdos1040.quadratic_sublevel_subset_balls` (E1040-UNBOUNDED).
* `Erdos1040.volume_quadratic_sublevel_le` (E1040-UNBOUNDED).
* `Erdos1040.unbounded_exists_quadratic_small_area` (E1040-UNBOUNDED).
* `Erdos1040.unbounded_hasArbitrarilySmallLemniscates` (E1040-UNBOUNDED).
* `Erdos1040.exists_pos_integrableOn_log_norm_sq_ball` (E1040-L2KERNEL).
* `Erdos1040.locallyIntegrable_log_norm_sq` (E1040-L2KERNEL).
* `Erdos1040.memLp_log_norm_of_isCompact` (E1040-L2KERNEL).
* `Erdos1040.atomicLogPotential` (E1040-ATOMIC-LOG).
* `Erdos1040.atomicLogPotential_eq_log_product` (E1040-ATOMIC-LOG).
* `Erdos1040.atomicLogPotential_neg_iff` (E1040-ATOMIC-LOG).
* `Erdos1040.ae_ne_roots` (E1040-ATOMIC-LOG).
* `Erdos1040.unitLemniscate_ae_eq_atomicLogPotential_neg` (E1040-ATOMIC-LOG).
* `Erdos1040.volume_unitLemniscate_eq_atomicLogPotential_neg` (E1040-ATOMIC-LOG).
* `Erdos1040.memLp_log_norm_sub_of_isCompact` (E1040-L2KERNEL).
* `Erdos1040.memLp_log_norm_sub_closedBall` (E1040-L2KERNEL).
* `Erdos1040.measure_neg_le_margin_add_sq_eLpNorm` (E1040-AREA-TRANSFER).
* `Erdos1040.restrictAreaL2` (E1040-L2KERNEL).
* `Erdos1040.lipschitzWith_restrictAreaL2` (E1040-L2KERNEL).
* `Erdos1040.continuous_translateAreaL2` (E1040-L2KERNEL).
* `Erdos1040.areaLogKernel` (E1040-L2KERNEL).
* `Erdos1040.continuous_areaLogKernel` (E1040-L2KERNEL).
* `Erdos1040.adjointAreaPotential` (E1040-ADJOINT-CONTINUITY).
* `Erdos1040.integrable_adjointAreaPotential` (E1040-ADJOINT-CONTINUITY).
* `Erdos1040.adjointAreaPotential_eq_inner` (E1040-ADJOINT-CONTINUITY).
* `Erdos1040.continuous_adjointAreaPotential` (E1040-ADJOINT-CONTINUITY).
* `Erdos1040.adjointAreaPotential_zero_on_support_of_ae` (E1040-ADJOINT-CONTINUITY).
* `Erdos1040.exists_sample_sequence_tendsto_integral` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exists_equal_weight_average` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exists_equal_weight_average_on_compact` (E1040-ATOMIC-KERNEL).
* `Erdos1040.memLp_atomicLogPotential_of_isCompact` (E1040-ATOMIC-KERNEL).
* `Erdos1040.areaLogKernel_average_ae_eq_atomicLogPotential` (E1040-ATOMIC-KERNEL).
* `Erdos1040.atomicLogPotential_toLp_eq_average_areaLogKernel` (E1040-ATOMIC-KERNEL).
* `Erdos1040.integrable_areaLogKernel_on_compact` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exists_roots_approx_areaLogKernel_integral` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exteriorLogKernel` (E1040-ATOMIC-KERNEL).
* `Erdos1040.continuous_exteriorLogKernel` (E1040-ATOMIC-KERNEL).
* `Erdos1040.integrable_exteriorLogKernel_on_compact` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exteriorLogKernel_integral_apply` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exists_roots_approx_area_and_exterior_integrals` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exists_roots_approx_area_and_exterior_potentials` (E1040-ATOMIC-KERNEL).
* `Erdos1040.exists_bound_log_norm_circleMap_sub` (E1040-CIRCLE-MEAN).
* `Erdos1040.integrable_log_density_at_circleMap` (E1040-CIRCLE-MEAN).
* `Erdos1040.integrable_circle_log_density_prod` (E1040-CIRCLE-MEAN).
* `Erdos1040.circleIntegrable_log_density_potential` (E1040-CIRCLE-MEAN).
* `Erdos1040.circleAverage_log_density_potential` (E1040-CIRCLE-MEAN).
* `Erdos1040.circleAverage_log_density_potential_zero_of_integral_zero` (E1040-CIRCLE-MEAN).
* `Erdos1040.exists_roots_simultaneous_potential_approximation` (E1040-ATOMIC-KERNEL).
* `Erdos1040.circleAverage_adjointAreaPotential` (E1040-CIRCLE-MEAN).
* `Erdos1040.integral_sq_log_norm_sub_eq_norm_areaLogKernel_sq` (E1040-SOURCE-POTENTIAL).
* `Erdos1040.integrable_log_norm_sub_prod` (E1040-SOURCE-POTENTIAL).
* `Erdos1040.harmonic_eventually_eq_of_isLocalMax` (E1040-HARMONIC-MAX).
* `Erdos1040.harmonic_eqOn_of_isPreconnected_of_isMaxOn` (E1040-HARMONIC-MAX).
* `Erdos1040.areaLogKernel_integral_ae_eq_source_potential` (E1040-SOURCE-POTENTIAL).
* `Erdos1040.memLp_source_potential` (E1040-SOURCE-POTENTIAL).
* `Erdos1040.source_potential_toLp_eq_integral_areaLogKernel` (E1040-SOURCE-POTENTIAL).
* `Erdos1040.abs_log_norm_sub_sub_log_norm_le` (E1040-POTENTIAL-ASYMPTOTICS).
* `Erdos1040.integrable_log_density_potential_of_norm_lt` (E1040-POTENTIAL-ASYMPTOTICS).
* `Erdos1040.abs_log_density_potential_sub_mass_log_le` (E1040-POTENTIAL-ASYMPTOTICS).
* `Erdos1040.tendsto_log_density_potential_sub_mass_log` (E1040-POTENTIAL-ASYMPTOTICS).
* `Erdos1040.tendsto_log_density_potential_of_integral_zero` (E1040-POTENTIAL-ASYMPTOTICS).
* `Erdos1040.harmonic_nonpos_of_continuous_majorant` (E1040-HARMONIC-MAX).
* `Erdos1040.harmonic_eq_zero_of_nonpos_of_circleAverage_zero` (E1040-HARMONIC-MAX).
* `Erdos1040.integrable_areaLogKernel_density` (E1040-SOURCE-DENSITY).
* `Erdos1040.integrable_log_density_prod` (E1040-SOURCE-DENSITY).
* `Erdos1040.areaLogKernel_density_integral_ae_eq_source_potential` (E1040-SOURCE-DENSITY).
* `Erdos1040.memLp_source_density_potential` (E1040-SOURCE-DENSITY).
* `Erdos1040.source_density_potential_toLp_eq_integral_areaLogKernel` (E1040-SOURCE-DENSITY).
* `Erdos1040.inner_integral_areaLogKernel_density` (E1040-SOURCE-DENSITY).
* `Erdos1040.capSet` (E1040-CAP-SEPARATOR).
* `Erdos1040.isCompact_capSet` (E1040-CAP-SEPARATOR).
* `Erdos1040.cap_denominator_ne_zero` (E1040-CAP-SEPARATOR).
* `Erdos1040.capResolvent` (E1040-CAP-SEPARATOR).
* `Erdos1040.closed_subalgebra_geometric_inverse_mem` (E1040-CAP-SEPARATOR).
* `Erdos1040.capResolvent_far_mem` (E1040-CAP-SEPARATOR).
* `Erdos1040.capResolvent_step_mem` (E1040-CAP-SEPARATOR).
* `Erdos1040.adjointAreaPotential_ae_zero_of_annihilator` (E1040-ANNIHILATOR).
* `Erdos1040.capSet_compactSpace` (E1040-CAP-SEPARATOR).
* `Erdos1040.norm_normalized_log_kernel_le` (E1040-POTENTIAL-HARMONICITY).
* `Erdos1040.hasDerivAt_normalized_log_kernel` (E1040-POTENTIAL-HARMONICITY).
* `Erdos1040.integrable_normalized_log_density` (E1040-POTENTIAL-HARMONICITY).
* `Erdos1040.differentiableOn_normalized_log_density_integral` (E1040-POTENTIAL-HARMONICITY).
* `Erdos1040.integrable_log_density_potential_of_notMem` (E1040-POTENTIAL-HARMONICITY).
* `Erdos1040.harmonicAt_log_density_potential` (E1040-POTENTIAL-HARMONICITY).
* `Erdos1040.harmonicOnNhd_log_density_potential_compl` (E1040-POTENTIAL-HARMONICITY).
* `Erdos1040.adjointAreaPotential_zero_on_support_of_annihilator` (E1040-ANNIHILATOR).
* `Erdos1040.capResolvent_zero_mem` (E1040-CAP-SEPARATOR).
* `Erdos1040.exists_cap_polynomial` (E1040-CAP-SEPARATOR).
* `Erdos1040.hasSum_log_density_moments` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.hasFPowerSeriesAt_log_density_generating_function` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.integrable_log_density_generating_function` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.re_log_density_generating_function` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.integral_eq_of_log_density_potential_eq` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.complex_moments_eq_of_log_density_potential_eq` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.integrable_polynomial_density` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.polynomial_integrals_eq_of_log_density_potential_eq` (E1040-POTENTIAL-MOMENTS).
* `Erdos1040.boundedMeasurableDensities` (E1040-DENSITY-OPERATOR).
* `Erdos1040.sourceDensityOperator` (E1040-DENSITY-OPERATOR).
* `Erdos1040.exists_density_approx_of_annihilator` (E1040-DENSITY-OPERATOR).
* `Erdos1040.exists_polynomial_rotation_integral` (E1040-RUNGE).
* `Erdos1040.exists_unit_rotation_mean_ge_constant` (E1040-RUNGE).
* `Erdos1040.volume_rotated_strip_le` (E1040-RUNGE).
* `Erdos1040.exists_mean_zero_polynomial_large_off_small_area` (E1040-RUNGE).
* `Erdos1040.adjointAreaPotential_eq_mass_mul_source_potential_of_annihilator` (E1040-ADJOINT-UNIQUENESS).
* `Erdos1040.integral_area_mul_re_polynomial_eq_mass_mul_source_integral_of_annihilator` (E1040-ADJOINT-UNIQUENESS).
* `Erdos1040.nonnegativeLogKernel` (E1040-LOG-ENERGY).
* `Erdos1040.nonnegativeLogKernel_self` (E1040-LOG-ENERGY).
* `Erdos1040.nonnegativeLogKernel_of_ne` (E1040-LOG-ENERGY).
* `Erdos1040.continuous_nonnegativeLogKernel` (E1040-LOG-ENERGY).
* `Erdos1040.lowerSemicontinuous_lintegral_continuous_ennreal` (E1040-LOG-ENERGY).
* `Erdos1040.nonnegativeLogEnergy` (E1040-LOG-ENERGY).
* `Erdos1040.lowerSemicontinuous_nonnegativeLogEnergy` (E1040-LOG-ENERGY).
* `Erdos1040.exists_minimizer_nonnegativeLogEnergy` (E1040-LOG-ENERGY).
* `Erdos1040.memLp_re_polynomial` (E1040-DENSITY).
* `Erdos1040.inner_re_polynomial_toLp` (E1040-DENSITY).
* `Erdos1040.exists_density_approx_re_polynomial` (E1040-DENSITY).
* `Erdos1040.shifted_density_mass_pos` (E1040-POSITIVE-DENSITY).
* `Erdos1040.isProbabilityMeasure_shifted_density` (E1040-POSITIVE-DENSITY).
* `Erdos1040.integral_shifted_density` (E1040-POSITIVE-DENSITY).
* `Erdos1040.unitLemniscate_subset_closedBall_of_roots_norm_le` (E1040-AREA-ASSEMBLY).
* `Erdos1040.exists_L2_tolerance_for_small_negative_set` (E1040-AREA-ASSEMBLY).
* `Erdos1040.exists_roots_small_area_of_source_margin` (E1040-AREA-ASSEMBLY).
* `Erdos1040.hasArbitrarilySmallLemniscates_of_uniform_source_margin` (E1040-AREA-ASSEMBLY).
* `Erdos1040.nonnegativeLogKernel_toReal_of_dist_le` (E1040-LOG-ENERGY).
* `Erdos1040.ae_ne_of_finite_nonnegativeLogEnergy` (E1040-LOG-ENERGY).
* `Erdos1040.nullSingletonClass_of_finite_nonnegativeLogEnergy` (E1040-LOG-ENERGY).
* `Erdos1040.integrable_log_dist_prod_of_finite_nonnegativeLogEnergy` (E1040-LOG-ENERGY).
* `Erdos1040.nonnegativeLogEnergy_toReal_eq_log_sub_integral` (E1040-LOG-ENERGY).
* `Erdos1040.probabilityMixture` (E1040-ENERGY-VARIATION).
* `Erdos1040.nonnegativeLogCrossEnergy` (E1040-ENERGY-VARIATION).
* `Erdos1040.nonnegativeLogCrossEnergy_comm` (E1040-ENERGY-VARIATION).
* `Erdos1040.nonnegativeLogEnergy_probabilityMixture` (E1040-ENERGY-VARIATION).
* `Erdos1040.toReal_nonnegativeLogEnergy_probabilityMixture` (E1040-ENERGY-VARIATION).
* `Erdos1040.nonnegativeLogEnergy_le_crossEnergy_of_minimizer` (E1040-ENERGY-VARIATION).
* `Erdos1040.exists_L2_tolerance_for_small_sublevel_set` (E1040-CONDITIONAL-LEMNISCATE).
* `Erdos1040.exists_large_shift_small_exterior_set` (E1040-CONDITIONAL-LEMNISCATE).
* `Erdos1040.shifted_source_potential_ae_eq` (E1040-CONDITIONAL-LEMNISCATE).
* `Erdos1040.nonnegativeLogKernel_scale_change` (E1040-LOG-ENERGY).
* `Erdos1040.nonnegativeLogEnergy_scale_change` (E1040-LOG-ENERGY).
* `Erdos1040.finite_nonnegativeLogEnergy_scale_iff` (E1040-LOG-ENERGY).
* `Erdos1040.nonnegativeLogEnergy_normalized_scale_independent` (E1040-LOG-ENERGY).
* `Erdos1040.minimizer_nonnegativeLogEnergy_scale_iff` (E1040-LOG-ENERGY).
* `Erdos1040.nonnegativeLogPotential` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.HasNoFiniteLogEnergyProbability` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.measurable_nonnegativeLogPotential` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.nonnegativeLogCrossEnergy_eq_lintegral_potential` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.hasNoFiniteLogEnergyProbability_sublevel_of_minimizer` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.probabilityRestriction` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.finite_nonnegativeLogEnergy_probabilityRestriction` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.measure_eq_zero_of_hasNoFiniteLogEnergyProbability` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.nonnegativeLogPotential_ae_eq_energy_of_minimizer` (E1040-ENERGY-FROSTMAN).
* `Erdos1040.hasArbitrarilySmallLemniscates_of_potential_properties` (E1040-CONDITIONAL-LEMNISCATE).
* `Erdos1040.truncatedLogEnergy` (E1040-TRUNCATED-ENERGY).
* `Erdos1040.lowerSemicontinuous_truncatedLogEnergy` (E1040-TRUNCATED-ENERGY).
* `Erdos1040.nonnegativeLogEnergy_eq_iSup_truncated` (E1040-TRUNCATED-ENERGY).
* `Erdos1040.exists_probability_energy_le_of_truncated_bounds` (E1040-TRUNCATED-ENERGY).
* `Erdos1040.exists_probability_energy_le_of_approx_truncated_bounds` (E1040-TRUNCATED-ENERGY).
* `Erdos1040.empiricalSourceProbability` (E1040-EMPIRICAL-ENERGY).
* `Erdos1040.lintegral_empiricalSourceProbability` (E1040-EMPIRICAL-ENERGY).
* `Erdos1040.truncatedLogEnergy_empirical` (E1040-EMPIRICAL-ENERGY).
* `Erdos1040.unorderedPairProduct` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.geometricMeanSeparation` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.finiteDiameter` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.transfiniteDiameter` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.continuous_unorderedPairProduct` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.continuous_geometricMeanSeparation` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.finiteDiameter_eq_max_of_compact` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.finiteDiameter_empty` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.transfiniteDiameter_empty` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.finiteDiameter_lt_top_of_compact` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.exists_distinct_configuration_of_one_le_transfiniteDiameter` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.sum_offDiag_log_dist_eq_twice_log_unorderedPairProduct` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.exists_distinct_configuration_log_sum_nonneg` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.lowerSemicontinuous_nonnegativeLogPotential` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.nonnegativeLogPotential_le_energy_on_support_of_minimizer` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.integrable_log_norm_sub_of_nonnegativeLogPotential_ne_top` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.nonnegativeLogPotential_toReal_eq_log_sub_integral` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.sourceSupport` (E1040-SUPPORT-HULL).
* `Erdos1040.sourceSupport_subset` (E1040-SUPPORT-HULL).
* `Erdos1040.isCompact_sourceSupport` (E1040-SUPPORT-HULL).
* `Erdos1040.sourceSupport_nonempty` (E1040-SUPPORT-HULL).
* `Erdos1040.sourceProbabilityOnSupport` (E1040-SUPPORT-HULL).
* `Erdos1040.map_sourceProbabilityOnSupport` (E1040-SUPPORT-HULL).
* `Erdos1040.integral_sourceProbabilityOnSupport` (E1040-SUPPORT-HULL).
* `Erdos1040.integrable_sourceProbabilityOnSupport_iff` (E1040-SUPPORT-HULL).
* `Erdos1040.lintegral_sourceProbabilityOnSupport` (E1040-SUPPORT-HULL).
* `Erdos1040.nullSingletonClass_sourceProbabilityOnSupport` (E1040-SUPPORT-HULL).
* `Erdos1040.integrable_source_potential_of_notMem_support` (E1040-SUPPORT-HULL).
* `Erdos1040.harmonicOnNhd_source_potential_compl_support` (E1040-SUPPORT-HULL).
* `Erdos1040.toReal_truncatedLogEnergy_empirical` (E1040-EMPIRICAL-ENERGY).
* `Erdos1040.isPreconnected_complex_norm_gt` (E1040-SUPPORT-HULL).
* `Erdos1040.frontier_connectedComponentIn_compl_subset` (E1040-SUPPORT-HULL).
* `Erdos1040.exists_compact_hull_with_connected_complement` (E1040-SUPPORT-HULL).
* `Erdos1040.sum_truncated_kernel_le_of_log_sum_nonneg` (E1040-EMPIRICAL-ENERGY).
* `Erdos1040.truncatedLogEnergy_empirical_le_of_log_sum_nonneg` (E1040-EMPIRICAL-ENERGY).
* `Erdos1040.exists_probability_energy_le_log_of_one_le_transfiniteDiameter` (E1040-DIAMETER-ENERGY).
* `Erdos1040.exists_finite_minimizer_of_one_le_transfiniteDiameter` (E1040-DIAMETER-ENERGY).
* `Erdos1040.HasArbitrarilySmallLemniscates.mono` (E1040-POLYNOMIAL-CONCLUSION).
* `Erdos1040.exists_monic_polynomial_small_area` (E1040-POLYNOMIAL-CONCLUSION).
* `Erdos1040.tendsto_log_source_potential_atTop` (E1040-EXTERIOR-POSITIVITY).
* `Erdos1040.log_source_potential_pos_on_hull_compl` (E1040-EXTERIOR-POSITIVITY).
* `Erdos1040.hasArbitrarilySmallLemniscates_of_nonnegative_source_potential` (E1040-EQUILIBRIUM-ASSEMBLY).
* `Erdos1040.harmonic_nonpos_of_boundary_and_infinity` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.eventually_neg_log_potential_lt_of_le_on_source` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.integrable_log_norm_sub_of_finite_minimizer` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.log_source_potential_ge_of_finite_minimizer` (E1040-GLOBAL-FROSTMAN).
* `Erdos1040.hasArbitrarilySmallLemniscates_of_finite_minimizer` (E1040-EQUILIBRIUM-ASSEMBLY).
* `Erdos1040.hasArbitrarilySmallLemniscates_of_one_le_transfiniteDiameter` (E1040-COMPACT-GEOMETRIC).
* `Erdos1040.erdos1040` (E1040-FULL).
* `Erdos1040.sum_matrix_succAbove_eq` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.sum_succAbove_matrix_eq` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.sum_log_dist_eq_twice_log_unorderedPairProduct` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.unorderedPairProduct_pos_of_injective` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.log_geometricMeanSeparation_eq` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.sum_log_geometricMeanSeparation_succAbove` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.exists_geometricMeanSeparation_le_succAbove` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.finiteDiameter_succ_le` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.antitone_finiteDiameter` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.tendsto_finiteDiameter_transfiniteDiameter` (E1040-GEOMETRIC-DIAMETER).
* `Erdos1040.logarithmicCapacityScale` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.one_le_logarithmicCapacityScale` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.dist_le_logarithmicCapacityScale` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.robinConstant` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.logarithmicCapacity` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.robinConstant_eq_iInf_energy_sub_log` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.robinConstant_empty` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.logarithmicCapacity_empty` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.logarithmicCapacity_eq_zero_iff` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.one_le_logarithmicCapacity_iff` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.robinConstant_eq_energy_sub_log_of_minimizer` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.exists_finite_minimizer_of_one_le_logarithmicCapacity` (E1040-LOGARITHMIC-CAPACITY).
* `Erdos1040.hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity` (E1040-COMPACT-CAPACITY).
* `Erdos1040.erdos1040_capacity_one` (E1040-CAP1).
* `Erdos1040.hasArbitrarilySmallLemniscates_of_one_lt_logarithmicCapacity` (E1040-GT1).

Additional admission: formal/admissions/2026-09-05-capacity-only-complete.json.
The following 31 theorems and 3 definitions passed every documented gate
before index inclusion. Total: 241 theorems and 33 definitions in 52 modules.
E1040-CAPACITY-ONLY is refuted by the admitted negative statements.

* `Erdos1040.nonnegativeLogEnergy_eq_top_of_countable` (E1040-CAPACITY-ONLY).
* `Erdos1040.logarithmicCapacity_eq_zero_of_countable` (E1040-CAPACITY-ONLY).
* `Erdos1040.smallCountableSource` (E1040-CAPACITY-ONLY).
* `Erdos1040.smallCountableSource_countable` (E1040-CAPACITY-ONLY).
* `Erdos1040.smallCountableSource_isCompact` (E1040-CAPACITY-ONLY).
* `Erdos1040.smallCountableSource_infinite` (E1040-CAPACITY-ONLY).
* `Erdos1040.smallCountableSource_subset_closedBall` (E1040-CAPACITY-ONLY).
* `Erdos1040.zero_mem_smallCountableSource` (E1040-CAPACITY-ONLY).
* `Erdos1040.ball_three_quarters_subset_unitLemniscate` (E1040-CAPACITY-ONLY).
* `Erdos1040.volume_ball_three_quarters` (E1040-CAPACITY-ONLY).
* `Erdos1040.volume_unitLemniscate_ge_nine_pi_sixteenths` (E1040-CAPACITY-ONLY).
* `Erdos1040.ball_three_quarters_subset_monic_sublevel` (E1040-CAPACITY-ONLY).
* `Erdos1040.volume_monic_sublevel_ge_nine_pi_sixteenths` (E1040-CAPACITY-ONLY).
* `Erdos1040.volume_plus_minus_four_quadratic_le` (E1040-CAPACITY-ONLY).
* `Erdos1040.exists_plus_minus_four_monic_small_area` (E1040-CAPACITY-ONLY).
* `Erdos1040.plus_minus_four_area_bound_lt_ball_obstruction` (E1040-CAPACITY-ONLY).
* `Erdos1040.geometricMeanSeparation_dilate` (E1040-CAPACITY-ONLY).
* `Erdos1040.finiteDiameter_dilate` (E1040-CAPACITY-ONLY).
* `Erdos1040.transfiniteDiameter_dilate` (E1040-CAPACITY-ONLY).
* `Erdos1040.transfiniteDiameter_eq_zero_of_countable_compact` (E1040-CAPACITY-ONLY).
* `Erdos1040.minimalLemniscateArea` (E1040-CAPACITY-ONLY).
* `Erdos1040.minimalLemniscateArea_le_of_monic` (E1040-CAPACITY-ONLY).
* `Erdos1040.smallCountableSource_minimalLemniscateArea_ge` (E1040-CAPACITY-ONLY).
* `Erdos1040.largeCountableSource` (E1040-CAPACITY-ONLY).
* `Erdos1040.largeCountableSource_countable` (E1040-CAPACITY-ONLY).
* `Erdos1040.largeCountableSource_isCompact` (E1040-CAPACITY-ONLY).
* `Erdos1040.largeCountableSource_infinite` (E1040-CAPACITY-ONLY).
* `Erdos1040.largeCountableSource_minimalLemniscateArea_le` (E1040-CAPACITY-ONLY).
* `Erdos1040.capacity_only_dependence_counterexample` (E1040-CAPACITY-ONLY).
* `Erdos1040.minimalLemniscateArea_not_determined_by_transfiniteDiameter` (E1040-CAPACITY-ONLY).
* `Erdos1040.minimalLemniscateArea_not_determined_by_logarithmicCapacity` (E1040-CAPACITY-ONLY).
* `Erdos1040.minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials` (E1040-FULL).
* `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter` (E1040-FULL).
* `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity` (E1040-CAP1).
-/
