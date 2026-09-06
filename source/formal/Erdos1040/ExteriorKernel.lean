import Erdos1040.AtomicApproximation
import Erdos1040.AtomicPotential
import Erdos1040.LogContinuity

/-!
Uniform logarithmic-kernel approximation on compact sets disjoint from the
sources. Sampling the product of area-L² and continuous-function kernels
gives one positive finite root list meeting both error tolerances.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1040

/-- A logarithmic kernel on an observation set disjoint from its source set. -/
def exteriorLogKernel {S E : Set ℂ} (hSE : Disjoint S E) (w : S) : C(E, ℝ) :=
  ⟨fun z => Real.log ‖(z : ℂ) - (w : ℂ)‖,
    (continuous_subtype_val.sub continuous_const).norm.log (fun z =>
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hSE.symm.ne_of_mem z.property w.property)))⟩

/-- The exterior kernel varies continuously in the continuous-function topology. -/
theorem continuous_exteriorLogKernel {S E : Set ℂ} (hSE : Disjoint S E) :
    Continuous (exteriorLogKernel hSE) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).norm.log (fun p =>
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hSE.symm.ne_of_mem p.2.property p.1.property)))

/-- Compact sources give a Bochner-integrable exterior kernel in the sup-norm space. -/
theorem integrable_exteriorLogKernel_on_compact {S E : Set ℂ} [CompactSpace E]
    (hS : IsCompact S) (hSE : Disjoint S E)
    (μ : Measure S) [IsProbabilityMeasure μ] : Integrable (exteriorLogKernel hSE) μ := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  simpa only [IntegrableOn, Measure.restrict_univ] using
    (continuous_exteriorLogKernel hSE).continuousOn.integrableOn_compact (μ := μ) isCompact_univ

/-- Evaluation of the continuous-function integral is the actual logarithmic potential. -/
theorem exteriorLogKernel_integral_apply {S E : Set ℂ} [CompactSpace E]
    (hS : IsCompact S) (hSE : Disjoint S E)
    (μ : Measure S) [IsProbabilityMeasure μ] (z : E) :
    (∫ w, exteriorLogKernel hSE w ∂μ) z =
      ∫ w : S, Real.log ‖(z : ℂ) - (w : ℂ)‖ ∂μ := by
  exact ContinuousMap.integral_apply (integrable_exteriorLogKernel_on_compact hS hSE μ) z

/-- One positive equal-weight source list approximates both area-L² and exterior sup norms. -/
theorem exists_roots_approx_area_and_exterior_integrals {S K E : Set ℂ} [CompactSpace E]
    (hS : IsCompact S) (hK : IsCompact K) (hSE : Disjoint S E)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (εA εE : ℝ) (hεA : 0 < εA) (hεE : 0 < εE) :
    ∃ n : ℕ, 0 < n ∧ ∃ points : Fin n → S,
      ‖(n : ℝ)⁻¹ • ∑ i, areaLogKernel hK (points i) -
        ∫ w : S, areaLogKernel hK w ∂μ‖ < εA ∧
      ‖(n : ℝ)⁻¹ • ∑ i, exteriorLogKernel hSE (points i) -
        ∫ w : S, exteriorLogKernel hSE w ∂μ‖ < εE := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let k : S → Lp ℝ 2 (volume.restrict K) × C(E, ℝ) :=
    fun w => (areaLogKernel hK w, exteriorLogKernel hSE w)
  have hk : Continuous k :=
    ((continuous_areaLogKernel hK).comp continuous_subtype_val).prodMk
      (continuous_exteriorLogKernel hSE)
  have hki : Integrable k μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hk.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  obtain ⟨n, hn, points, hp⟩ := exists_equal_weight_average_on_compact hS μ k hk
    (min εA εE) (lt_min hεA hεE)
  refine ⟨n, hn, points, ?_, ?_⟩
  · have hf := (norm_fst_le ((n : ℝ)⁻¹ • ∑ i, k (points i) - ∫ w, k w ∂μ)).trans_lt hp
    have hf' := hf.trans_le (min_le_left εA εE)
    simpa [fst_integral hki, Prod.fst_sum, k] using hf'
  · have hf := (norm_snd_le ((n : ℝ)⁻¹ • ∑ i, k (points i) - ∫ w, k w ∂μ)).trans_lt hp
    have hf' := hf.trans_le (min_le_right εA εE)
    simpa [snd_integral hki, Prod.snd_sum, k] using hf'

/-- The same source list also approximates the actual exterior potential at every observation. -/
theorem exists_roots_approx_area_and_exterior_potentials {S K E : Set ℂ} [CompactSpace E]
    (hS : IsCompact S) (hK : IsCompact K) (hSE : Disjoint S E)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (εA εE : ℝ) (hεA : 0 < εA) (hεE : 0 < εE) :
    ∃ n : ℕ, 0 < n ∧ ∃ points : Fin n → S,
      ‖(n : ℝ)⁻¹ • ∑ i, areaLogKernel hK (points i) -
        ∫ w : S, areaLogKernel hK w ∂μ‖ < εA ∧
      ∀ z : E, |atomicLogPotential (fun i => (points i : ℂ)) z -
        ∫ w : S, Real.log ‖(z : ℂ) - (w : ℂ)‖ ∂μ| < εE := by
  obtain ⟨n, hn, points, hA, hE⟩ :=
    exists_roots_approx_area_and_exterior_integrals hS hK hSE μ εA εE hεA hεE
  refine ⟨n, hn, points, hA, fun z => ?_⟩
  have hz := (ContinuousMap.norm_coe_le_norm
    ((n : ℝ)⁻¹ • ∑ i, exteriorLogKernel hSE (points i) -
      ∫ w : S, exteriorLogKernel hSE w ∂μ) z).trans_lt hE
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.sum_apply] at hz
  rw [exteriorLogKernel_integral_apply hS hSE μ z] at hz
  simpa only [exteriorLogKernel, ContinuousMap.coe_mk, smul_eq_mul, Real.norm_eq_abs,
    atomicLogPotential, div_eq_mul_inv, mul_comm] using hz

end Erdos1040
