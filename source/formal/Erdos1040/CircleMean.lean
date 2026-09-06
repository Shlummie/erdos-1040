import Mathlib

/-!
Circle means of actual logarithmic source integrals. A compact source set
lies strictly inside the averaging circle, giving a uniform finite bound on
the logarithm and justifying both source integrability and Fubini. No value
or boundary regularity of a potential on its source set is asserted.
-/

noncomputable section

open MeasureTheory Metric Set Filter Complex
open scoped Topology

namespace Erdos1040

/-- The logarithm of distance between an enclosing circle and a compact source
set has a uniform finite bound, for every angle and every source point. -/
theorem exists_bound_log_norm_circleMap_sub {S : Set ℂ} (hS : IsCompact S)
    {R : ℝ} (hR : 0 < R) (hSR : ∀ w ∈ S, ‖w‖ < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, ∀ w : S,
      ‖Real.log ‖circleMap 0 R θ - (w : ℂ)‖‖ ≤ C := by
  have hn : ∀ p ∈ (sphere (0 : ℂ) R) ×ˢ S, ‖p.1 - p.2‖ ≠ 0 := by
    intro p hp
    apply norm_ne_zero_iff.mpr
    intro hp0
    have heq : p.1 = p.2 := sub_eq_zero.mp hp0
    have ht := hSR p.2 hp.2
    rw [← heq, mem_sphere_zero_iff_norm.mp hp.1] at ht
    exact (lt_irrefl R) ht
  have hc : ContinuousOn (fun p : ℂ × ℂ ↦ Real.log ‖p.1 - p.2‖)
      ((sphere (0 : ℂ) R) ×ˢ S) :=
    (continuous_fst.sub continuous_snd).norm.continuousOn.log hn
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : ℂ) R).prod hS).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun θ w ↦ ?_⟩
  exact (hC (circleMap 0 R θ, (w : ℂ))
    ⟨circleMap_mem_sphere 0 hR.le θ, w.property⟩).trans (le_max_left _ _)

/-- Every point of a strictly enclosing circle has an absolutely integrable
source kernel against an integrable real density. -/
theorem integrable_log_density_at_circleMap {S : Set ℂ} (hS : IsCompact S)
    {R : ℝ} (hR : 0 < R) (hSR : ∀ w ∈ S, ‖w‖ < R)
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Integrable f μ) (θ : ℝ) :
    Integrable (fun w : S ↦ f w * Real.log ‖circleMap 0 R θ - (w : ℂ)‖) μ := by
  obtain ⟨C, _, hC⟩ := exists_bound_log_norm_circleMap_sub hS hR hSR
  exact hf.mul_bdd
    (by fun_prop : Measurable (fun w : S ↦ Real.log ‖circleMap 0 R θ - (w : ℂ)‖)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w ↦ hC θ w))

/-- The angle/source product integrand is absolutely integrable, establishing
the actual Fubini hypothesis for circle averaging. -/
theorem integrable_circle_log_density_prod {S : Set ℂ} (hS : IsCompact S)
    {R : ℝ} (hR : 0 < R) (hSR : ∀ w ∈ S, ‖w‖ < R)
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Integrable f μ) :
    Integrable (fun p : ℝ × S ↦ f p.2 * Real.log ‖circleMap 0 R p.1 - (p.2 : ℂ)‖)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod μ) := by
  obtain ⟨C, _, hC⟩ := exists_bound_log_norm_circleMap_sub hS hR hSR
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.uIoc 0 (2 * Real.pi))) := by
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    infer_instance
  exact (hf.comp_snd (volume.restrict (Set.uIoc 0 (2 * Real.pi)))).mul_bdd
    (by fun_prop : Measurable
      (fun p : ℝ × S ↦ Real.log ‖circleMap 0 R p.1 - (p.2 : ℂ)‖)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p ↦ hC p.1 p.2))

/-- The actual source potential is circle-integrable on every strictly
enclosing circle. -/
theorem circleIntegrable_log_density_potential {S : Set ℂ} (hS : IsCompact S)
    {R : ℝ} (hR : 0 < R) (hSR : ∀ w ∈ S, ‖w‖ < R)
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Integrable f μ) :
    CircleIntegrable (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) 0 R := by
  apply intervalIntegrable_iff.mpr
  exact (integrable_circle_log_density_prod hS hR hSR μ f hf).integral_prod_left

/-- The circle mean of an actual logarithmic source integral equals its real
mass times the logarithm of the strictly enclosing radius. -/
theorem circleAverage_log_density_potential {S : Set ℂ} (hS : IsCompact S)
    {R : ℝ} (hR : 0 < R) (hSR : ∀ w ∈ S, ‖w‖ < R)
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Integrable f μ) :
    Real.circleAverage (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) 0 R =
      (∫ w : S, f w ∂μ) * Real.log R := by
  calc
    Real.circleAverage (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) 0 R =
        ∫ w : S, f w * Real.circleAverage (fun z : ℂ ↦ Real.log ‖z - (w : ℂ)‖) 0 R ∂μ := by
      rw [Real.circleAverage_def, smul_eq_mul,
        intervalIntegral_integral_swap (integrable_circle_log_density_prod hS hR hSR μ f hf),
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      rw [intervalIntegral.integral_const_mul, Real.circleAverage_def, smul_eq_mul]
      ring
    _ = ∫ w : S, f w * Real.log R ∂μ := by
      apply integral_congr_ae
      filter_upwards with w
      rw [circleAverage_log_norm_sub_const_of_mem_closedBall]
      rw [mem_closedBall_zero_iff, abs_of_pos hR]
      exact (hSR w w.property).le
    _ = (∫ w : S, f w ∂μ) * Real.log R := integral_mul_const _ _

/-- A zero-mass real source density has exactly zero logarithmic circle mean
on every strictly enclosing circle. -/
theorem circleAverage_log_density_potential_zero_of_integral_zero {S : Set ℂ}
    (hS : IsCompact S) {R : ℝ} (hR : 0 < R) (hSR : ∀ w ∈ S, ‖w‖ < R)
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Integrable f μ)
    (hmass : ∫ w : S, f w ∂μ = 0) :
    Real.circleAverage (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) 0 R = 0 := by
  rw [circleAverage_log_density_potential hS hR hSR μ f hf, hmass, zero_mul]

end Erdos1040
