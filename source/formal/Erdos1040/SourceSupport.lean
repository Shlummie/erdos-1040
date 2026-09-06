import Erdos1040.PotentialHarmonic

/-!
The actual ambient support of a compact-source probability and its transport
to that support. The transported probability has exactly the same ambient
measure, actual integrals, integrability, and logarithmic potential.
-/

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology

namespace Erdos1040

def sourceSupport {S : Set ℂ} (μ : ProbabilityMeasure S) : Set ℂ :=
  ((μ : Measure S).map ((↑) : S → ℂ)).support

theorem sourceSupport_subset {S : Set ℂ} (hS : IsClosed S)
    (μ : ProbabilityMeasure S) : sourceSupport μ ⊆ S := by
  apply Measure.support_subset_of_isClosed hS
  rw [mem_ae_map_iff measurable_subtype_coe.aemeasurable hS.measurableSet]
  exact Filter.Eventually.of_forall fun w : S ↦ w.property

theorem isCompact_sourceSupport {S : Set ℂ} (hS : IsCompact S)
    (μ : ProbabilityMeasure S) : IsCompact (sourceSupport μ) :=
  hS.of_isClosed_subset Measure.isClosed_support (sourceSupport_subset hS.isClosed μ)

theorem sourceSupport_nonempty {S : Set ℂ} (μ : ProbabilityMeasure S) :
    (sourceSupport μ).Nonempty := by
  have : IsProbabilityMeasure ((μ : Measure S).map ((↑) : S → ℂ)) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  exact Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)

def sourceProbabilityOnSupport {S : Set ℂ} (μ : ProbabilityMeasure S) :
    ProbabilityMeasure (sourceSupport μ) := by
  let η : Measure ℂ := (μ : Measure S).map ((↑) : S → ℂ)
  have : IsProbabilityMeasure η :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  refine ⟨η.comap ((↑) : sourceSupport μ → ℂ), ?_⟩
  have hT : MeasurableSet (sourceSupport μ) := Measure.isClosed_support.measurableSet
  apply (MeasurableEmbedding.subtype_coe hT).isProbabilityMeasure_comap
  rw [Subtype.range_coe]
  change η.support ∈ ae η
  exact Measure.support_mem_ae

theorem map_sourceProbabilityOnSupport {S : Set ℂ} (μ : ProbabilityMeasure S) :
    (sourceProbabilityOnSupport μ : Measure (sourceSupport μ)).map
      ((↑) : sourceSupport μ → ℂ) = (μ : Measure S).map ((↑) : S → ℂ) := by
  change (((μ : Measure S).map ((↑) : S → ℂ)).comap
    ((↑) : sourceSupport μ → ℂ)).map ((↑) : sourceSupport μ → ℂ) = _
  have hT : MeasurableSet (sourceSupport μ) := Measure.isClosed_support.measurableSet
  rw [map_comap_subtype_coe hT]
  exact Measure.restrict_eq_self_of_ae_mem
    (show sourceSupport μ ∈ ae ((μ : Measure S).map ((↑) : S → ℂ)) from
      Measure.support_mem_ae)

theorem integral_sourceProbabilityOnSupport {S : Set ℂ} (hS : MeasurableSet S)
    (μ : ProbabilityMeasure S) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℂ → E) :
    (∫ w : sourceSupport μ, f (w : ℂ) ∂(sourceProbabilityOnSupport μ)) =
      ∫ w : S, f (w : ℂ) ∂μ := by
  have hT : MeasurableSet (sourceSupport μ) := Measure.isClosed_support.measurableSet
  rw [← (MeasurableEmbedding.subtype_coe hT).integral_map f,
    map_sourceProbabilityOnSupport, (MeasurableEmbedding.subtype_coe hS).integral_map f]

theorem integrable_sourceProbabilityOnSupport_iff {S : Set ℂ} (hS : MeasurableSet S)
    (μ : ProbabilityMeasure S) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℂ → E) :
    Integrable (fun w : sourceSupport μ ↦ f (w : ℂ))
      (sourceProbabilityOnSupport μ : Measure (sourceSupport μ)) ↔
      Integrable (fun w : S ↦ f (w : ℂ)) (μ : Measure S) := by
  have hT : MeasurableSet (sourceSupport μ) := Measure.isClosed_support.measurableSet
  change Integrable (f ∘ ((↑) : sourceSupport μ → ℂ)) _ ↔
    Integrable (f ∘ ((↑) : S → ℂ)) _
  rw [← (MeasurableEmbedding.subtype_coe hT).integrable_map_iff,
    map_sourceProbabilityOnSupport, (MeasurableEmbedding.subtype_coe hS).integrable_map_iff]

theorem lintegral_sourceProbabilityOnSupport {S : Set ℂ} (hS : MeasurableSet S)
    (μ : ProbabilityMeasure S) (f : ℂ → ℝ≥0∞) :
    (∫⁻ w : sourceSupport μ, f (w : ℂ) ∂(sourceProbabilityOnSupport μ)) =
      ∫⁻ w : S, f (w : ℂ) ∂μ := by
  have hT : MeasurableSet (sourceSupport μ) := Measure.isClosed_support.measurableSet
  rw [← (MeasurableEmbedding.subtype_coe hT).lintegral_map f,
    map_sourceProbabilityOnSupport, (MeasurableEmbedding.subtype_coe hS).lintegral_map f]

theorem nullSingletonClass_sourceProbabilityOnSupport {S : Set ℂ} (μ : ProbabilityMeasure S)
    [NullSingletonClass (μ : Measure S)] :
    NullSingletonClass (sourceProbabilityOnSupport μ : Measure (sourceSupport μ)) := by
  constructor
  intro x
  change (((μ : Measure S).map ((↑) : S → ℂ)).comap
    ((↑) : sourceSupport μ → ℂ)) {x} = 0
  have hT : MeasurableSet (sourceSupport μ) := Measure.isClosed_support.measurableSet
  rw [comap_subtype_coe_apply hT, Set.image_singleton,
    Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
  apply Set.Subsingleton.measure_zero
  intro y hy z hz
  apply Subtype.ext
  exact (show (y : ℂ) = (x : ℂ) from hy).trans
    (show (z : ℂ) = (x : ℂ) from hz).symm

theorem integrable_source_potential_of_notMem_support {S : Set ℂ} (hS : IsCompact S)
    (μ : ProbabilityMeasure S) {z : ℂ} (hz : z ∉ sourceSupport μ) :
    Integrable (fun w : S ↦ Real.log ‖z - (w : ℂ)‖) (μ : Measure S) := by
  apply (integrable_sourceProbabilityOnSupport_iff hS.measurableSet μ
    (fun w : ℂ ↦ Real.log ‖z - w‖)).mp
  simpa only [one_mul] using
    integrable_log_density_potential_of_notMem (isCompact_sourceSupport hS μ)
      (sourceProbabilityOnSupport μ : Measure (sourceSupport μ))
      (fun _ : sourceSupport μ ↦ (1 : ℝ)) (integrable_const 1) hz

theorem harmonicOnNhd_source_potential_compl_support {S : Set ℂ} (hS : IsCompact S)
    (μ : ProbabilityMeasure S) :
    HarmonicOnNhd (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)
      (sourceSupport μ)ᶜ := by
  have heq : (fun z : ℂ ↦ ∫ w : sourceSupport μ, Real.log ‖z - (w : ℂ)‖
      ∂(sourceProbabilityOnSupport μ)) =
      (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) := by
    funext z
    exact integral_sourceProbabilityOnSupport hS.measurableSet μ
      (fun w : ℂ ↦ Real.log ‖z - w‖)
  simpa only [one_mul, heq] using
    harmonicOnNhd_log_density_potential_compl (isCompact_sourceSupport hS μ)
      (sourceProbabilityOnSupport μ : Measure (sourceSupport μ))
      (fun _ : sourceSupport μ ↦ (1 : ℝ)) (integrable_const 1)

end Erdos1040
