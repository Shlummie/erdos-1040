import Erdos1040.SourcePotential
import Erdos1040.AdjointPotential

/-!
Bounded measurable real source densities: actual logarithmic potentials,
Bochner area-L² classes, and the adjoint pairing used by the density argument.
These identities do not assert the density theorem itself.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Erdos1040

theorem integrable_areaLogKernel_density {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ w, ‖f w‖ ≤ C) :
    Integrable (fun w : S ↦ f w • areaLogKernel hK (w : ℂ)) μ := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (fun w : S ↦ areaLogKernel hK (w : ℂ)) :=
    (continuous_areaLogKernel hK).comp continuous_subtype_val
  have hi : Integrable (fun w : S ↦ areaLogKernel hK (w : ℂ)) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  exact hi.bdd_smul C hf.aestronglyMeasurable (Filter.Eventually.of_forall hfC)

theorem integrable_log_density_prod {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ w, ‖f w‖ ≤ C) :
    Integrable (fun p : S × ℂ ↦ f p.1 * Real.log ‖p.2 - (p.1 : ℂ)‖)
      (μ.prod (volume.restrict K)) :=
  (integrable_log_norm_sub_prod hS hK μ).bdd_mul
    (hf.comp measurable_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ hfC p.1)

theorem areaLogKernel_density_integral_ae_eq_source_potential {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ w, ‖f w‖ ≤ C) :
    ⇑(∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ) =ᵐ[volume.restrict K]
      (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hi := integrable_areaLogKernel_density hS hK μ f hf C hfC
  have hp := integrable_log_density_prod hS hK μ f hf C hfC
  apply Integrable.ae_eq_of_forall_setIntegral_eq
    (⇑(∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ)) _
    ((Lp.memLp _).integrable (by norm_num)) hp.integral_prod_right
  intro t ht hμt
  let e : Lp ℝ 2 (volume.restrict K) := indicatorConstLp 2 ht hμt.ne (1 : ℝ)
  have hr : Integrable (fun p : S × ℂ ↦ f p.1 * Real.log ‖p.2 - (p.1 : ℂ)‖)
      (μ.prod ((volume.restrict K).restrict t)) := by
    simpa only [← Measure.prod_restrict, Measure.restrict_univ] using
      hp.restrict (s := Set.univ ×ˢ t)
  calc
    (∫ z in t, (∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ) z ∂volume.restrict K) =
        ⟪e, ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ :=
      (L2.inner_indicatorConstLp_one ht hμt.ne _).symm
    _ = ∫ w : S, ⟪e, f w • areaLogKernel hK (w : ℂ)⟫_ℝ ∂μ := (integral_inner hi e).symm
    _ = ∫ w : S, ∫ z in t, f w * Real.log ‖z - (w : ℂ)‖ ∂volume.restrict K ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [inner_smul_right, L2.inner_indicatorConstLp_one ht hμt.ne, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (memLp_log_norm_sub_of_isCompact (w : ℂ) hK).coeFn_toLp] with z hz
      simp only [areaLogKernel, hz]
    _ = ∫ z in t, ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ ∂volume.restrict K :=
      integral_integral_swap hr

theorem memLp_source_density_potential {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ w, ‖f w‖ ≤ C) :
    MemLp (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ)
      2 (volume.restrict K) :=
  (Lp.memLp _).ae_eq
    (areaLogKernel_density_integral_ae_eq_source_potential hS hK μ f hf C hfC)

theorem source_density_potential_toLp_eq_integral_areaLogKernel {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ w, ‖f w‖ ≤ C) :
    (memLp_source_density_potential hS hK μ f hf C hfC).toLp
      (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) =
      ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ := by
  apply Lp.ext
  exact (memLp_source_density_potential hS hK μ f hf C hfC).coeFn_toLp.trans
    (areaLogKernel_density_integral_ae_eq_source_potential hS hK μ f hf C hfC).symm

theorem inner_integral_areaLogKernel_density {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ w, ‖f w‖ ≤ C)
    (h : Lp ℝ 2 (volume.restrict K)) :
    ⟪h, ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ =
      ∫ w : S, f w * adjointAreaPotential hK h (w : ℂ) ∂μ := by
  rw [← integral_inner (integrable_areaLogKernel_density hS hK μ f hf C hfC) h]
  simp only [inner_smul_right, adjointAreaPotential_eq_inner]

theorem adjointAreaPotential_ae_zero_of_annihilator {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (h : Lp ℝ 2 (volume.restrict K))
    (horth : ∀ f : S → ℝ, Measurable f → (∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) →
      ⟪h, ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ = 0) :
    (fun w : S ↦ adjointAreaPotential hK h (w : ℂ)) =ᵐ[μ] fun _ ↦ 0 := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let f : S → ℝ := fun w ↦ adjointAreaPotential hK h (w : ℂ)
  have hc : Continuous f := (continuous_adjointAreaPotential hK h).comp continuous_subtype_val
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ w, ‖f w‖ ≤ C := fun w ↦ hC w (Set.mem_univ w)
  have hz := horth f hc.measurable ⟨C, hb⟩
  rw [inner_integral_areaLogKernel_density hS hK μ f hc.measurable C hb h] at hz
  have hsq : (∫ w : S, (f w) ^ 2 ∂μ) = 0 := by simpa only [sq] using hz
  have hi : Integrable (fun w : S ↦ (f w) ^ 2) μ := by
    exact (MemLp.of_bound hc.aestronglyMeasurable C
      (Filter.Eventually.of_forall hb) : MemLp f 2 μ).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun w ↦ sq_nonneg (f w)) hi).mp hsq
  filter_upwards [hae] with w hw
  exact sq_eq_zero_iff.mp hw

theorem adjointAreaPotential_zero_on_support_of_annihilator {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (h : Lp ℝ 2 (volume.restrict K))
    (horth : ∀ f : S → ℝ, Measurable f → (∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) →
      ⟪h, ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ = 0) :
    ∀ w ∈ (μ.map ((↑) : S → ℂ)).support, adjointAreaPotential hK h w = 0 := by
  apply adjointAreaPotential_zero_on_support_of_ae hK h (μ.map ((↑) : S → ℂ))
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq (continuous_adjointAreaPotential hK h) continuous_const).measurableSet).2
  exact adjointAreaPotential_ae_zero_of_annihilator hS hK μ h horth

end Erdos1040
