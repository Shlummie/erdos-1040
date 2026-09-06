import Erdos1040.DiscretePotential
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Actual source-integral representatives of compact-source Bochner area potentials.
The totalized logarithm is treated through joint absolute integrability, without
assuming pointwise evaluation is continuous on L².
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Erdos1040

theorem integral_sq_log_norm_sub_eq_norm_areaLogKernel_sq {K : Set ℂ}
    (hK : IsCompact K) (w : ℂ) :
    (∫ z in K, (Real.log ‖z - w‖) ^ 2) = ‖areaLogKernel hK w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_log_norm_sub_of_isCompact w hK).coeFn_toLp] with z hz
  simpa [areaLogKernel, hz, RCLike.inner_apply, sq]

theorem integrable_log_norm_sub_prod {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ] :
    Integrable (fun p : S × ℂ ↦ Real.log ‖p.2 - (p.1 : ℂ)‖)
      (μ.prod (volume.restrict K)) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hm : StronglyMeasurable (fun p : S × ℂ ↦ Real.log ‖p.2 - (p.1 : ℂ)‖) :=
    (Real.measurable_log.comp
      (measurable_snd.sub (measurable_subtype_coe.comp measurable_fst)).norm).stronglyMeasurable
  have hsquare : Integrable (fun p : S × ℂ ↦ (Real.log ‖p.2 - (p.1 : ℂ)‖) ^ 2)
      (μ.prod (volume.restrict K)) := by
    apply (integrable_prod_iff (hm.pow 2).aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun w ↦
        (memLp_log_norm_sub_of_isCompact (w : ℂ) hK).integrable_sq
    · have hc : Continuous (fun w : S ↦ ‖areaLogKernel hK (w : ℂ)‖ ^ 2) :=
        ((continuous_areaLogKernel hK).comp continuous_subtype_val).norm.pow 2
      have hi : Integrable (fun w : S ↦ ‖areaLogKernel hK (w : ℂ)‖ ^ 2) μ := by
        simpa only [IntegrableOn, Measure.restrict_univ] using
          hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
      simpa [Pi.pow_apply, Real.norm_eq_abs,
        integral_sq_log_norm_sub_eq_norm_areaLogKernel_sq hK] using hi
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsquare).integrable
    (by norm_num)

theorem areaLogKernel_integral_ae_eq_source_potential {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ] :
    ⇑(∫ w : S, areaLogKernel hK (w : ℂ) ∂μ) =ᵐ[volume.restrict K]
      (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hi : Integrable (fun w : S ↦ areaLogKernel hK (w : ℂ)) μ := by
    have hc : Continuous (fun w : S ↦ areaLogKernel hK (w : ℂ)) :=
      (continuous_areaLogKernel hK).comp continuous_subtype_val
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  have hp := integrable_log_norm_sub_prod hS hK μ
  apply Integrable.ae_eq_of_forall_setIntegral_eq
    (⇑(∫ w : S, areaLogKernel hK (w : ℂ) ∂μ)) _
    ((Lp.memLp _).integrable (by norm_num)) hp.integral_prod_right
  intro t ht hμt
  let e : Lp ℝ 2 (volume.restrict K) := indicatorConstLp 2 ht hμt.ne (1 : ℝ)
  have hr : Integrable (fun p : S × ℂ ↦ Real.log ‖p.2 - (p.1 : ℂ)‖)
      (μ.prod ((volume.restrict K).restrict t)) := by
    simpa only [← Measure.prod_restrict, Measure.restrict_univ] using
      hp.restrict (s := Set.univ ×ˢ t)
  calc
    (∫ z in t, (∫ w : S, areaLogKernel hK (w : ℂ) ∂μ) z ∂volume.restrict K) =
        ⟪e, ∫ w : S, areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ :=
      (L2.inner_indicatorConstLp_one ht hμt.ne _).symm
    _ = ∫ w : S, ⟪e, areaLogKernel hK (w : ℂ)⟫_ℝ ∂μ := (integral_inner hi e).symm
    _ = ∫ w : S, ∫ z in t, Real.log ‖z - (w : ℂ)‖ ∂volume.restrict K ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [L2.inner_indicatorConstLp_one ht hμt.ne]
      exact integral_congr_ae (ae_restrict_of_ae
        (memLp_log_norm_sub_of_isCompact (w : ℂ) hK).coeFn_toLp)
    _ = ∫ z in t, ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ ∂volume.restrict K :=
      integral_integral_swap hr

theorem memLp_source_potential {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ] :
    MemLp (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)
      2 (volume.restrict K) :=
  (Lp.memLp _).ae_eq (areaLogKernel_integral_ae_eq_source_potential hS hK μ)

theorem source_potential_toLp_eq_integral_areaLogKernel {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ] :
    (memLp_source_potential hS hK μ).toLp
      (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) =
      ∫ w : S, areaLogKernel hK (w : ℂ) ∂μ := by
  apply Lp.ext
  exact (memLp_source_potential hS hK μ).coeFn_toLp.trans
    (areaLogKernel_integral_ae_eq_source_potential hS hK μ).symm

end Erdos1040
