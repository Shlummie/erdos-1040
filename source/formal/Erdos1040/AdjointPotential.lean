import Erdos1040.LogContinuity

/-!
The area potential in the annihilator argument is an actual finite integral.
Its continuity on the entire plane uses area-L² kernel continuity, including
at sources and on irregular positive-area boundaries.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Erdos1040

/-- The logarithmic potential of a real area-L² density on a compact set. -/
def adjointAreaPotential {K : Set ℂ} (_hK : IsCompact K)
    (h : Lp ℝ 2 (volume.restrict K)) (w : ℂ) : ℝ :=
  ∫ z in K, h z * Real.log ‖w - z‖

theorem integrable_adjointAreaPotential {K : Set ℂ} (hK : IsCompact K)
    (h : Lp ℝ 2 (volume.restrict K)) (w : ℂ) :
    Integrable (fun z ↦ h z * Real.log ‖w - z‖) (volume.restrict K) := by
  apply (L2.integrable_inner (𝕜 := ℝ) h (areaLogKernel hK w)).congr
  filter_upwards [(memLp_log_norm_sub_of_isCompact w hK).coeFn_toLp] with z hz
  simpa [areaLogKernel, RCLike.inner_apply, hz, norm_sub_rev w z, mul_comm]

theorem adjointAreaPotential_eq_inner {K : Set ℂ} (hK : IsCompact K)
    (h : Lp ℝ 2 (volume.restrict K)) (w : ℂ) :
    adjointAreaPotential hK h w = ⟪h, areaLogKernel hK w⟫_ℝ := by
  rw [adjointAreaPotential, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_log_norm_sub_of_isCompact w hK).coeFn_toLp] with z hz
  simpa [areaLogKernel, RCLike.inner_apply, hz, norm_sub_rev w z, mul_comm]

theorem continuous_adjointAreaPotential {K : Set ℂ} (hK : IsCompact K)
    (h : Lp ℝ 2 (volume.restrict K)) : Continuous (adjointAreaPotential hK h) := by
  have hc : Continuous (fun w ↦ ⟪h, areaLogKernel hK w⟫_ℝ) :=
    continuous_const.inner (continuous_areaLogKernel hK)
  simpa only [← adjointAreaPotential_eq_inner hK h] using hc

theorem adjointAreaPotential_zero_on_support_of_ae {K : Set ℂ} (hK : IsCompact K)
    (h : Lp ℝ 2 (volume.restrict K)) (ν : Measure ℂ)
    (hzero : adjointAreaPotential hK h =ᵐ[ν] fun _ ↦ 0) :
    ∀ w ∈ ν.support, adjointAreaPotential hK h w = 0 := by
  exact ν.support_subset_of_isClosed
    (isClosed_eq (continuous_adjointAreaPotential hK h) continuous_const) hzero

end Erdos1040
