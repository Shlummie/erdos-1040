import Erdos1040.CircleMean
import Erdos1040.AdjointPotential

/-!
The exact circle mean of the actual adjoint area potential. The compact-area
L² density has finite mass, and a strictly enclosing circle has no source
singularity. The subtype change of measure preserves the original area integral.
-/

noncomputable section

open MeasureTheory

namespace Erdos1040

/-- The actual area-adjoint potential has circle mean equal to its total
restricted-area mass times the logarithm of every strictly enclosing radius. -/
theorem circleAverage_adjointAreaPotential {K : Set ℂ} (hK : IsCompact K)
    (h : Lp ℝ 2 (volume.restrict K)) {R : ℝ} (hR : 0 < R)
    (hKR : ∀ z ∈ K, ‖z‖ < R) :
    Real.circleAverage (adjointAreaPotential hK h) 0 R =
      (∫ z in K, h z) * Real.log R := by
  let μK : Measure K := (volume : Measure ℂ).comap ((↑) : K → ℂ)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasureOnCompacts μK :=
    IsFiniteMeasureOnCompacts.comap' (volume : Measure ℂ) continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hK.measurableSet)
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hf : Integrable (fun z : K ↦ h z) μK :=
    (integrableOn_iff_comap_subtypeVal hK.measurableSet).mp
      (MemLp.integrable (by norm_num) (Lp.memLp h))
  have heq := circleAverage_log_density_potential hK hR hKR μK (fun z : K ↦ h z) hf
  have hpotential :
      (fun w : ℂ ↦ ∫ z : K, h z * Real.log ‖w - (z : ℂ)‖ ∂μK) =
        (fun w : ℂ ↦ ∫ z in K, h z * Real.log ‖w - z‖) := by
    funext w
    exact integral_subtype_comap hK.measurableSet (fun z : ℂ ↦ h z * Real.log ‖w - z‖)
  rw [hpotential] at heq
  change Real.circleAverage (fun w : ℂ ↦ ∫ z in K, h z * Real.log ‖w - z‖) 0 R =
    (∫ z in K, h z) * Real.log R
  simpa only [μK, integral_subtype_comap hK.measurableSet] using heq

end Erdos1040
