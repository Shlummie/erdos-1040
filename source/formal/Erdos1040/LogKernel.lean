import Mathlib

/-!
Planar square-integrability of the logarithmic kernel. The real logarithm is
totalized at zero; this is a representative for area-L² purposes. These lemmas
do not define classical equilibrium potentials or logarithmic capacity.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

namespace Erdos1040

/-- The square of the logarithmic norm is integrable near its planar singularity. -/
theorem exists_pos_integrableOn_log_norm_sq_ball :
    ∃ r : ℝ, 0 < r ∧
      IntegrableOn (fun z : ℂ ↦ (Real.log ‖z‖) ^ 2) (ball 0 r) volume := by
  have hsmall :=
    (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (s := (-1 : ℝ)) (2 : ℝ)
      (by norm_num)).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r, hr, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  refine ⟨r, hr, integrableOn_ball_of_norm_le_rpow
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ) (C := 1) (α := 1)
    (by norm_num) ?_ ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hb := hbound ⟨norm_pos_iff.mpr hz0, mem_ball_zero_iff.mp hz⟩
      simpa only [Set.mem_ofPred_eq, Real.rpow_two, Real.rpow_neg_one, norm_pow, Real.norm_eq_abs,
        abs_abs, abs_inv, abs_norm, one_mul] using hb
  · exact (by fun_prop : Measurable (fun z : ℂ ↦ (Real.log ‖z‖) ^ 2)).aestronglyMeasurable

/-- The square of the logarithmic norm is locally integrable for planar area. -/
theorem locallyIntegrable_log_norm_sq :
    LocallyIntegrable (fun z : ℂ ↦ (Real.log ‖z‖) ^ 2) volume := by
  intro z
  by_cases hz : z = 0
  · subst z
    obtain ⟨r, hr, hint⟩ := exists_pos_integrableOn_log_norm_sq_ball
    exact ⟨ball 0 r, ball_mem_nhds 0 hr, hint⟩
  · have hc : ContinuousAt (fun z : ℂ ↦ (Real.log ‖z‖) ^ 2) z :=
      (continuous_norm.continuousAt.log (norm_ne_zero_iff.mpr hz)).pow 2
    have hm : AEStronglyMeasurable (fun z : ℂ ↦ (Real.log ‖z‖) ^ 2) volume :=
      (by fun_prop : Measurable (fun z : ℂ ↦ (Real.log ‖z‖) ^ 2)).aestronglyMeasurable
    exact hc.integrableAtFilter
      ⟨univ, Filter.univ_mem, by simpa using hm⟩ (volume.finiteAt_nhds z)

/-- The logarithmic norm belongs to area-L² on every compact subset of the plane. -/
theorem memLp_log_norm_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    MemLp (fun z : ℂ ↦ Real.log ‖z‖) 2 (volume.restrict K) := by
  apply (memLp_two_iff_integrable_sq
    (by fun_prop : Measurable (fun z : ℂ ↦ Real.log ‖z‖)).aestronglyMeasurable).2
  exact locallyIntegrable_log_norm_sq.integrableOn_isCompact hK

/-- A logarithmic kernel with any source belongs to area-L² on every compact set. -/
theorem memLp_log_norm_sub_of_isCompact (w : ℂ) {K : Set ℂ} (hK : IsCompact K) :
    MemLp (fun z : ℂ ↦ Real.log ‖z - w‖) 2 (volume.restrict K) := by
  have hpres : MeasurePreserving (fun z : ℂ ↦ z - w) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℂ) (-w)
  have hemb : MeasurableEmbedding (fun z : ℂ ↦ z - w) := by
    exact (Homeomorph.subRight w).measurableEmbedding
  have hint : IntegrableOn (fun z : ℂ ↦ (Real.log ‖z‖) ^ 2)
      ((fun z : ℂ ↦ z - w) '' K) volume :=
    locallyIntegrable_log_norm_sq.integrableOn_isCompact
      (hK.image (continuous_id.sub continuous_const))
  apply (memLp_two_iff_integrable_sq
    (by fun_prop : Measurable (fun z : ℂ ↦ Real.log ‖z - w‖)).aestronglyMeasurable).2
  exact (hpres.integrableOn_image hemb).1 hint

/-- In particular, arbitrary translated logarithmic kernels are in area-L² on bounded disks. -/
theorem memLp_log_norm_sub_closedBall (c w : ℂ) (r : ℝ) :
    MemLp (fun z : ℂ ↦ Real.log ‖z - w‖) 2 (volume.restrict (closedBall c r)) :=
  memLp_log_norm_sub_of_isCompact w (isCompact_closedBall c r)

end Erdos1040
