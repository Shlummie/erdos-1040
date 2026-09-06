import Erdos1040.LogKernel

/-!
Continuity of logarithmic kernels as classes in real area-L². The totalized
value of the logarithm at its source affects only an area-null singleton.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

namespace Erdos1040

/-- Restriction of global area-L² classes to an arbitrary planar set. -/
def restrictAreaL2 (K : Set ℂ) (f : Lp ℝ 2 (volume : Measure ℂ)) :
    Lp ℝ 2 (volume.restrict K) :=
  ((Lp.memLp f).restrict K).toLp f

/-- Restriction does not increase the L² distance. -/
theorem lipschitzWith_restrictAreaL2 (K : Set ℂ) :
    LipschitzWith 1 (restrictAreaL2 K) := by
  intro f g
  change edist (((Lp.memLp f).restrict K).toLp f)
      (((Lp.memLp g).restrict K).toLp g) ≤ (1 : ℝ≥0∞) * edist f g
  rw [Lp.edist_toLp_toLp, Lp.edist_def, one_mul]
  exact eLpNorm_mono_measure (p := 2) (μ := (volume : Measure ℂ))
    (ν := volume.restrict K) (⇑f - ⇑g) Measure.restrict_le_self

/-- Translations of a global area-L² class depend continuously on the shift. -/
theorem continuous_translateAreaL2 (f : Lp ℝ 2 (volume : Measure ℂ)) :
    Continuous (fun w : ℂ ↦
      Lp.compMeasurePreserving (fun z : ℂ ↦ z - w)
        (measurePreserving_sub_right (volume : Measure ℂ) w) f) := by
  let g : ℂ → C(ℂ, ℂ) := fun w ↦ ⟨fun z ↦ z - w, continuous_id.sub continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun w ↦ measurePreserving_sub_right (volume : Measure ℂ) w) (by norm_num)

/-- The logarithmic kernel with a variable source, as a real area-L² class. -/
def areaLogKernel {K : Set ℂ} (hK : IsCompact K) (w : ℂ) :
    Lp ℝ 2 (volume.restrict K) :=
  (memLp_log_norm_sub_of_isCompact w hK).toLp (fun z ↦ Real.log ‖z - w‖)

/-- On every compact planar domain, the logarithmic kernel depends continuously
on its source in the L² norm. -/
theorem continuous_areaLogKernel {K : Set ℂ} (hK : IsCompact K) :
    Continuous (areaLogKernel hK) := by
  apply continuous_iff_continuousAt.mpr
  intro w₀
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  let L : ℝ := R + ‖w₀‖ + 2
  let q : ℂ → ℝ := (closedBall 0 L).indicator (fun z ↦ Real.log ‖z‖)
  have hq : MemLp q 2 (volume : Measure ℂ) :=
    (memLp_indicator_iff_restrict measurableSet_closedBall).2
      (memLp_log_norm_of_isCompact (isCompact_closedBall 0 L))
  let T (w : ℂ) : Lp ℝ 2 (volume : Measure ℂ) :=
    Lp.compMeasurePreserving (fun z : ℂ ↦ z - w)
      (measurePreserving_sub_right (volume : Measure ℂ) w) (hq.toLp q)
  have hc : Continuous (fun w ↦ restrictAreaL2 K (T w)) :=
    (lipschitzWith_restrictAreaL2 K).continuous.comp
      (continuous_translateAreaL2 (hq.toLp q))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds w₀ (by norm_num : (0 : ℝ) < 1)] with w hw
  symm
  change ((Lp.memLp (T w)).restrict K).toLp (T w) =
    (memLp_log_norm_sub_of_isCompact w hK).toLp (fun z ↦ Real.log ‖z - w‖)
  apply MemLp.toLp_congr
  have hTw : (T w : ℂ → ℝ) =ᵐ[volume] fun z ↦ q (z - w) :=
    (hq.comp_measurePreserving
      (measurePreserving_sub_right (volume : Measure ℂ) w)).coeFn_toLp
  filter_upwards [ae_restrict_of_ae hTw, self_mem_ae_restrict hK.measurableSet] with z hz hzK
  have hww : ‖w - w₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
  have hnormw : ‖w‖ < ‖w₀‖ + 1 := by
    have ht := norm_sub_le w w₀
    have ht' := norm_add_le (w - w₀) w₀
    rw [sub_add_cancel] at ht'
    linarith
  have hzL : z - w ∈ closedBall (0 : ℂ) L := by
    rw [mem_closedBall_zero_iff]
    calc
      ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
      _ ≤ L := by dsimp [L]; linarith [hbound z hzK]
  rw [hz]
  exact Set.indicator_of_mem hzL _

end Erdos1040
