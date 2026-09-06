import Erdos1040.SourcePotential
import Erdos1040.AreaTransfer

/-!
The final discretization and area assembly, conditional on a source probability
whose actual logarithmic potential has a positive margin outside a small-area
set. No capacity or equilibrium-measure hypothesis is supplied by this module.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos1040

theorem unitLemniscate_subset_closedBall_of_roots_norm_le {n : ℕ}
    (roots : Fin n → ℂ) {M : ℝ} (hM : ∀ i, ‖roots i‖ ≤ M) :
    unitLemniscate roots ⊆ Metric.closedBall (0 : ℂ) (M + 1) := by
  intro z hz
  by_contra hzM
  have hzM' : M + 1 < ‖z‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hzM
  have hi (i : Fin n) : 1 ≤ ‖z - roots i‖ := by
    have hb := norm_sub_norm_le z (roots i)
    linarith [hM i]
  have hp : 1 ≤ ‖∏ i, (z - roots i)‖ := by
    rw [norm_prod]
    exact Finset.one_le_prod (fun i _ ↦ hi i)
  exact (not_lt_of_ge hp) hz

theorem exists_L2_tolerance_for_small_negative_set (ν : Measure ℂ)
    (g : ℂ → ℝ) (hg : MemLp g 2 ν) (δ : ℝ≥0) (hδ : 0 < δ)
    (ε : ℝ) (_hε : 0 < ε) (ha : ν {z | g z < (δ : ℝ)} < ENNReal.ofReal ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ (f : ℂ → ℝ) (hf : MemLp f 2 ν),
      ‖hf.toLp f - hg.toLp g‖ < r → ν {z | f z < 0} < ENNReal.ofReal ε := by
  let a := ν {z | g z < (δ : ℝ)}
  have hafin : a ≠ ∞ := ne_top_of_lt (ha.trans_le le_top)
  have hδR : 0 < (δ : ℝ) := hδ
  have hc : ContinuousAt (fun r : ℝ ↦ ENNReal.ofReal
      (a.toReal + ((δ : ℝ)⁻¹)^2 * r^2)) 0 :=
    ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
  have hs : ∀ᶠ r : ℝ in 𝓝 0, ENNReal.ofReal
      (a.toReal + ((δ : ℝ)⁻¹)^2 * r^2) < ENNReal.ofReal ε := by
    apply hc.tendsto.eventually_lt_const
    simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, add_zero,
      ENNReal.ofReal_toReal hafin] using ha
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r, hr, fun f hf herr ↦ ?_⟩
  have hn := hrs (show ‖hf.toLp f - hg.toLp g‖ ∈ Metric.ball (0 : ℝ) r from by
    simpa only [Metric.mem_ball, dist_zero_right, norm_norm] using herr)
  change ENNReal.ofReal (a.toReal + ((δ : ℝ)⁻¹)^2 *
    ‖hf.toLp f - hg.toLp g‖ ^ 2) < ENNReal.ofReal ε at hn
  have he : eLpNorm (fun z ↦ f z - g z) 2 ν =
      ENNReal.ofReal ‖hf.toLp f - hg.toLp g‖ := by
    rw [ofReal_norm, ← MemLp.toLp_sub hf hg, Lp.enorm_toLp]
    rfl
  have hb := measure_neg_le_margin_add_sq_eLpNorm ν f g
    (hf.sub hg).aestronglyMeasurable δ hδ
  apply hb.trans_lt
  rw [he]
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal hafin, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos hδR, ENNReal.ofReal_coe_nnreal] at hn
  exact hn

theorem exists_roots_small_area_of_source_margin {S : Set ℂ} (hS : IsCompact S)
    {M : ℝ} (hSM : ∀ w ∈ S, ‖w‖ ≤ M) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ≥0) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε)
    (ha : (volume.restrict (Metric.closedBall (0 : ℂ) (M + 1)))
      {z | (∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) < (δ : ℝ)} < ENNReal.ofReal ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ roots : Fin n → ℂ, (∀ i, roots i ∈ S) ∧
      volume (unitLemniscate roots) < ENNReal.ofReal ε := by
  let D := Metric.closedBall (0 : ℂ) (M + 1)
  have hD : IsCompact D := isCompact_closedBall _ _
  let g : ℂ → ℝ := fun z ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ
  have hg : MemLp g 2 (volume.restrict D) := memLp_source_potential hS hD μ
  obtain ⟨r, hr, hrs⟩ := exists_L2_tolerance_for_small_negative_set
    (volume.restrict D) g hg δ hδ ε hε ha
  obtain ⟨n, hn, roots, hroots, herr⟩ :=
    exists_roots_approx_areaLogKernel_integral hS hD μ r hr
  have hnear : ‖(memLp_atomicLogPotential_of_isCompact roots hD).toLp
      (atomicLogPotential roots) - hg.toLp g‖ < r := by
    have heq : hg.toLp g = ∫ w : S, areaLogKernel hD (w : ℂ) ∂μ :=
      source_potential_toLp_eq_integral_areaLogKernel hS hD μ
    rw [heq]
    exact herr
  have hneg := hrs (atomicLogPotential roots)
    (memLp_atomicLogPotential_of_isCompact roots hD) hnear
  have hinside : unitLemniscate roots ⊆ D :=
    unitLemniscate_subset_closedBall_of_roots_norm_le roots
      (fun i ↦ hSM (roots i) (hroots i))
  refine ⟨n, hn, roots, hroots, ?_⟩
  calc
    volume (unitLemniscate roots) = (volume.restrict D) (unitLemniscate roots) := by
      rw [Measure.restrict_apply' hD.measurableSet, Set.inter_eq_left.mpr hinside]
    _ = (volume.restrict D) {z | atomicLogPotential roots z < 0} :=
      measure_congr (ae_restrict_of_ae (unitLemniscate_ae_eq_atomicLogPotential_neg hn roots))
    _ < ENNReal.ofReal ε := hneg

theorem hasArbitrarilySmallLemniscates_of_uniform_source_margin {S : Set ℂ}
    (hS : IsCompact S) {M : ℝ} (hSM : ∀ w ∈ S, ‖w‖ ≤ M)
    (μ : Measure S) [IsProbabilityMeasure μ] (δ : ℝ≥0) (hδ : 0 < δ)
    (hmargin : ∀ᵐ z : ℂ ∂volume.restrict (Metric.closedBall (0 : ℂ) (M + 1)),
      (δ : ℝ) ≤ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) :
    HasArbitrarilySmallLemniscates S := by
  intro ε hε
  apply exists_roots_small_area_of_source_margin hS hSM μ δ hδ ε hε
  have hz : (volume.restrict (Metric.closedBall (0 : ℂ) (M + 1)))
      {z | (∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) < (δ : ℝ)} = 0 := by
    simpa only [not_le] using ae_iff.mp hmargin
  rw [hz]
  exact ENNReal.ofReal_pos.mpr hε

end Erdos1040
