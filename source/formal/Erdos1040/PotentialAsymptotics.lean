import Erdos1040.CircleMean

/-!
Asymptotics of actual signed logarithmic source integrals. A source-radius
bound gives an explicit O(1 / ‖z‖) bound for the potential after subtracting
its total real mass times log ‖z‖. Compact sources therefore give a zero
limit at infinity after this subtraction, including the zero-mass case.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology

namespace Erdos1040

/-- Outside twice the source distance, the logarithmic kernel differs from
the logarithm of the observation distance by at most twice their ratio. -/
theorem abs_log_norm_sub_sub_log_norm_le {z w : ℂ} (hz : 0 < ‖z‖)
    (hw : 2 * ‖w‖ ≤ ‖z‖) :
    |Real.log ‖z - w‖ - Real.log ‖z‖| ≤ 2 * ‖w‖ / ‖z‖ := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz
  have hzw : z - w ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [heq] at hz hw
    linarith [norm_nonneg w]
  have hq : ‖-(w / z)‖ ≤ (1 : ℝ) / 2 := by
    rw [norm_neg, norm_div, div_le_iff₀ hz]
    linarith
  have heq : Real.log ‖z - w‖ - Real.log ‖z‖ = Real.log ‖1 - w / z‖ := by
    rw [← Real.log_div (norm_ne_zero_iff.mpr hzw) (ne_of_gt hz), ← norm_div,
      sub_div, div_self hz0]
  rw [heq]
  calc
    |Real.log ‖1 - w / z‖| = |(Complex.log (1 - w / z)).re| := by rw [Complex.log_re]
    _ ≤ ‖Complex.log (1 - w / z)‖ := Complex.abs_re_le_norm _
    _ ≤ (3 / 2) * ‖w / z‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using Complex.norm_log_one_add_half_le_self hq
    _ ≤ 2 * ‖w‖ / ‖z‖ := by
      rw [norm_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (div_nonneg (norm_nonneg _) hz.le)

/-- An integrable signed source density gives an absolutely integrable
logarithmic source kernel outside twice any nonnegative source-radius bound. -/
theorem integrable_log_density_potential_of_norm_lt {S : Set ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hSM : ∀ w : S, ‖(w : ℂ)‖ ≤ M)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ)
    {z : ℂ} (hz : 2 * M < ‖z‖) :
    Integrable (fun w : S => f w * Real.log ‖z - (w : ℂ)‖) μ := by
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
  have hb (w : S) : |Real.log ‖z - (w : ℂ)‖ - Real.log ‖z‖| ≤ 2 * M / ‖z‖ := by
    exact (abs_log_norm_sub_sub_log_norm_le hzpos (by linarith [hSM w])).trans
      (div_le_div_of_nonneg_right (by linarith [hSM w]) hzpos.le)
  apply hf.mul_bdd
    (by fun_prop : Measurable (fun w : S => Real.log ‖z - (w : ℂ)‖)).aestronglyMeasurable
  filter_upwards with w
  calc
    ‖Real.log ‖z - (w : ℂ)‖‖ =
        |(Real.log ‖z - (w : ℂ)‖ - Real.log ‖z‖) + Real.log ‖z‖| := by
      rw [sub_add_cancel, Real.norm_eq_abs]
    _ ≤ |Real.log ‖z - (w : ℂ)‖ - Real.log ‖z‖| + |Real.log ‖z‖| := abs_add_le _ _
    _ ≤ 2 * M / ‖z‖ + |Real.log ‖z‖| := by linarith [hb w]

/-- The actual signed potential has a quantitative mass-corrected error
bounded by the source radius, total absolute density, and inverse distance. -/
theorem abs_log_density_potential_sub_mass_log_le {S : Set ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hSM : ∀ w : S, ‖(w : ℂ)‖ ≤ M)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ)
    {z : ℂ} (hz : 2 * M < ‖z‖) :
    |(∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) -
        (∫ w : S, f w ∂μ) * Real.log ‖z‖| ≤
      (2 * M / ‖z‖) * ∫ w : S, |f w| ∂μ := by
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz
  have hfi := integrable_log_density_potential_of_norm_lt hM hSM μ f hf hz
  have heq : (∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) -
      (∫ w : S, f w ∂μ) * Real.log ‖z‖ =
      ∫ w : S, f w * (Real.log ‖z - (w : ℂ)‖ - Real.log ‖z‖) ∂μ := by
    rw [← integral_mul_const, ← integral_sub hfi (hf.mul_const _)]
    apply integral_congr_ae
    filter_upwards with w
    ring
  rw [heq, ← Real.norm_eq_abs]
  calc
    ‖∫ w : S, f w * (Real.log ‖z - (w : ℂ)‖ - Real.log ‖z‖) ∂μ‖ ≤
        ∫ w : S, |f w| * (2 * M / ‖z‖) ∂μ := by
      apply norm_integral_le_of_norm_le (hf.abs.mul_const _)
      filter_upwards with w
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (abs_log_norm_sub_sub_log_norm_le hzpos (by linarith [hSM w])).trans
        (div_le_div_of_nonneg_right (by linarith [hSM w]) hzpos.le)
    _ = (2 * M / ‖z‖) * ∫ w : S, |f w| ∂μ := by
      rw [integral_mul_const, mul_comm]

/-- For compact sources, subtracting the total real mass times log distance
makes the actual logarithmic potential tend to zero at infinity. -/
theorem tendsto_log_density_potential_sub_mass_log {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ) :
    Tendsto (fun z : ℂ => (∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) -
      (∫ w : S, f w ∂μ) * Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨M, hM, hSM⟩ := hS.isBounded.exists_pos_norm_lt
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (g := fun z : ℂ => (2 * M / ‖z‖) * ∫ w : S, |f w| ∂μ)
  · filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (2 * M)] with z hz
    simpa only [Real.norm_eq_abs] using
      abs_log_density_potential_sub_mass_log_le hM.le (fun w => (hSM w w.property).le) μ f hf hz
  · simpa only [zero_mul] using
      (tendsto_norm_cocompact_atTop.const_div_atTop (2 * M)).mul_const (∫ w : S, |f w| ∂μ)

/-- An integrable real density of total mass zero on a compact source set
has an actual logarithmic potential tending to zero at infinity. -/
theorem tendsto_log_density_potential_of_integral_zero {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ)
    (hmass : ∫ w : S, f w ∂μ = 0) :
    Tendsto (fun z : ℂ => ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ)
      (cocompact ℂ) (𝓝 0) := by
  simpa only [hmass, zero_mul, sub_zero] using
    tendsto_log_density_potential_sub_mass_log hS μ f hf

end Erdos1040
