import Erdos1040.PotentialAsymptotics

/-!
Harmonicity of actual compact-source logarithmic potentials away from their
sources. A local normalized complex logarithm supplies a local holomorphic
integral. No global logarithm branch or global harmonic conjugate is used.
-/

noncomputable section

open MeasureTheory InnerProductSpace Metric Set Filter
open scoped Topology

namespace Erdos1040

/-- A source separated by r gives a uniformly bounded normalized logarithm
on the observation disk of radius r/2. -/
theorem norm_normalized_log_kernel_le {z₀ z w : ℂ} {r : ℝ}
    (hr : 0 < r) (hw : r ≤ ‖z₀ - w‖) (hz : ‖z - z₀‖ < r / 2) :
    ‖Complex.log (1 + (z - z₀) / (z₀ - w))‖ ≤ 1 := by
  have hd : 0 < ‖z₀ - w‖ := lt_of_lt_of_le hr hw
  have hq : ‖(z - z₀) / (z₀ - w)‖ ≤ (1 : ℝ) / 2 := by
    rw [norm_div, div_le_iff₀ hd]
    linarith
  exact (Complex.norm_log_one_add_half_le_self hq).trans (by nlinarith)

/-- The local normalized logarithm has the usual reciprocal-distance derivative. -/
theorem hasDerivAt_normalized_log_kernel {z₀ z w : ℂ} {r : ℝ}
    (hr : 0 < r) (hw : r ≤ ‖z₀ - w‖) (hz : ‖z - z₀‖ < r / 2) :
    HasDerivAt (fun v : ℂ => Complex.log (1 + (v - z₀) / (z₀ - w)))
      (z - w)⁻¹ z := by
  have hd : 0 < ‖z₀ - w‖ := lt_of_lt_of_le hr hw
  have hd0 : z₀ - w ≠ 0 := norm_pos_iff.mp hd
  have hq : ‖(z - z₀) / (z₀ - w)‖ ≤ (1 : ℝ) / 2 := by
    rw [norm_div, div_le_iff₀ hd]
    linarith
  have hs : 1 + (z - z₀) / (z₀ - w) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    have hre := (abs_le.mp (Complex.abs_re_le_norm ((z - z₀) / (z₀ - w)))).1
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hdif := (((hasDerivAt_id z).sub_const z₀).div_const (z₀ - w)).const_add 1 |>.clog hs
  have heq : 1 / (z₀ - w) / (1 + (z - z₀) / (z₀ - w)) = (z - w)⁻¹ := by
    rw [div_div, one_div]
    congr 1
    field_simp [hd0]
    ring
  simpa only [id_eq, heq] using hdif

/-- Integrable real densities give integrable local complex logarithmic kernels. -/
theorem integrable_normalized_log_density {S : Set ℂ} {z₀ z : ℂ} {r : ℝ}
    (hr : 0 < r) (hsep : ∀ w : S, r ≤ ‖z₀ - (w : ℂ)‖)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ)
    (hz : ‖z - z₀‖ < r / 2) :
    Integrable (fun w : S => (f w : ℂ) *
      Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ)))) μ := by
  have hfc : Integrable (fun w : S => (f w : ℂ)) μ := hf.ofReal
  exact hfc.mul_bdd
    (by fun_prop : Measurable
      (fun w : S => Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ))))).aestronglyMeasurable
    (Eventually.of_forall (fun w => norm_normalized_log_kernel_le hr (hsep w) hz))

/-- Under uniform source separation, integration preserves local complex differentiability. -/
theorem differentiableOn_normalized_log_density_integral {S : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hsep : ∀ w : S, r ≤ ‖z₀ - (w : ℂ)‖)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ w : S, (f w : ℂ) *
      Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ))) ∂μ) (ball z₀ (r / 2)) := by
  intro z hz
  have hfc : Integrable (fun w : S => (f w : ℂ)) μ := hf.ofReal
  have hFmeas : ∀ᶠ v in 𝓝 z, AEStronglyMeasurable
      (fun w : S => (f w : ℂ) * Complex.log (1 + (v - z₀) / (z₀ - (w : ℂ)))) μ := by
    filter_upwards with v
    exact hfc.aestronglyMeasurable.mul
      (by fun_prop : Measurable
        (fun w : S => Complex.log (1 + (v - z₀) / (z₀ - (w : ℂ))))).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (fun w : S => (f w : ℂ) * (z - (w : ℂ))⁻¹) μ :=
    hfc.aestronglyMeasurable.mul
      (by fun_prop : Measurable (fun w : S => (z - (w : ℂ))⁻¹)).aestronglyMeasurable
  have hbound : ∀ᵐ w : S ∂μ, ∀ v ∈ ball z₀ (r / 2),
      ‖(f w : ℂ) * (v - (w : ℂ))⁻¹‖ ≤ |f w| / (r / 2) := by
    filter_upwards with w v hv
    have hv' : ‖v - z₀‖ < r / 2 := by simpa only [mem_ball, dist_eq_norm] using hv
    have hdist : r / 2 ≤ ‖v - (w : ℂ)‖ := by
      have ht := norm_add_le (z₀ - v) (v - (w : ℂ))
      rw [sub_add_sub_cancel, norm_sub_rev z₀ v] at ht
      linarith [hsep w]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hdist
  have hdiff : ∀ᵐ w : S ∂μ, ∀ v ∈ ball z₀ (r / 2),
      HasDerivAt (fun v : ℂ => (f w : ℂ) *
        Complex.log (1 + (v - z₀) / (z₀ - (w : ℂ))))
        ((f w : ℂ) * (v - (w : ℂ))⁻¹) v := by
    filter_upwards with w v hv
    exact (hasDerivAt_normalized_log_kernel hr (hsep w)
      (by simpa only [mem_ball, dist_eq_norm] using hv)).const_mul (f w : ℂ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_ball.mem_nhds hz) hFmeas
    (integrable_normalized_log_density hr hsep μ f hf
      (by simpa only [mem_ball, dist_eq_norm] using hz))
    hF'meas hbound (hf.abs.div_const _) hdiff).2.differentiableAt.differentiableWithinAt

/-- The actual signed logarithmic source integral is absolutely integrable
at every observation outside a compact source set. -/
theorem integrable_log_density_potential_of_notMem {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ) {z : ℂ} (hz : z ∉ S) :
    Integrable (fun w : S => f w * Real.log ‖z - (w : ℂ)‖) μ := by
  have hc : ContinuousOn (fun w : ℂ => Real.log ‖z - w‖) S :=
    (continuous_const.sub continuous_id).norm.continuousOn.log (by
      intro w hw
      change ‖z - w‖ ≠ 0
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun heq => hz (heq.symm ▸ hw))))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc
  exact hf.mul_bdd
    (by fun_prop : Measurable (fun w : S => Real.log ‖z - (w : ℂ)‖)).aestronglyMeasurable
    (Eventually.of_forall (fun w => hC w w.property))

/-- Actual logarithmic potentials of integrable real densities on compact
sources are harmonic at every observation outside the source set. -/
theorem harmonicAt_log_density_potential {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ) {z₀ : ℂ} (hz₀ : z₀ ∉ S) :
    HarmonicAt (fun z : ℂ => ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) z₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hS.isClosed.isOpen_compl.mem_nhds hz₀)
  have hsep : ∀ w : S, r ≤ ‖z₀ - (w : ℂ)‖ := by
    intro w
    by_contra h
    have hw : (w : ℂ) ∈ ball z₀ r := by
      simpa only [mem_ball, dist_eq_norm, norm_sub_rev (w : ℂ) z₀] using lt_of_not_ge h
    exact hball hw w.property
  let F : ℂ → ℂ := fun z => ∫ w : S, (f w : ℂ) *
    Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ))) ∂μ
  let P₀ : ℝ := ∫ w : S, f w * Real.log ‖z₀ - (w : ℂ)‖ ∂μ
  have hF : AnalyticAt ℂ F z₀ :=
    (differentiableOn_normalized_log_density_integral hr hsep μ f hf).analyticAt
      (ball_mem_nhds z₀ (by positivity))
  have hH : HarmonicAt (fun z => P₀ + (F z).re) z₀ :=
    (harmonicAt_const P₀).add hF.harmonicAt_re
  apply (harmonicAt_congr_nhds (f₁ := fun z => P₀ + (F z).re) ?_).mp hH
  filter_upwards [ball_mem_nhds z₀ (by positivity : 0 < r / 2)] with z hz
  have hzn : z ∉ S := hball ((ball_subset_ball (by linarith : r / 2 ≤ r)) hz)
  have hFint := integrable_normalized_log_density hr hsep μ f hf
    (by simpa only [mem_ball, dist_eq_norm] using hz)
  have hreal : (F z).re = ∫ w : S, ((f w : ℂ) *
      Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ)))).re ∂μ :=
    (Complex.reCLM.integral_comp_comm hFint).symm
  have hReint : Integrable (fun w : S => ((f w : ℂ) *
      Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ)))).re) μ :=
    Complex.reCLM.integrable_comp hFint
  rw [hreal]
  dsimp only [P₀]
  rw [← integral_add
    (integrable_log_density_potential_of_notMem hS μ f hf hz₀) hReint]
  apply integral_congr_ae
  filter_upwards with w
  have h0 : z₀ - (w : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun heq => hz₀ (heq.symm ▸ w.property))
  have hzw : z - (w : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun heq => hzn (heq.symm ▸ w.property))
  have harg : 1 + (z - z₀) / (z₀ - (w : ℂ)) = (z - (w : ℂ)) / (z₀ - (w : ℂ)) := by
    field_simp [h0]
    ring
  change f w * Real.log ‖z₀ - (w : ℂ)‖ +
    ((f w : ℂ) * Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ)))).re =
    f w * Real.log ‖z - (w : ℂ)‖
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.log_re, harg, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hzw) (norm_ne_zero_iff.mpr h0)]
  ring

/-- The actual signed logarithmic potential is harmonic throughout the
complement of its compact source set. -/
theorem harmonicOnNhd_log_density_potential_compl {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) (f : S → ℝ) (hf : Integrable f μ) :
    HarmonicOnNhd (fun z : ℂ => ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) Sᶜ :=
  fun _ hz => harmonicAt_log_density_potential hS μ f hf hz

end Erdos1040
