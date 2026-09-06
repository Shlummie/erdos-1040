import Erdos1040.CircleMean

/-!
Polynomial-moment extraction from equality of actual real logarithmic
potentials outside a disk. Sources may have different compact supports and
different finite measures. The generating functions use complex logarithms
only near zero, where their convergent series and real-part identities are
proved from the actual source integrals.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology
namespace Erdos1040
/-- The actual density-weighted complex logarithm has its integrated moment series. -/
theorem hasSum_log_density_moments {S : Set ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hSM : ∀ w : S, ‖(w : ℂ)‖ ≤ M) (μ : Measure S)
    (f : S → ℝ) (hf : Integrable f μ) {u : ℂ} (hu : ‖u‖ * M < 1) :
    HasSum (fun n : ℕ ↦ u ^ n * (∫ w : S, (f w : ℂ) * (w : ℂ) ^ n ∂μ) / n)
      (∫ w : S, (f w : ℂ) * (-Complex.log (1 - u * (w : ℂ))) ∂μ) := by
  let q : ℝ := ‖u‖ * M
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg _) hM
  have hqs : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_lt_one hq0 hu
  have hfc : Integrable (fun w : S ↦ (f w : ℂ)) μ := Complex.ofRealCLM.integrable_comp hf
  have hsum := hasSum_integral_of_dominated_convergence
    (F := fun (n : ℕ) (w : S) ↦ (f w : ℂ) * ((u * (w : ℂ)) ^ n / n))
    (f := fun w : S ↦ (f w : ℂ) * (-Complex.log (1 - u * (w : ℂ))))
    (fun (n : ℕ) (w : S) ↦ |f w| * q ^ n)
    (fun n ↦ hfc.aestronglyMeasurable.mul
      (by fun_prop : Measurable (fun w : S ↦ (u * (w : ℂ)) ^ n / (n : ℂ))).aestronglyMeasurable)
    (fun n ↦ Eventually.of_forall (fun w ↦ by
      by_cases hn : n = 0
      · simp [hn]
      · simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_natCast]
        calc |f w| * ((‖u‖ * ‖(w : ℂ)‖) ^ n / (n : ℝ))
            ≤ |f w| * ((‖u‖ * M) ^ n / (1 : ℝ)) := by
              gcongr
              · exact hSM w
              · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          _ = |f w| * q ^ n := by simp [q]))
    (Eventually.of_forall (fun w ↦ hqs.mul_left _))
    (by simpa only [tsum_mul_left] using (hf.abs.mul_const (∑' n : ℕ, q ^ n)))
    (Eventually.of_forall (fun w ↦ (Complex.hasSum_taylorSeries_neg_log
      ((norm_mul u (w : ℂ)).trans_lt ((mul_le_mul_of_nonneg_left (hSM w)
        (norm_nonneg u)).trans_lt hu))).mul_left (f w : ℂ)))
  convert! hsum using 1
  funext n
  rw [← integral_const_mul, div_eq_mul_inv, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with w
  rw [mul_pow]
  ring

/-- The actual generating integral is analytic at zero with the exact moment coefficients. -/
theorem hasFPowerSeriesAt_log_density_generating_function {S : Set ℂ} (hS : IsCompact S) (μ : Measure S)
    (f : S → ℝ) (hf : Integrable f μ) :
    HasFPowerSeriesAt
      (fun u : ℂ ↦ ∫ w : S, (f w : ℂ) * (-Complex.log (1 - u * (w : ℂ))) ∂μ)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ ↦ (∫ w : S, (f w : ℂ) * (w : ℂ) ^ n ∂μ) / n)) 0 := by
  obtain ⟨M, hM, hSM⟩ := hS.isBounded.exists_pos_norm_lt
  apply hasFPowerSeriesAt_iff.mpr
  have hu : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ * M < 1 :=
    (continuous_norm.mul_const M).continuousAt (gt_mem_nhds (by simp))
  filter_upwards [hu] with u hu
  simpa only [zero_add, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
    mul_div_assoc] using
    hasSum_log_density_moments hM.le (fun w ↦ (hSM w w.property).le) μ f hf hu

/-- The local complex logarithmic generating kernel is absolutely integrable. -/
theorem integrable_log_density_generating_function {S : Set ℂ} {M : ℝ}
    (hSM : ∀ w : S, ‖(w : ℂ)‖ ≤ M) (μ : Measure S)
    (f : S → ℝ) (hf : Integrable f μ) {u : ℂ} (hu : ‖u‖ * M ≤ 1 / 2) :
    Integrable (fun w : S ↦ (f w : ℂ) * (-Complex.log (1 - u * (w : ℂ)))) μ := by
  have hfc : Integrable (fun w : S ↦ (f w : ℂ)) μ := Complex.ofRealCLM.integrable_comp hf
  apply hfc.mul_bdd (c := (3 / 2) * (‖u‖ * M))
    (by fun_prop : Measurable (fun w : S ↦ -Complex.log (1 - u * (w : ℂ)))).aestronglyMeasurable
  filter_upwards with w
  have hw : ‖-(u * (w : ℂ))‖ ≤ (1 : ℝ) / 2 := by
    rw [norm_neg, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hSM w) (norm_nonneg u)).trans hu
  calc ‖-Complex.log (1 - u * (w : ℂ))‖
      = ‖Complex.log (1 + -(u * (w : ℂ)))‖ := by rw [norm_neg, sub_eq_add_neg]
    _ ≤ (3 / 2) * ‖-(u * (w : ℂ))‖ := Complex.norm_log_one_add_half_le_self hw
    _ ≤ (3 / 2) * (‖u‖ * M) := by
      rw [norm_neg, norm_mul]
      gcongr
      exact hSM w

/-- The real part of the generating integral is the exact mass-corrected potential. -/
theorem re_log_density_generating_function {S : Set ℂ} {M : ℝ}
    (hSM : ∀ w : S, ‖(w : ℂ)‖ ≤ M) (μ : Measure S)
    (f : S → ℝ) (hf : Integrable f μ) {u : ℂ}
    (hu0 : u ≠ 0) (hu : ‖u‖ * M ≤ 1 / 2) :
    (∫ w : S, (f w : ℂ) * (-Complex.log (1 - u * (w : ℂ))) ∂μ).re =
      (∫ w : S, f w ∂μ) * Real.log ‖u⁻¹‖ -
        ∫ w : S, f w * Real.log ‖u⁻¹ - (w : ℂ)‖ ∂μ := by
  have hi := integrable_log_density_generating_function hSM μ f hf hu
  have hkernel (w : S) : -Real.log ‖1 - u * (w : ℂ)‖ =
      Real.log ‖u⁻¹‖ - Real.log ‖u⁻¹ - (w : ℂ)‖ := by
    have huw : ‖u * (w : ℂ)‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left (hSM w) (norm_nonneg u)).trans hu)
        (by norm_num)
    have hne : 1 - u * (w : ℂ) ≠ 0 := by
      intro h
      have h1 : u * (w : ℂ) = 1 := (sub_eq_zero.mp h).symm
      simp only [h1, norm_one, lt_self_iff_false] at huw
    have heq : u⁻¹ - (w : ℂ) = u⁻¹ * (1 - u * (w : ℂ)) := by
      field_simp
    rw [heq, norm_mul, Real.log_mul
      (norm_ne_zero_iff.mpr (inv_ne_zero hu0)) (norm_ne_zero_iff.mpr hne)]
    ring
  have hire : Integrable (fun w : S ↦ f w * (-Real.log ‖1 - u * (w : ℂ)‖)) μ := by
    have hri := hi.re
    change Integrable (fun w : S ↦ ((f w : ℂ) * (-Complex.log (1 - u * (w : ℂ)))).re) μ at hri
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.log_re, zero_mul, sub_zero] using hri
  have hpot : Integrable (fun w : S ↦ f w * Real.log ‖u⁻¹ - (w : ℂ)‖) μ := by
    convert (hf.mul_const (Real.log ‖u⁻¹‖)).sub hire using 1
    funext w
    change f w * Real.log ‖u⁻¹ - (w : ℂ)‖ = f w * Real.log ‖u⁻¹‖ -
      f w * (-Real.log ‖1 - u * (w : ℂ)‖)
    rw [hkernel w]
    ring
  have hri := integral_re hi
  change (∫ w : S, ((f w : ℂ) * (-Complex.log (1 - u * (w : ℂ)))).re ∂μ) =
    (∫ w : S, (f w : ℂ) * (-Complex.log (1 - u * (w : ℂ))) ∂μ).re at hri
  rw [← hri]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.log_re, zero_mul, sub_zero]
  simp_rw [hkernel, mul_sub]
  rw [integral_sub (hf.mul_const _) hpot, integral_mul_const]

/-- Exterior equality of the actual logarithmic potentials forces equality of total masses. -/
theorem integral_eq_of_log_density_potential_eq {S T : Set ℂ} (hS : IsCompact S) (hT : IsCompact T)
    (μ : Measure S) (ν : Measure T) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : S → ℝ) (g : T → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    {R₀ : ℝ}
    (heq : ∀ z : ℂ, R₀ < ‖z‖ →
      (∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) =
        ∫ w : T, g w * Real.log ‖z - (w : ℂ)‖ ∂ν) :
    (∫ w : S, f w ∂μ) = ∫ w : T, g w ∂ν := by
  obtain ⟨M₁, _, hSM⟩ := hS.isBounded.exists_pos_norm_lt
  obtain ⟨M₂, _, hTM⟩ := hT.isBounded.exists_pos_norm_lt
  obtain ⟨R, hR⟩ := exists_gt (max (max M₁ M₂) (max R₀ 1))
  have hM₁R : M₁ < R :=
    lt_of_le_of_lt ((le_max_left M₁ M₂).trans (le_max_left _ _)) hR
  have hM₂R : M₂ < R :=
    lt_of_le_of_lt ((le_max_right M₁ M₂).trans (le_max_left _ _)) hR
  have hR₀R : R₀ < R :=
    lt_of_le_of_lt ((le_max_left R₀ 1).trans (le_max_right _ _)) hR
  have h1R : 1 < R :=
    lt_of_le_of_lt ((le_max_right R₀ 1).trans (le_max_right _ _)) hR
  have hRpos : 0 < R := lt_trans zero_lt_one h1R
  have hcircle :
      Real.circleAverage (fun z : ℂ ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) 0 R =
      Real.circleAverage (fun z : ℂ ↦ ∫ w : T, g w * Real.log ‖z - (w : ℂ)‖ ∂ν) 0 R := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    apply heq z
    rw [mem_sphere, dist_zero_right, abs_of_pos hRpos] at hz
    rwa [hz]
  rw [circleAverage_log_density_potential hS hRpos
    (fun w hw ↦ (hSM w hw).trans hM₁R) μ f hf,
    circleAverage_log_density_potential hT hRpos
    (fun w hw ↦ (hTM w hw).trans hM₂R) ν g hg] at hcircle
  exact mul_right_cancel₀ (ne_of_gt (Real.log_pos h1R)) hcircle

/-- Exterior equality of the actual logarithmic potentials forces every complex moment to agree. -/
theorem complex_moments_eq_of_log_density_potential_eq {S T : Set ℂ} (hS : IsCompact S) (hT : IsCompact T)
    (μ : Measure S) (ν : Measure T) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : S → ℝ) (g : T → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    {R₀ : ℝ}
    (heq : ∀ z : ℂ, R₀ < ‖z‖ →
      (∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) =
        ∫ w : T, g w * Real.log ‖z - (w : ℂ)‖ ∂ν) :
    ∀ n : ℕ, (∫ w : S, (f w : ℂ) * (w : ℂ) ^ n ∂μ) =
      ∫ w : T, (g w : ℂ) * (w : ℂ) ^ n ∂ν := by
  have hmass := integral_eq_of_log_density_potential_eq hS hT μ ν f g hf hg heq
  let F : ℂ → ℂ := fun u ↦
    (∫ w : S, (f w : ℂ) * (-Complex.log (1 - u * (w : ℂ))) ∂μ) -
      ∫ w : T, (g w : ℂ) * (-Complex.log (1 - u * (w : ℂ))) ∂ν
  have hpower := (hasFPowerSeriesAt_log_density_generating_function hS μ f hf).sub
    (hasFPowerSeriesAt_log_density_generating_function hT ν g hg)
  have hFan : AnalyticAt ℂ F 0 := hpower.analyticAt
  obtain ⟨M₁, _, hSM⟩ := hS.isBounded.exists_pos_norm_lt
  obtain ⟨M₂, _, hTM⟩ := hT.isBounded.exists_pos_norm_lt
  obtain ⟨M, hM⟩ := exists_gt (max (max M₁ M₂) (max R₀ 1))
  have hM₁M : M₁ < M :=
    lt_of_le_of_lt ((le_max_left M₁ M₂).trans (le_max_left _ _)) hM
  have hM₂M : M₂ < M :=
    lt_of_le_of_lt ((le_max_right M₁ M₂).trans (le_max_left _ _)) hM
  have hR₀M : R₀ < M :=
    lt_of_le_of_lt ((le_max_left R₀ 1).trans (le_max_right _ _)) hM
  have hSbound : ∀ w : S, ‖(w : ℂ)‖ ≤ M := fun w ↦ ((hSM w w.property).trans hM₁M).le
  have hTbound : ∀ w : T, ‖(w : ℂ)‖ ≤ M := fun w ↦ ((hTM w w.property).trans hM₂M).le
  have hRe : ∀ᶠ u : ℂ in 𝓝 0, (F u).re = 0 := by
    have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ * M < 1 / 2 :=
      (continuous_norm.mul_const M).continuousAt (gt_mem_nhds (by norm_num))
    filter_upwards [hsmall] with u hu
    by_cases hu0 : u = 0
    · subst u
      simp [F]
    · have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have hinv : R₀ < ‖u⁻¹‖ := by
        rw [norm_inv, inv_eq_one_div, lt_div_iff₀ hunorm]
        have := mul_le_mul_of_nonneg_right hR₀M.le hunorm.le
        nlinarith
      dsimp only [F]
      rw [Complex.sub_re, re_log_density_generating_function hSbound μ f hf hu0 hu.le,
        re_log_density_generating_function hTbound ν g hg hu0 hu.le,
        hmass, heq u⁻¹ hinv, sub_self]
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hFan.eventually_analyticAt.and hRe)
  obtain ⟨C, hC⟩ := AnalyticOnNhd.eq_const_of_re_eq_const
    (show AnalyticOnNhd ℂ F (ball 0 r) from fun z hz ↦ (hball z hz).1)
    (fun z hz ↦ (hball z hz).2) isOpen_ball (isConnected_ball hr)
  have hC0 : C = 0 := (hC 0 (mem_ball_self hr)).symm.trans (by simp [F])
  have hFzero : F =ᶠ[𝓝 0] 0 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with u hu
    exact (hC u hu).trans hC0
  have hseries := sub_eq_zero.mp (hpower.eq_zero_of_eventually hFzero)
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero, mul_one, integral_complex_ofReal] using congrArg Complex.ofReal hmass
  · have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) hseries
    simp only [FormalMultilinearSeries.coeff_ofScalars] at hcoeff
    exact (div_left_inj' (Nat.cast_ne_zero.mpr hn : (n : ℂ) ≠ 0)).mp hcoeff

/-- Every complex polynomial is integrable against an integrable real density on compact sources. -/
theorem integrable_polynomial_density {S : Set ℂ} (hS : IsCompact S) (μ : Measure S)
    (f : S → ℝ) (hf : Integrable f μ) (p : Polynomial ℂ) :
    Integrable (fun w : S ↦ (f w : ℂ) * p.eval (w : ℂ)) μ := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn p.continuousOn
  have hfc : Integrable (fun w : S ↦ (f w : ℂ)) μ := Complex.ofRealCLM.integrable_comp hf
  apply hfc.mul_bdd (c := C)
    ((p.continuous.comp continuous_subtype_val).measurable.aestronglyMeasurable)
  exact Eventually.of_forall (fun w ↦ hC w w.property)

/-- Exterior equality of the actual logarithmic potentials forces all complex polynomial integrals to agree. -/
theorem polynomial_integrals_eq_of_log_density_potential_eq {S T : Set ℂ} (hS : IsCompact S) (hT : IsCompact T)
    (μ : Measure S) (ν : Measure T) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : S → ℝ) (g : T → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    {R₀ : ℝ}
    (heq : ∀ z : ℂ, R₀ < ‖z‖ →
      (∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) =
        ∫ w : T, g w * Real.log ‖z - (w : ℂ)‖ ∂ν) :
    ∀ p : Polynomial ℂ, (∫ w : S, (f w : ℂ) * p.eval (w : ℂ) ∂μ) =
      ∫ w : T, (g w : ℂ) * p.eval (w : ℂ) ∂ν := by
  have hmom := complex_moments_eq_of_log_density_potential_eq hS hT μ ν f g hf hg heq
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp_rw [Polynomial.eval_add, mul_add]
    rw [integral_add (integrable_polynomial_density hS μ f hf p)
      (integrable_polynomial_density hS μ f hf q),
      integral_add (integrable_polynomial_density hT ν g hg p)
      (integrable_polynomial_density hT ν g hg q), hp, hq]
  | monomial n a =>
    simp_rw [Polynomial.eval_monomial]
    calc (∫ w : S, (f w : ℂ) * (a * (w : ℂ) ^ n) ∂μ) =
        a * ∫ w : S, (f w : ℂ) * (w : ℂ) ^ n ∂μ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with w
          ring
      _ = a * ∫ w : T, (g w : ℂ) * (w : ℂ) ^ n ∂ν := by rw [hmom n]
      _ = ∫ w : T, (g w : ℂ) * (a * (w : ℂ) ^ n) ∂ν := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with w
          ring
end Erdos1040

