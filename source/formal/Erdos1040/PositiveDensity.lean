import Erdos1040.SourceDensity

/-!
An actual probability measure obtained by adding a sufficiently large
constant to a bounded signed source density and normalizing its mass.
The integral identity applies to Banach-valued kernels, including area L2.
-/

noncomputable section

open MeasureTheory

namespace Erdos1040

theorem shifted_density_mass_pos {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    {C A : ℝ} (hfC : ∀ w, ‖f w‖ ≤ C) (hCA : C < A) :
    0 < (∫ w, f w ∂μ) + A := by
  have hfi : Integrable f μ :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hfC))
  have hlower : -C ≤ ∫ w, f w ∂μ := by
    calc -C = ∫ _ : X, -C ∂μ := by simp
      _ ≤ ∫ w, f w ∂μ := integral_mono (integrable_const _) hfi
        (fun w ↦ (abs_le.mp (show |f w| ≤ C from by
          simpa [Real.norm_eq_abs] using hfC w)).1)
  linarith

theorem isProbabilityMeasure_shifted_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    {C A : ℝ} (hfC : ∀ w, ‖f w‖ ≤ C) (hCA : C < A) :
    IsProbabilityMeasure (μ.withDensity
      (fun w ↦ ENNReal.ofReal ((f w + A) / ((∫ w, f w ∂μ) + A)))) := by
  have hmass := shifted_density_mass_pos μ f hf hfC hCA
  have hfi : Integrable f μ :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hfC))
  have hnonneg (w : X) : 0 ≤ (f w + A) / ((∫ w, f w ∂μ) + A) := by
    have hl := (abs_le.mp (show |f w| ≤ C from by simpa [Real.norm_eq_abs] using hfC w)).1
    exact div_nonneg (by linarith) hmass.le
  apply isProbabilityMeasure_iff.mpr
  have hdi : Integrable (fun w ↦ (f w + A) / ((∫ w, f w ∂μ) + A)) μ :=
    (hfi.add (integrable_const A)).div_const _
  have hsum : (∫ w, f w + A ∂μ) = (∫ w, f w ∂μ) + A := by
    simpa using integral_add hfi (integrable_const A)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hdi (Filter.Eventually.of_forall hnonneg),
    integral_div, hsum]
  simp [hmass.ne']

theorem integral_shifted_density {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    {C A : ℝ} (hfC : ∀ w, ‖f w‖ ≤ C) (hCA : C < A)
    (g : X → E) (hg : Integrable g μ) :
    (∫ w, g w ∂μ.withDensity
      (fun w ↦ ENNReal.ofReal ((f w + A) / ((∫ w, f w ∂μ) + A)))) =
      ((∫ w, f w ∂μ) + A)⁻¹ • ((∫ w, f w • g w ∂μ) + A • ∫ w, g w ∂μ) := by
  have hmass := shifted_density_mass_pos μ f hf hfC hCA
  have hnonneg (w : X) : 0 ≤ (f w + A) / ((∫ w, f w ∂μ) + A) := by
    have hl := (abs_le.mp (show |f w| ≤ C from by simpa [Real.norm_eq_abs] using hfC w)).1
    exact div_nonneg (by linarith) hmass.le
  rw [integral_withDensity_eq_integral_toReal_smul
    ((hf.add_const A).div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hnonneg _), div_eq_inv_mul, mul_smul, add_smul]
  have hfg : Integrable (fun w ↦ f w • g w) μ :=
    hg.bdd_smul C hf.aestronglyMeasurable (Filter.Eventually.of_forall hfC)
  have hAg : Integrable (fun w ↦ A • g w) μ := hg.smul A
  rw [integral_smul, integral_add hfg hAg, integral_smul]

end Erdos1040
