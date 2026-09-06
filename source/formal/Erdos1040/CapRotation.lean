import Erdos1040.CapPolynomial

/-!
The complete mean-zero polynomial construction from cap separation, rotation
averaging, and planar strip area. The observation disk may have any positive
radius; it need not contain the compact source set. No source measure is
rotated, and this auxiliary polynomial is not a final root polynomial.
-/

noncomputable section

open MeasureTheory InnerProductSpace Metric Set Polynomial
open scoped Topology BigOperators

namespace Erdos1040

/-- Integrating a polynomial over compact sources after scalar multiplication
gives another polynomial, with the actual source integral as its evaluation. -/
theorem exists_polynomial_rotation_integral {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) [IsFiniteMeasure μ] (Q : ℂ[X]) :
    ∃ A : ℂ[X], ∀ u : ℂ, A.eval u = ∫ w : S, Q.eval (u * (w : ℂ)) ∂μ := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let A : ℂ[X] := ∑ n ∈ Q.support,
    monomial n (∫ w : S, Q.coeff n * (w : ℂ) ^ n ∂μ)
  refine ⟨A, fun u => ?_⟩
  have hi (n : ℕ) : Integrable (fun w : S => Q.coeff n * (u * (w : ℂ)) ^ n) μ := by
    have hc : Continuous (fun w : S => Q.coeff n * (u * (w : ℂ)) ^ n) := by fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  calc
    A.eval u = ∑ n ∈ Q.support, (∫ w : S, Q.coeff n * (w : ℂ) ^ n ∂μ) * u ^ n := by
      simp only [A, eval_finsetSum, eval_monomial]
    _ = ∑ n ∈ Q.support, ∫ w : S, Q.coeff n * (u * (w : ℂ)) ^ n ∂μ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with w
      rw [mul_pow]
      ring
    _ = ∫ w : S, ∑ n ∈ Q.support, Q.coeff n * (u * (w : ℂ)) ^ n ∂μ :=
      (integral_finsetSum Q.support (fun n _ => hi n)).symm
    _ = ∫ w : S, Q.eval (u * (w : ℂ)) ∂μ := by
      simp only [eval_eq_sum, Polynomial.sum]

/-- Some unit rotation gives a real source average at least the polynomial's
real value at zero. The source probability itself is unchanged. -/
theorem exists_unit_rotation_mean_ge_constant {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) [IsProbabilityMeasure μ] (Q : ℂ[X]) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ (Q.eval 0).re ≤ ∫ w : S, (Q.eval (u * (w : ℂ))).re ∂μ := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨A, hA⟩ := exists_polynomial_rotation_integral hS μ Q
  have hAc : Continuous (fun z : ℂ => (A.eval z).re) := Complex.continuous_re.comp A.continuous
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    ⟨1, by simp⟩ hAc.continuousOn
  have hhar : HarmonicOnNhd (fun z : ℂ => (A.eval z).re) (closedBall 0 |(1 : ℝ)|) :=
    fun z _ => ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) A) z (mem_univ z)).harmonicAt_re
  have havg : (A.eval 0).re ≤ (A.eval u).re := by
    rw [← hhar.circleAverage_eq]
    apply Real.circleAverage_mono_on_of_le_circle (hAc.continuousOn.circleIntegrable (by norm_num))
    intro z hz
    exact hmax (by simpa using hz)
  have hA0 : A.eval 0 = Q.eval 0 := by
    rw [hA]
    simp
  have hQi : Integrable (fun w : S => Q.eval (u * (w : ℂ))) μ := by
    have hc : Continuous (fun w : S => Q.eval (u * (w : ℂ))) :=
      Q.continuous.comp (continuous_const.mul continuous_subtype_val)
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  have hre : (A.eval u).re = ∫ w : S, (Q.eval (u * (w : ℂ))).re ∂μ := by
    rw [hA]
    exact (Complex.reCLM.integral_comp_comm hQi).symm
  refine ⟨u, mem_sphere_zero_iff_norm.mp hu, ?_⟩
  simpa only [hA0, hre] using havg

/-- Intersecting a radius-M disk with any rotated strip of half-width a
has planar area at most 4 M a. -/
theorem volume_rotated_strip_le {M a : ℝ} (hM : 0 ≤ M) (_ha : 0 ≤ a)
    {u : ℂ} (hu : ‖u‖ = 1) :
    volume {z : ℂ | ‖z‖ ≤ M ∧ |(u * z).im| ≤ a} ≤ ENNReal.ofReal (4 * M * a) := by
  let T : Set ℂ := {z : ℂ | |z.re| ≤ M ∧ |z.im| ≤ a}
  have hTm : MeasurableSet T :=
    (isClosed_le Complex.continuous_re.abs continuous_const).measurableSet.inter
      (isClosed_le Complex.continuous_im.abs continuous_const).measurableSet
  have hTv : volume T = ENNReal.ofReal (4 * M * a) := by
    have heq : T = Complex.measurableEquivRealProd ⁻¹'
        (Icc (-M) M ×ˢ Icc (-a) a) := by
      ext z
      simp only [T, mem_ofPred_eq, mem_preimage, mem_prod,
        Complex.measurableEquivRealProd_apply, mem_Icc, abs_le]
    rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by linarith : 0 ≤ M - -M)]
    congr 1
    ring
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { (LinearEquiv.smulOfNeZero ℂ ℂ u hu0).restrictScalars ℝ with
      norm_map' := by
        intro z
        change ‖u * z‖ = ‖z‖
        rw [norm_mul, hu, one_mul] }
  have hp : MeasurePreserving (fun z : ℂ => u * z) volume volume := e.measurePreserving
  calc
    volume {z : ℂ | ‖z‖ ≤ M ∧ |(u * z).im| ≤ a} ≤ volume ((fun z : ℂ => u * z) ⁻¹' T) := by
      apply measure_mono
      intro z hz
      refine ⟨(Complex.abs_re_le_norm (u * z)).trans ?_, hz.2⟩
      simpa only [norm_mul, hu, one_mul] using hz.1
    _ = volume T := hp.measure_preimage hTm.nullMeasurableSet
    _ = ENNReal.ofReal (4 * M * a) := hTv

/-- For any compact source probability and any positive-radius observation
disk, a polynomial has real source mean zero and real part greater than 3/4
outside a subset of that disk of arbitrarily small prescribed area. -/
theorem exists_mean_zero_polynomial_large_off_small_area {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) [IsProbabilityMeasure μ] {M η : ℝ} (hM : 0 < M) (hη : 0 < η) :
    ∃ P : ℂ[X], (∫ w : S, (P.eval (w : ℂ)).re ∂μ) = 0 ∧
      volume {z : ℂ | ‖z‖ ≤ M ∧ (P.eval z).re ≤ 3 / 4} < ENNReal.ofReal η := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let a : ℝ := min (M / 2) (η / (8 * M))
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haM : a < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hasmall : 4 * M * a < η := by
    calc
      4 * M * a ≤ 4 * M * (η / (8 * M)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = η / 2 := by field_simp [hM.ne'] <;> ring
      _ < η := by linarith
  obtain ⟨Q, hQ0, hQcap⟩ := exists_cap_polynomial ha haM
  obtain ⟨u, hu, humean⟩ := exists_unit_rotation_mean_ge_constant hS μ Q
  let A : ℝ := ∫ w : S, (Q.eval (u * (w : ℂ))).re ∂μ
  have hA : 1 ≤ A := by simpa only [hQ0, Complex.one_re] using humean
  let P : ℂ[X] := C (A : ℂ) - Q.comp (C u * X)
  have heval (z : ℂ) : (P.eval z).re = A - (Q.eval (u * z)).re := by simp [P]
  have hQi : Integrable (fun w : S => (Q.eval (u * (w : ℂ))).re) μ := by
    have hc : Continuous (fun w : S => (Q.eval (u * (w : ℂ))).re) :=
      Complex.continuous_re.comp (Q.continuous.comp (continuous_const.mul continuous_subtype_val))
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  refine ⟨P, ?_, ?_⟩
  · simp_rw [heval]
    rw [integral_sub (integrable_const A) hQi]
    simp [A]
  · calc
      volume {z : ℂ | ‖z‖ ≤ M ∧ (P.eval z).re ≤ 3 / 4} ≤
          volume {z : ℂ | ‖z‖ ≤ M ∧ |(u * z).im| ≤ a} := by
        apply measure_mono
        intro z hz
        refine ⟨hz.1, ?_⟩
        by_contra! hza
        have hnorm : ‖u * z‖ ≤ M := by simpa only [norm_mul, hu, one_mul] using hz.1
        have hq := hQcap (u * z) hnorm hza.le
        have hqre := Complex.re_le_norm (Q.eval (u * z))
        have hp := hz.2
        rw [heval] at hp
        linarith
      _ ≤ ENNReal.ofReal (4 * M * a) := volume_rotated_strip_le hM.le ha.le hu
      _ < ENNReal.ofReal η := (ENNReal.ofReal_lt_ofReal_iff hη).2 hasmall

end Erdos1040
