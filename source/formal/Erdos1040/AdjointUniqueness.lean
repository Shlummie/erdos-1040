import Erdos1040.SourceDensity
import Erdos1040.PotentialHarmonic
import Erdos1040.AdjointCircleMean
import Erdos1040.HarmonicMaximum
import Erdos1040.PotentialMoments

/-!
The reviewed sign-and-circle-mean adjoint uniqueness argument, conditional on
its explicit geometric support and nonnegative source-potential hypotheses.
The source measure is a probability, and the real area mass may have either
sign or be zero. No boundary regularity, boundary continuity of the source
potential, or global harmonic conjugate is assumed.
-/

noncomputable section

open MeasureTheory InnerProductSpace Metric Set Filter
open scoped Topology InnerProductSpace
namespace Erdos1040

/-- Conditional adjoint uniqueness from explicit source-support and potential
hypotheses. These hypotheses are classical inputs still required by the
capacity-one application; this theorem does not establish them. -/
theorem adjointAreaPotential_eq_mass_mul_source_potential_of_annihilator {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (hSK : S ⊆ K) (μ : Measure S) [IsProbabilityMeasure μ]
    (hconn : IsPreconnected Kᶜ)
    (hboundary : frontier K ⊆ (μ.map ((↑) : S → ℂ)).support)
    (hpotential : ∀ z : ℂ, 0 ≤ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)
    (h : Lp ℝ 2 (volume.restrict K))
    (horth : ∀ f : S → ℝ, Measurable f → (∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) →
      ⟪h, ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ = 0) :
    ∀ z : ℂ, z ∉ K → adjointAreaPotential hK h z =
      (∫ w in K, h w) * (∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) := by
  let μK : Measure K := (volume : Measure ℂ).comap ((↑) : K → ℂ)
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hhi : Integrable (fun w : K ↦ h w) μK :=
    (integrableOn_iff_comap_subtypeVal hK.measurableSet).mp
      (MemLp.integrable (by norm_num) (Lp.memLp h))
  let c : ℝ := ∫ w in K, h w
  let U : ℂ → ℝ := fun z ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ
  let W : ℂ → ℝ := fun z ↦ adjointAreaPotential hK h z - c * U z
  have hArep : (fun z : ℂ ↦ ∫ w : K, h w * Real.log ‖z - (w : ℂ)‖ ∂μK) =
      adjointAreaPotential hK h := by
    funext z
    exact integral_subtype_comap hK.measurableSet
      (fun w : ℂ ↦ h w * Real.log ‖z - w‖)
  have hMassrep : (∫ w : K, h w ∂μK) = c :=
    integral_subtype_comap hK.measurableSet (fun w : ℂ ↦ h w)
  have hAhar : HarmonicOnNhd (adjointAreaPotential hK h) Kᶜ := by
    simpa only [hArep] using harmonicOnNhd_log_density_potential_compl hK μK
      (fun w : K ↦ h w) hhi
  have hUhar : HarmonicOnNhd U Kᶜ := by
    intro z hz
    simpa only [one_mul] using harmonicAt_log_density_potential hS μ
      (fun _ : S ↦ (1 : ℝ)) (integrable_const 1)
      (show z ∉ S from fun hzS ↦ hz (hSK hzS))
  have hWhar : HarmonicOnNhd W Kᶜ := by
    simpa only [W, Pi.sub_def, Pi.smul_def, smul_eq_mul] using
      hAhar.sub (hUhar.const_smul (c := c))
  have hAlim : Tendsto (fun z : ℂ ↦ adjointAreaPotential hK h z - c * Real.log ‖z‖)
      (cocompact ℂ) (𝓝 0) := by
    have hArep' := congrFun hArep
    simpa only [hArep', hMassrep] using tendsto_log_density_potential_sub_mass_log hK μK
      (fun w : K ↦ h w) hhi
  have hUlim : Tendsto (fun z : ℂ ↦ U z - Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
    simpa [U] using tendsto_log_density_potential_sub_mass_log hS μ
      (fun _ : S ↦ (1 : ℝ)) (integrable_const 1)
  have hWlim : Tendsto W (cocompact ℂ) (𝓝 0) := by
    convert! hAlim.sub (hUlim.const_mul c) using 1
    · funext z
      dsimp [W]
      ring
    · simp
  have hsupport := adjointAreaPotential_zero_on_support_of_annihilator hS hK μ h horth
  have hbd : ∀ z ∈ frontier Kᶜ, adjointAreaPotential hK h z = 0 := by
    intro z hz
    exact hsupport z (hboundary (by simpa only [frontier_compl] using hz))
  have hunbounded : ¬ Bornology.IsBounded Kᶜ := by
    intro hb
    apply NormedSpace.unbounded_univ ℝ ℂ
    simpa only [union_compl_self] using hK.isBounded.union hb
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  have hSR : ∀ w ∈ S, ‖w‖ < R := fun w hw ↦ hKR w (hSK hw)
  have hcircle : sphere (0 : ℂ) R ⊆ Kᶜ := by
    intro z hz hzK
    have hzR : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    exact (hKR z hzK).ne hzR
  have hAcircle : CircleIntegrable (adjointAreaPotential hK h) 0 R :=
    (continuous_adjointAreaPotential hK h).continuousOn.circleIntegrable hR.le
  have hUcircle : CircleIntegrable U 0 R :=
    (hUhar.continuousOn.mono hcircle).circleIntegrable hR.le
  have hUmean : Real.circleAverage U 0 R = Real.log R := by
    simpa [U] using circleAverage_log_density_potential hS hR hSR μ
      (fun _ : S ↦ (1 : ℝ)) (integrable_const 1)
  have hWmean : Real.circleAverage W 0 R = 0 := by
    change Real.circleAverage (adjointAreaPotential hK h - c • U) 0 R = 0
    rw [Real.circleAverage_sub hAcircle hUcircle.const_smul, Real.circleAverage_smul,
      circleAverage_adjointAreaPotential hK h hR hKR, hUmean]
    simp [c, smul_eq_mul]
  by_cases hc : 0 ≤ c
  · have hnonpos : ∀ z ∈ Kᶜ, W z ≤ 0 :=
      harmonic_nonpos_of_continuous_majorant hconn hK.isClosed.isOpen_compl hunbounded
        hWhar (continuous_adjointAreaPotential hK h) hbd
        (fun z _ ↦ sub_le_self _ (mul_nonneg hc (hpotential z))) hWlim
    have hzero := harmonic_eq_zero_of_nonpos_of_circleAverage_zero hconn
      hK.isClosed.isOpen_compl hWhar hnonpos hR hcircle hWmean
    intro z hz
    exact sub_eq_zero.mp (hzero hz)
  · have hnegLim : Tendsto (fun z ↦ -W z) (cocompact ℂ) (𝓝 0) := by
      simpa only [neg_zero] using hWlim.neg
    have hnonpos : ∀ z ∈ Kᶜ, -W z ≤ 0 :=
      harmonic_nonpos_of_continuous_majorant hconn hK.isClosed.isOpen_compl hunbounded
        hWhar.neg (continuous_adjointAreaPotential hK h).neg
        (fun z hz ↦ by simp only [Pi.neg_apply, hbd z hz, neg_zero])
        (fun z _ ↦ by
          dsimp [W]
          have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (hpotential z)
          linarith) hnegLim
    have hnegMean : Real.circleAverage (fun z ↦ -W z) 0 R = 0 := by
      simpa only [neg_one_smul, hWmean, smul_zero] using
        (Real.circleAverage_fun_smul (a := (-1 : ℝ)) (f := W) (c := 0) (R := R))
    have hzero := harmonic_eq_zero_of_nonpos_of_circleAverage_zero hconn
      hK.isClosed.isOpen_compl hWhar.neg hnonpos hR hcircle hnegMean
    intro z hz
    exact sub_eq_zero.mp (neg_eq_zero.mp (hzero hz))
/-- Under the same explicit classical hypotheses, every annihilating real
area density has the stated pairing against the real part of every complex
polynomial. This is a conditional supporting identity for the density argument. -/
theorem integral_area_mul_re_polynomial_eq_mass_mul_source_integral_of_annihilator {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (hSK : S ⊆ K) (μ : Measure S) [IsProbabilityMeasure μ]
    (hconn : IsPreconnected Kᶜ)
    (hboundary : frontier K ⊆ (μ.map ((↑) : S → ℂ)).support)
    (hpotential : ∀ z : ℂ, 0 ≤ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)
    (h : Lp ℝ 2 (volume.restrict K))
    (horth : ∀ f : S → ℝ, Measurable f → (∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) →
      ⟪h, ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ = 0)
    (p : Polynomial ℂ) :
    (∫ z in K, h z * (p.eval z).re) =
      (∫ z in K, h z) * ∫ w : S, (p.eval (w : ℂ)).re ∂μ := by
  let μK : Measure K := (volume : Measure ℂ).comap ((↑) : K → ℂ)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasureOnCompacts μK :=
    IsFiniteMeasureOnCompacts.comap' (volume : Measure ℂ) continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hK.measurableSet)
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hhi : Integrable (fun w : K ↦ h w) μK :=
    (integrableOn_iff_comap_subtypeVal hK.measurableSet).mp
      (MemLp.integrable (by norm_num) (Lp.memLp h))
  let c : ℝ := ∫ z in K, h z
  have huniq := adjointAreaPotential_eq_mass_mul_source_potential_of_annihilator
    hS hK hSK μ hconn hboundary hpotential h horth
  obtain ⟨R, _, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  have heq : ∀ z : ℂ, R < ‖z‖ →
      (∫ w : K, h w * Real.log ‖z - (w : ℂ)‖ ∂μK) =
      ∫ w : S, c * Real.log ‖z - (w : ℂ)‖ ∂μ := by
    intro z hz
    calc (∫ w : K, h w * Real.log ‖z - (w : ℂ)‖ ∂μK) =
        adjointAreaPotential hK h z :=
          integral_subtype_comap hK.measurableSet
            (fun w : ℂ ↦ h w * Real.log ‖z - w‖)
      _ = c * ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ :=
        huniq z (fun hzK ↦ (not_le_of_gt (hKR z hzK)) hz.le)
      _ = ∫ w : S, c * Real.log ‖z - (w : ℂ)‖ ∂μ := (integral_const_mul _ _).symm
  have hpoly := polynomial_integrals_eq_of_log_density_potential_eq hK hS μK μ
    (fun w : K ↦ h w) (fun _ : S ↦ c) hhi (integrable_const c) heq p
  have hleft := integrable_polynomial_density hK μK (fun w : K ↦ h w) hhi p
  have hright := integrable_polynomial_density hS μ (fun _ : S ↦ c) (integrable_const c) p
  have hre := congrArg Complex.re hpoly
  change Complex.reCLM (∫ w : K, (h w : ℂ) * p.eval (w : ℂ) ∂μK) =
    Complex.reCLM (∫ w : S, (c : ℂ) * p.eval (w : ℂ) ∂μ) at hre
  rw [← Complex.reCLM.integral_comp_comm hleft,
    ← Complex.reCLM.integral_comp_comm hright] at hre
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  calc (∫ z in K, h z * (p.eval z).re) =
      ∫ w : K, h w * (p.eval (w : ℂ)).re ∂μK :=
        (integral_subtype_comap hK.measurableSet (fun z : ℂ ↦ h z * (p.eval z).re)).symm
    _ = ∫ w : S, c * (p.eval (w : ℂ)).re ∂μ := hre
    _ = c * ∫ w : S, (p.eval (w : ℂ)).re ∂μ := integral_const_mul _ _
end Erdos1040

