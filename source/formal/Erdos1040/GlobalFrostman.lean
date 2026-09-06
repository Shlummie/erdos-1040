import Erdos1040.EnergyFrostman
import Erdos1040.LogEnergyScale
import Erdos1040.PotentialHarmonic
import Erdos1040.HarmonicMaximum
import Erdos1040.SourceSupport
import Erdos1040.ExteriorPositivity

/-!
Pointwise logarithmic-potential foundations and the global Frostman bound.
The energy and potential retain infinity at singular points until finiteness
has been proved. No global potential inequality is assumed.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace Metric
open scoped ENNReal NNReal Topology
namespace Erdos1040

theorem lowerSemicontinuous_nonnegativeLogPotential {S : Set ℂ}
    (D : ℝ) (μ : ProbabilityMeasure S) :
    LowerSemicontinuous (nonnegativeLogPotential D μ) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro z
  have hc (w : S) : Continuous (fun v : ℂ ↦ nonnegativeLogKernel D v (w : ℂ)) := by
    have hpair : Continuous (fun v : ℂ ↦ (v, (w : ℂ))) :=
      continuous_id.prodMk continuous_const
    have hcomp := (continuous_nonnegativeLogKernel D).comp hpair
    exact hcomp
  have hm (v : ℂ) : Measurable (fun w : S ↦ nonnegativeLogKernel D v (w : ℂ)) :=
    ((continuous_nonnegativeLogKernel D).comp
      (continuous_const.prodMk continuous_subtype_val)).measurable
  calc
    nonnegativeLogPotential D μ z =
        ∫⁻ w : S, liminf (fun v : ℂ ↦ nonnegativeLogKernel D v (w : ℂ)) (𝓝 z) ∂μ := by
      apply lintegral_congr
      intro w
      exact (hc w).continuousAt.tendsto.liminf_eq.symm
    _ ≤ liminf (nonnegativeLogPotential D μ) (𝓝 z) := lintegral_liminf_le hm

theorem nonnegativeLogPotential_le_energy_on_support_of_minimizer {S : Set ℂ}
    (D : ℝ) (μ : ProbabilityMeasure S) (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    (hmin : ∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν) :
    ∀ z ∈ ((μ : Measure S).map ((↑) : S → ℂ)).support,
      nonnegativeLogPotential D μ z ≤ nonnegativeLogEnergy D μ := by
  have hc := (lowerSemicontinuous_nonnegativeLogPotential D μ).isClosed_preimage
    (nonnegativeLogEnergy D μ)
  apply Measure.support_subset_of_isClosed hc
  apply (ae_map_iff measurable_subtype_coe.aemeasurable hc.measurableSet).2
  exact (nonnegativeLogPotential_ae_eq_energy_of_minimizer D μ hμ hmin).le

theorem integrable_log_norm_sub_of_nonnegativeLogPotential_ne_top {S : Set ℂ}
    {D : ℝ} (hD : 0 < D) (μ : ProbabilityMeasure S) {z : ℂ}
    (hbound : ∀ w ∈ S, dist z w ≤ D)
    (hV : nonnegativeLogPotential D μ z ≠ ⊤) :
    Integrable (fun w : S ↦ Real.log ‖z - (w : ℂ)‖) (μ : Measure S) := by
  have hm : Measurable (fun w : S ↦ nonnegativeLogKernel D z (w : ℂ)) :=
    ((continuous_nonnegativeLogKernel D).comp
      (continuous_const.prodMk continuous_subtype_val)).measurable
  have hne : ∀ᵐ w : S ∂(μ : Measure S), z ≠ (w : ℂ) := by
    filter_upwards [ae_lt_top hm hV] with w hw
    intro hzw
    rw [hzw, nonnegativeLogKernel_self hD] at hw
    exact (lt_irrefl _ hw)
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hV
  apply ((integrable_const (Real.log D)).sub hi).congr
  filter_upwards [hne] with w hw
  change Real.log D - (nonnegativeLogKernel D z (w : ℂ)).toReal = Real.log ‖z - (w : ℂ)‖
  rw [nonnegativeLogKernel_toReal_of_dist_le hD hw (hbound w w.property), dist_eq_norm]
  ring

theorem nonnegativeLogPotential_toReal_eq_log_sub_integral {S : Set ℂ}
    {D : ℝ} (hD : 0 < D) (μ : ProbabilityMeasure S) {z : ℂ}
    (hbound : ∀ w ∈ S, dist z w ≤ D)
    (hV : nonnegativeLogPotential D μ z ≠ ⊤) :
    (nonnegativeLogPotential D μ z).toReal =
      Real.log D - ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ := by
  have hm : Measurable (fun w : S ↦ nonnegativeLogKernel D z (w : ℂ)) :=
    ((continuous_nonnegativeLogKernel D).comp
      (continuous_const.prodMk continuous_subtype_val)).measurable
  have hne : ∀ᵐ w : S ∂(μ : Measure S), z ≠ (w : ℂ) := by
    filter_upwards [ae_lt_top hm hV] with w hw
    intro hzw
    rw [hzw, nonnegativeLogKernel_self hD] at hw
    exact (lt_irrefl _ hw)
  have hi := integrable_log_norm_sub_of_nonnegativeLogPotential_ne_top hD μ hbound hV
  calc
    (nonnegativeLogPotential D μ z).toReal =
        ∫ w : S, (nonnegativeLogKernel D z (w : ℂ)).toReal ∂μ :=
      (integral_toReal hm.aemeasurable (ae_lt_top hm hV)).symm
    _ = ∫ w : S, Real.log D - Real.log ‖z - (w : ℂ)‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hne] with w hw
      simpa only [dist_eq_norm] using
        nonnegativeLogKernel_toReal_of_dist_le hD hw (hbound w w.property)
    _ = Real.log D - ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ := by
      rw [integral_sub (integrable_const _) hi]
      simp

theorem harmonic_nonpos_of_boundary_and_infinity {f : ℂ → ℝ} {U : Set ℂ}
    (hopen : IsOpen U) (hf : HarmonicOnNhd f U)
    (hbd : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝 ξ, z ∈ U → f z < ε)
    (hinfty : ∀ ε : ℝ, 0 < ε → ∀ᶠ z in cocompact ℂ, f z < ε) :
    ∀ x ∈ U, f x ≤ 0 := by
  have hclosed (ε : ℝ) (hε : 0 < ε) :
      IsClosed {z : ℂ | z ∈ U ∧ ε ≤ f z} := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    by_cases hyU : y ∈ U
    · have hylt : f y < ε := lt_of_not_ge (fun h ↦ hy ⟨hyU, h⟩)
      filter_upwards [(hf y hyU).1.continuousAt (gt_mem_nhds hylt)] with z hz
      exact fun hzK ↦ (not_le_of_gt hz) hzK.2
    · by_cases hycl : y ∈ closure U
      · have hybd : y ∈ frontier U := by
          rw [frontier, hopen.interior_eq]
          exact ⟨hycl, hyU⟩
        filter_upwards [hbd y hybd ε hε] with z hz
        exact fun hzK ↦ (not_le_of_gt (hz hzK.1)) hzK.2
      · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hycl] with z hz
        exact fun hzK ↦ hz (subset_closure hzK.1)
  intro x hx
  by_contra hpos
  have hxpos : 0 < f x := lt_of_not_ge hpos
  let K : Set ℂ := {z | z ∈ U ∧ f x ≤ f z}
  obtain ⟨L, hL, hLf⟩ := mem_cocompact.mp (hinfty (f x) hxpos)
  have hKL : K ⊆ L := by
    intro z hz
    by_contra hzL
    exact (not_le_of_gt (hLf hzL)) hz.2
  have hKcompact : IsCompact K := isCompact_of_isClosed_isBounded (hclosed (f x) hxpos)
    (hL.isBounded.subset hKL)
  obtain ⟨m, hm, hmaxK⟩ := hKcompact.exists_isMaxOn ⟨x, hx, le_rfl⟩
    (hf.continuousOn.mono (fun z hz ↦ hz.1))
  have hmaxU : IsMaxOn f U m := by
    intro y hy
    by_cases hyK : f x ≤ f y
    · exact hmaxK ⟨hy, hyK⟩
    · exact (le_of_lt (lt_of_not_ge hyK)).trans hm.2
  let A : Set ℂ := {z | z ∈ U ∧ f m ≤ f z}
  have hAopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hmaxy : IsMaxOn f U y := fun z hz ↦ (hmaxU hz).trans hy.2
    have hlocal := harmonic_eventually_eq_of_isLocalMax (hf y hy.1)
      (hmaxy.isLocalMax (hopen.mem_nhds hy.1))
    filter_upwards [hopen.mem_nhds hy.1, hlocal] with z hz heq
    exact ⟨hz, hy.2.trans_eq heq.symm⟩
  have hAuniv : A = Set.univ :=
    (show IsClopen A from
      ⟨hclosed (f m) (lt_of_lt_of_le hxpos hm.2), hAopen⟩).eq_univ ⟨m, hm.1, le_rfl⟩
  apply NormedSpace.unbounded_univ ℝ ℂ
  rw [← hAuniv]
  exact hKcompact.isBounded.subset (fun z hz ↦ ⟨hz.1, hm.2.trans hz.2⟩)

theorem eventually_neg_log_potential_lt_of_le_on_source {S : Set ℂ}
    (hS : IsCompact S) (hne : S.Nonempty) (μ : ProbabilityMeasure S)
    [NullSingletonClass (μ : Measure S)]
    (hI : ∀ z : ℂ, Integrable (fun w : S ↦ Real.log ‖z - (w : ℂ)‖) (μ : Measure S))
    (M : ℝ) (hM : ∀ z ∈ S, -(∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) ≤ M)
    {ξ : ℂ} (hξ : ξ ∈ S) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 ξ, -(∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) < M + ε := by
  choose a ha hdist using fun z : ℂ ↦ hS.exists_infDist_eq_dist hne z
  have hnear (z : ℂ) (w : S) : dist z (a z) ≤ dist z (w : ℂ) := by
    rw [← hdist z]
    exact infDist_le_dist_of_mem w.property
  have hratio (z : ℂ) (w : S) : dist (a z) (w : ℂ) ≤ 2 * dist z (w : ℂ) := by
    have ht := dist_triangle (a z) z (w : ℂ)
    rw [dist_comm (a z) z] at ht
    linarith [hnear z w]
  have hnearξ (z : ℂ) : dist (a z) ξ ≤ 2 * dist z ξ := by
    have ht := dist_triangle (a z) z ξ
    rw [dist_comm (a z) z] at ht
    linarith [hnear z ⟨ξ, hξ⟩]
  have haT : Tendsto a (𝓝 ξ) (𝓝 ξ) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [Metric.ball_mem_nhds ξ (half_pos hη)] with z hz
    exact lt_of_le_of_lt (hnearξ z) (by
      have hz' := Metric.mem_ball.mp hz
      linarith)
  have hnull (p : ℂ) : ∀ᵐ w : S ∂(μ : Measure S), (w : ℂ) ≠ p := by
    have hsub : Set.Subsingleton {w : S | (w : ℂ) = p} := by
      intro w hw v hv
      exact Subtype.ext (hw.trans hv.symm)
    exact measure_eq_zero_iff_ae_notMem.mp (hsub.measure_zero (μ : Measure S))
  let F : ℂ → S → ℝ := fun z w ↦
    max (Real.log ‖a z - (w : ℂ)‖ - Real.log ‖z - (w : ℂ)‖) 0
  have hFmeas (z : ℂ) : Measurable (F z) := by dsimp [F]; fun_prop
  have hFbound (z : ℂ) : ∀ᵐ w : S ∂(μ : Measure S), ‖F z w‖ ≤ Real.log 2 := by
    filter_upwards [hnull (a z), hnull z] with w hwA hwZ
    have hwa : 0 < ‖a z - (w : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwA.symm)
    have hwz : 0 < ‖z - (w : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwZ.symm)
    have hlog : Real.log ‖a z - (w : ℂ)‖ - Real.log ‖z - (w : ℂ)‖ ≤ Real.log 2 := by
      rw [← Real.log_div hwa.ne' hwz.ne']
      apply Real.log_le_log (div_pos hwa hwz)
      apply (div_le_iff₀ hwz).mpr
      simpa only [dist_eq_norm] using hratio z w
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le hlog (Real.log_nonneg (by norm_num))
  have hFI (z : ℂ) : Integrable (F z) (μ : Measure S) :=
    (integrable_const (Real.log 2)).mono' (hFmeas z).aestronglyMeasurable (hFbound z)
  have hFlim : ∀ᵐ w : S ∂(μ : Measure S), Tendsto (fun z : ℂ ↦ F z w) (𝓝 ξ) (𝓝 0) := by
    filter_upwards [hnull ξ] with w hw
    have hn : ‖ξ - (w : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw.symm)
    have h1 := ((haT.sub_const (w : ℂ)).norm).log hn
    have h2 := (((tendsto_id : Tendsto (fun z : ℂ ↦ z) (𝓝 ξ) (𝓝 ξ)).sub_const
      (w : ℂ)).norm).log hn
    simpa only [sub_self, max_self, id_eq, F] using (h1.sub h2).max
      (tendsto_const_nhds : Tendsto (fun _ : ℂ ↦ (0 : ℝ)) (𝓝 ξ) (𝓝 0))
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun _ : S ↦ Real.log 2)
    (Eventually.of_forall fun z ↦ (hFmeas z).aestronglyMeasurable)
    (Eventually.of_forall hFbound) (integrable_const _) hFlim
  simp only [integral_zero] at ht
  filter_upwards [ht.eventually_lt_const hε] with z hz
  have hidiff : -(∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) =
      -(∫ w : S, Real.log ‖a z - (w : ℂ)‖ ∂μ) +
        ∫ w : S, Real.log ‖a z - (w : ℂ)‖ - Real.log ‖z - (w : ℂ)‖ ∂μ := by
    rw [integral_sub (hI (a z)) (hI z)]
    ring
  calc
    -(∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) =
        -(∫ w : S, Real.log ‖a z - (w : ℂ)‖ ∂μ) +
          ∫ w : S, Real.log ‖a z - (w : ℂ)‖ - Real.log ‖z - (w : ℂ)‖ ∂μ := hidiff
    _ ≤ M + ∫ w : S, F z w ∂μ := add_le_add (hM (a z) (ha z))
      (integral_mono ((hI (a z)).sub (hI z)) (hFI z) (fun _ ↦ le_max_left _ _))
    _ < M + ε := by linarith


theorem integrable_log_norm_sub_of_finite_minimizer {S : Set ℂ}
    (hS : IsCompact S) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (μ : ProbabilityMeasure S) (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    (hmin : ∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν)
    (z : ℂ) :
    Integrable (fun w : S ↦ Real.log ‖z - (w : ℂ)‖) (μ : Measure S) := by
  by_cases hz : z ∈ sourceSupport μ
  · have hV := nonnegativeLogPotential_le_energy_on_support_of_minimizer D μ hμ hmin z hz
    exact integrable_log_norm_sub_of_nonnegativeLogPotential_ne_top hD μ
      (hbound z (sourceSupport_subset hS.isClosed μ hz)) (ne_top_of_le_ne_top hμ hV)
  · exact integrable_source_potential_of_notMem_support hS μ hz

theorem log_source_potential_ge_of_finite_minimizer {S : Set ℂ}
    (hS : IsCompact S) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (μ : ProbabilityMeasure S) (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    (hmin : ∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν) :
    ∀ z : ℂ, Real.log D - (nonnegativeLogEnergy D μ).toReal ≤
      ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ := by
  let T : Set ℂ := sourceSupport μ
  have hT : IsCompact T := isCompact_sourceSupport hS μ
  have hTS : T ⊆ S := sourceSupport_subset hS.isClosed μ
  let ν := sourceProbabilityOnSupport μ
  have : NullSingletonClass (μ : Measure S) :=
    nullSingletonClass_of_finite_nonnegativeLogEnergy hD μ hμ
  have : NullSingletonClass (ν : Measure T) := nullSingletonClass_sourceProbabilityOnSupport μ
  let U : ℂ → ℝ := fun z ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ
  let M : ℝ := (nonnegativeLogEnergy D μ).toReal - Real.log D
  have hI (z : ℂ) : Integrable (fun w : S ↦ Real.log ‖z - (w : ℂ)‖) (μ : Measure S) :=
    integrable_log_norm_sub_of_finite_minimizer hS hD hbound μ hμ hmin z
  have hIν (z : ℂ) : Integrable (fun w : T ↦ Real.log ‖z - (w : ℂ)‖) (ν : Measure T) :=
    (integrable_sourceProbabilityOnSupport_iff hS.measurableSet μ
      (fun w : ℂ ↦ Real.log ‖z - w‖)).mpr (hI z)
  have hUeq (z : ℂ) : (∫ w : T, Real.log ‖z - (w : ℂ)‖ ∂ν) = U z :=
    integral_sourceProbabilityOnSupport hS.measurableSet μ
      (fun w : ℂ ↦ Real.log ‖z - w‖)
  have hM (z : ℂ) (hz : z ∈ T) : -U z ≤ M := by
    have hV := nonnegativeLogPotential_le_energy_on_support_of_minimizer D μ hμ hmin z hz
    have hVreal := ENNReal.toReal_mono hμ hV
    have heq := nonnegativeLogPotential_toReal_eq_log_sub_integral hD μ
      (hbound z (hTS hz)) (ne_top_of_le_ne_top hμ hV)
    dsimp [U, M]
    linarith
  have hMν (z : ℂ) (hz : z ∈ T) :
      -(∫ w : T, Real.log ‖z - (w : ℂ)‖ ∂ν) ≤ M := by
    rw [hUeq]
    exact hM z hz
  let f : ℂ → ℝ := fun z ↦ -U z - M
  have hf : HarmonicOnNhd f Tᶜ := by
    intro z hz
    exact ((harmonicOnNhd_source_potential_compl_support hS μ) z hz).neg.sub
      (harmonicAt_const M)
  have hbd : ∀ ξ ∈ frontier Tᶜ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝 ξ, z ∈ Tᶜ → f z < ε := by
    intro ξ hξ ε hε
    have hξT : ξ ∈ T := by
      rw [frontier_compl] at hξ
      exact hT.isClosed.closure_eq ▸ frontier_subset_closure hξ
    have hb := eventually_neg_log_potential_lt_of_le_on_source hT
      (sourceSupport_nonempty μ) ν hIν M hMν hξT ε hε
    filter_upwards [hb] with z hz
    intro _
    rw [hUeq] at hz
    dsimp [f]
    linarith
  have hinfty : ∀ ε : ℝ, 0 < ε → ∀ᶠ z in cocompact ℂ, f z < ε := by
    intro ε _
    filter_upwards [(tendsto_log_source_potential_atTop hS μ).eventually_gt_atTop
      (-M - ε)] with z hz
    change -U z - M < ε
    change -M - ε < U z at hz
    linarith
  have hmax := harmonic_nonpos_of_boundary_and_infinity hT.isClosed.isOpen_compl hf hbd hinfty
  intro z
  have hzM : -U z ≤ M := by
    by_cases hz : z ∈ T
    · exact hM z hz
    · have hzmax := hmax z hz
      dsimp [f] at hzmax
      linarith
  dsimp [U, M] at hzM
  linarith


end Erdos1040
