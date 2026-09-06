import Erdos1040.AtomicAreaAssembly
import Erdos1040.PolynomialDensity
import Erdos1040.CapRotation
import Erdos1040.PositiveDensity

/-!
Conditional assembly from actual source-potential properties. The exterior
area estimate uses continuity of measure from above, so no collar regularity
or uniform convergence theorem is required. The classical source and
geometric properties remain explicit assumptions, not capacity theorems.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Erdos1040

theorem exists_L2_tolerance_for_small_sublevel_set (ν : Measure ℂ)
    [IsFiniteMeasure ν] (g : ℂ → ℝ) (hg : MemLp g 2 ν) (a : ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε)
    (ha : ν {z | g z < a + (δ : ℝ)} < ENNReal.ofReal ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ (f : ℂ → ℝ) (hf : MemLp f 2 ν),
      ‖hf.toLp f - hg.toLp g‖ < r → ν {z | f z < a} < ENNReal.ofReal ε := by
  let c : ℂ → ℝ := fun _ ↦ a
  have hc : MemLp c 2 ν := memLp_const a
  have ha' : ν {z | (g - c) z < (δ : ℝ)} < ENNReal.ofReal ε := by
    simpa only [Pi.sub_apply, c, sub_lt_iff_lt_add, add_comm] using ha
  obtain ⟨r, hr, hrs⟩ := exists_L2_tolerance_for_small_negative_set
    ν (g - c) (hg.sub hc) δ hδ ε hε ha'
  refine ⟨r, hr, fun f hf herr ↦ ?_⟩
  have hnear : ‖(hf.sub hc).toLp (f - c) - (hg.sub hc).toLp (g - c)‖ < r := by
    rw [MemLp.toLp_sub hf hc, MemLp.toLp_sub hg hc, sub_sub_sub_cancel_right]
    exact herr
  have hb := hrs (f - c) (hf.sub hc) hnear
  simpa only [Pi.sub_apply, c, sub_lt_zero] using hb

theorem exists_large_shift_small_exterior_set (ν : Measure ℂ) [IsFiniteMeasure ν]
    (K : Set ℂ) (hK : MeasurableSet K) (U V : ℂ → ℝ)
    (hU : AEMeasurable U ν) (hV : AEMeasurable V ν)
    (hpos : ∀ z ∉ K, 0 < U z) (C t ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, C < A ∧ 0 < A ∧
      ν {z | z ∉ K ∧ V z + A * U z < t} < ENNReal.ofReal ε := by
  let A0 := max C 0 + 1
  let B : ℕ → Set ℂ := fun n ↦ {z | z ∉ K ∧ V z + (A0 + n) * U z < t}
  have hB (n : ℕ) : NullMeasurableSet (B n) ν :=
    hK.compl.nullMeasurableSet.inter
      (nullMeasurableSet_lt (hV.add (aemeasurable_const.mul hU)) aemeasurable_const)
  have hanti : Antitone B := by
    intro n m hnm z hz
    refine ⟨hz.1, ?_⟩
    have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hmul := mul_le_mul_of_nonneg_right hnmR (hpos z hz.1).le
    change V z + (A0 + n) * U z < t
    have hzm := hz.2
    nlinarith
  have hempty : (⋂ n, B n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzall := Set.mem_iInter.mp hz
    have hp : 0 < U z := hpos z (hzall 0).1
    obtain ⟨n, hn⟩ := exists_nat_gt ((t - V z) / U z - A0)
    have hn' : (t - V z) / U z < A0 + n := by linarith
    have hlt := (div_lt_iff₀ hp).mp hn'
    have hzn := (hzall n).2
    linarith
  have ht := tendsto_measure_iInter_atTop hB hanti
    (show ∃ n : ℕ, ν (B n) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  rw [hempty, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const (ENNReal.ofReal_pos.mpr hε)).exists
  refine ⟨A0 + n, ?_, ?_, hn⟩
  · dsimp [A0]
    linarith [le_max_left C 0, Nat.cast_nonneg (α := ℝ) n]
  · dsimp [A0]
    linarith [le_max_right C 0, Nat.cast_nonneg (α := ℝ) n]

theorem shifted_source_potential_ae_eq {S D : Set ℂ} (hS : IsCompact S)
    (hD : IsCompact D) (μ : Measure S) [IsProbabilityMeasure μ]
    (f : S → ℝ) (hf : Measurable f) {C A : ℝ} (hfC : ∀ w, ‖f w‖ ≤ C)
    (hCA : C < A) :
    (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ.withDensity
      (fun w ↦ ENNReal.ofReal ((f w + A) / ((∫ w, f w ∂μ) + A))))
      =ᵐ[volume.restrict D]
    (fun z : ℂ ↦ ((∫ w : S, f w ∂μ) + A)⁻¹ *
      ((∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ) +
        A * ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)) := by
  filter_upwards [(integrable_log_norm_sub_prod hS hD μ).prod_left_ae] with z hz
  simpa only [smul_eq_mul] using integral_shifted_density μ f hf hfC hCA
    (fun w : S ↦ Real.log ‖z - (w : ℂ)‖) hz

theorem hasArbitrarilySmallLemniscates_of_potential_properties {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (hSK : S ⊆ K)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (hconn : IsPreconnected Kᶜ)
    (hboundary : frontier K ⊆ (μ.map ((↑) : S → ℂ)).support)
    (hpotential : ∀ z : ℂ, 0 ≤ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)
    (hstrict : ∀ z ∉ K, 0 < ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) :
    HasArbitrarilySmallLemniscates S := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn
    (continuous_id : Continuous (fun z : ℂ ↦ z)).continuousOn
  let M : ℝ := max M0 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKM : ∀ z ∈ K, ‖z‖ ≤ M := fun z hz ↦ (hM0 z hz).trans (le_max_left _ _)
  let D := Metric.closedBall (0 : ℂ) (M + 1)
  have hD : IsCompact D := isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hD.measure_lt_top.ne
  obtain ⟨P, hPmean, hPsmall⟩ :=
    exists_mean_zero_polynomial_large_off_small_area hS μ hM hε2
  let H : ℂ → ℝ := fun z ↦ (P.eval z).re
  have hHL2 : MemLp H 2 (volume.restrict K) := memLp_re_polynomial hK P
  have hHsmall : (volume.restrict K) {z | H z < (1 / 2 : ℝ) + (↑(1 / 4 : ℝ≥0) : ℝ)} <
      ENNReal.ofReal (ε / 2) := by
    rw [Measure.restrict_apply' hK.measurableSet]
    apply lt_of_le_of_lt (measure_mono ?_) hPsmall
    intro z hz
    refine ⟨hKM z hz.2, ?_⟩
    have hh := hz.1
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hh
    dsimp [H] at hh
    linarith
  obtain ⟨r, hr, hrs⟩ := exists_L2_tolerance_for_small_sublevel_set
    (volume.restrict K) H hHL2 (1 / 2) (1 / 4) (by norm_num) (ε / 2) hε2 hHsmall
  obtain ⟨f, hf, ⟨C, hfC⟩, hnear⟩ := exists_density_approx_re_polynomial
    hS hK hSK μ hconn hboundary hpotential P hPmean r hr
  let U : ℂ → ℝ := fun z ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ
  let V : ℂ → ℝ := fun z ↦ ∫ w : S, f w * Real.log ‖z - (w : ℂ)‖ ∂μ
  have hVK : MemLp V 2 (volume.restrict K) :=
    memLp_source_density_potential hS hK μ f hf C hfC
  have hVsmall : (volume.restrict K) {z | V z < 1 / 2} < ENNReal.ofReal (ε / 2) := by
    apply hrs V hVK
    have heq : hVK.toLp V = ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ :=
      source_density_potential_toLp_eq_integral_areaLogKernel hS hK μ f hf C hfC
    rw [heq]
    exact hnear
  have hUD : MemLp U 2 (volume.restrict D) := memLp_source_potential hS hD μ
  have hVD : MemLp V 2 (volume.restrict D) :=
    memLp_source_density_potential hS hD μ f hf C hfC
  obtain ⟨A, hCA, hA, houtside⟩ := exists_large_shift_small_exterior_set
    (volume.restrict D) K hK.measurableSet U V hUD.aestronglyMeasurable.aemeasurable
    hVD.aestronglyMeasurable.aemeasurable hstrict C (1 / 2) (ε / 2) hε2
  let m : ℝ := (∫ w : S, f w ∂μ) + A
  have hm : 0 < m := shifted_density_mass_pos μ f hf hfC hCA
  let σ : Measure S := μ.withDensity (fun w ↦ ENNReal.ofReal ((f w + A) / m))
  have : IsProbabilityMeasure σ := isProbabilityMeasure_shifted_density μ f hf hfC hCA
  let δ : ℝ≥0 := ⟨m⁻¹ * (1 / 2), by positivity⟩
  have hδ : 0 < δ := by change 0 < m⁻¹ * (1 / 2); positivity
  apply exists_roots_small_area_of_source_margin hS (fun w hw ↦ hKM w (hSK hw)) σ δ hδ ε hε
  let E : Set ℂ := {z | z ∈ K ∧ V z < 1 / 2}
  let B : Set ℂ := {z | z ∉ K ∧ V z + A * U z < 1 / 2}
  have hE : (volume.restrict D) E ≤ (volume.restrict K) {z | V z < 1 / 2} := by
    rw [Measure.restrict_apply' hD.measurableSet, Measure.restrict_apply' hK.measurableSet]
    apply measure_mono
    intro z hz
    exact ⟨hz.1.2, hz.1.1⟩
  have hform : (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂σ) =ᵐ[volume.restrict D]
      (fun z : ℂ ↦ m⁻¹ * (V z + A * U z)) :=
    shifted_source_potential_ae_eq hS hD μ f hf hfC hCA
  have hcover : ({z | (∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂σ) < (δ : ℝ)} : Set ℂ)
      ≤ᵐ[volume.restrict D] (E ∪ B : Set ℂ) := by
    filter_upwards [hform] with z hz
    intro hzbad
    change (∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂σ) < m⁻¹ * (1 / 2) at hzbad
    rw [hz] at hzbad
    have hraw : V z + A * U z < 1 / 2 :=
      (mul_lt_mul_iff_right₀ (inv_pos.mpr hm)).mp hzbad
    by_cases hzK : z ∈ K
    · exact Or.inl ⟨hzK, lt_of_le_of_lt
        (le_add_of_nonneg_right (mul_nonneg hA.le (hpotential z))) hraw⟩
    · exact Or.inr ⟨hzK, hraw⟩
  calc
    (volume.restrict D) {z | (∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂σ) < (δ : ℝ)} ≤
        (volume.restrict D) (E ∪ B) := measure_mono_ae hcover
    _ ≤ (volume.restrict D) E + (volume.restrict D) B := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add (hE.trans_lt hVsmall) houtside
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hε2.le hε2.le]
      congr 1
      ring

end Erdos1040
