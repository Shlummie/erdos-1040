import Mathlib

/-!
The ordinary strong maximum principle for real harmonic functions on complex
domains. Harmonic conjugates are constructed only on local disks; the domain
need not be simply connected and no boundary regularity is assumed.
-/

noncomputable section

open InnerProductSpace Metric Set Filter
open scoped Topology

namespace Erdos1040

/-- A real harmonic function with a local maximum is locally constant there. -/
theorem harmonic_eventually_eq_of_isLocalMax {f : ℂ → ℝ} {c : ℂ}
    (hf : HarmonicAt f c) (hmax : IsLocalMax f c) :
    ∀ᶠ z in 𝓝 c, f z = f c := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hf.eventually
  obtain ⟨F, hF, hFre⟩ :=
    (show HarmonicOnNhd f (ball c r) from hball).exists_analyticOnNhd_ball_re_eq
  have hcball : c ∈ ball c r := mem_ball_self hr
  have hFc : (F c).re = f c := hFre hcball
  have heqF : ∀ᶠ z in 𝓝 c, (F z).re = f z := by
    filter_upwards [ball_mem_nhds c hr] with z hz
    exact hFre hz
  have hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ (fun w ↦ Complex.exp (F w)) z := by
    filter_upwards [ball_mem_nhds c hr] with z hz
    exact Complex.differentiable_exp.differentiableAt.comp z (hF z hz).differentiableAt
  have hm : IsLocalMax (norm ∘ fun z ↦ Complex.exp (F z)) c := by
    filter_upwards [hmax, heqF] with z hz hzF
    simpa only [Function.comp_apply, Complex.norm_exp, hzF, hFc] using
      (Real.exp_le_exp.mpr hz)
  have heq := Complex.norm_eventually_eq_of_isLocalMax hd hm
  filter_upwards [heq, heqF] with z hz hzF
  apply Real.exp_injective
  simpa only [Complex.norm_exp, hzF, hFc] using hz

/-- A real harmonic function attaining its maximum on an open connected
complex domain is constant throughout that domain. -/
theorem harmonic_eqOn_of_isPreconnected_of_isMaxOn {f : ℂ → ℝ} {U : Set ℂ} {c : ℂ}
    (hU : IsPreconnected U) (hopen : IsOpen U) (hf : HarmonicOnNhd f U)
    (hc : c ∈ U) (hmax : IsMaxOn f U c) :
    EqOn f (fun _ ↦ f c) U := by
  let V : Set ℂ := U ∩ {z | IsMaxOn f U z}
  have hV : ∀ x ∈ V, f x = f c :=
    fun x hx ↦ le_antisymm (hmax hx.1) (hx.2 hc)
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hlocal : IsLocalMax f x := hx.2.isLocalMax (hopen.mem_nhds hx.1)
    filter_upwards [hopen.mem_nhds hx.1,
      harmonic_eventually_eq_of_isLocalMax (hf x hx.1) hlocal] with y hy hxy
    exact ⟨hy, fun z hz ↦ (hx.2 hz).trans_eq hxy.symm⟩
  have hVne : (U ∩ V).Nonempty := ⟨c, hc, hc, hmax⟩
  let W : Set ℂ := U ∩ {z | f z ≠ f c}
  have hWo : IsOpen W := hf.continuousOn.isOpen_inter_preimage hopen isOpen_ne
  have hdVW : Disjoint V W := disjoint_left.mpr fun x hxV hxW ↦ hxW.2 (hV x hxV)
  have hUVW : U ⊆ V ∪ W := fun x hx ↦
    (eq_or_ne (f x) (f c)).imp
      (fun h ↦ ⟨hx, fun y hy ↦ (hmax hy).trans_eq h.symm⟩) (And.intro hx)
  have hUV : U ⊆ V := hU.subset_left_of_subset_union hVo hWo hdVW hUVW hVne
  exact fun x hx ↦ hV x (hUV hx)

/-- A harmonic function on an unbounded open connected domain is nonpositive
if it tends to zero at infinity and has a continuous majorant vanishing on
the entire boundary. No continuity of the harmonic function at the boundary
and no regularity of the boundary are assumed. -/
theorem harmonic_nonpos_of_continuous_majorant {f g : ℂ → ℝ} {U : Set ℂ}
    (hU : IsPreconnected U) (hopen : IsOpen U)
    (hunbounded : ¬ Bornology.IsBounded U) (hf : HarmonicOnNhd f U)
    (hg : Continuous g) (hbd : ∀ x ∈ frontier U, g x = 0)
    (hfg : ∀ x ∈ U, f x ≤ g x)
    (hzero : Tendsto f (cocompact ℂ) (𝓝 0)) :
    ∀ x ∈ U, f x ≤ 0 := by
  intro x hx
  by_contra hpos
  have hxpos : 0 < f x := lt_of_not_ge hpos
  let K : Set ℂ := {z | z ∈ U ∧ f x ≤ f z}
  have hKclosed : IsClosed K := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    by_cases hyU : y ∈ U
    · have hylt : f y < f x := lt_of_not_ge (fun h ↦ hy ⟨hyU, h⟩)
      filter_upwards [(hf y hyU).1.continuousAt (gt_mem_nhds hylt)] with z hz
      exact fun hzK ↦ (not_le_of_gt hz) hzK.2
    · by_cases hycl : y ∈ closure U
      · have hybd : y ∈ frontier U := by
          rw [frontier, hopen.interior_eq]
          exact ⟨hycl, hyU⟩
        have hylt : g y < f x := by simpa only [hbd y hybd] using hxpos
        filter_upwards [hg.continuousAt (gt_mem_nhds hylt)] with z hz
        exact fun hzK ↦ (not_le_of_gt hz) (hzK.2.trans (hfg z hzK.1))
      · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hycl] with z hz
        exact fun hzK ↦ hz (subset_closure hzK.1)
  obtain ⟨L, hL, hLf⟩ := mem_cocompact.mp (hzero (gt_mem_nhds hxpos))
  have hKL : K ⊆ L := by
    intro z hz
    by_contra hzL
    exact (not_le_of_gt (hLf hzL)) hz.2
  have hKcompact : IsCompact K := isCompact_of_isClosed_isBounded hKclosed
    (hL.isBounded.subset hKL)
  obtain ⟨m, hm, hmaxK⟩ := hKcompact.exists_isMaxOn ⟨x, hx, le_rfl⟩
    (hf.continuousOn.mono (fun z hz ↦ hz.1))
  have hmaxU : IsMaxOn f U m := by
    intro y hy
    by_cases hyK : f x ≤ f y
    · exact hmaxK ⟨hy, hyK⟩
    · exact (le_of_lt (lt_of_not_ge hyK)).trans hm.2
  have hconst := harmonic_eqOn_of_isPreconnected_of_isMaxOn hU hopen hf hm.1 hmaxU
  apply hunbounded
  apply hKcompact.isBounded.subset
  intro z hz
  exact ⟨hz, hm.2.trans_eq (hconst hz).symm⟩

/-- A nonpositive harmonic function with zero mean on one circle lying in
an open connected domain vanishes throughout the domain. -/
theorem harmonic_eq_zero_of_nonpos_of_circleAverage_zero
    {f : ℂ → ℝ} {U : Set ℂ} {c : ℂ} {R : ℝ}
    (hU : IsPreconnected U) (hopen : IsOpen U) (hf : HarmonicOnNhd f U)
    (hnonpos : ∀ z ∈ U, f z ≤ 0) (hR : 0 < R)
    (hcircle : sphere c R ⊆ U) (hmean : Real.circleAverage f c R = 0) :
    EqOn f (fun _ ↦ 0) U := by
  have hcont : ContinuousOn f (sphere c R) := hf.continuousOn.mono hcircle
  obtain ⟨m, hm, hmax⟩ := (isCompact_sphere c R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hcont
  have hle := Real.circleAverage_mono_on_of_le_circle (hcont.circleIntegrable hR.le)
    (fun z hz ↦ hmax (by simpa only [abs_of_pos hR] using hz))
  have hfm : f m = 0 := le_antisymm (hnonpos m (hcircle hm)) (by rwa [hmean] at hle)
  have hmaxU : IsMaxOn f U m := fun z hz ↦ (hnonpos z hz).trans_eq hfm.symm
  have hconst := harmonic_eqOn_of_isPreconnected_of_isMaxOn hU hopen hf (hcircle hm) hmaxU
  simpa only [hfm] using hconst

end Erdos1040
