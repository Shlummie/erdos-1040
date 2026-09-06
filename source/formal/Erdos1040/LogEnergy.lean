import Mathlib

/-!
The extended logarithmic energy retains positive infinity on the diagonal.
Its nonnegative shifted form agrees with classical logarithmic energy plus
log D on a source whose pair distances are bounded by positive D. It is not
the raw logarithmic potential on arbitrary exterior observation points.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace Erdos1040

/-- The nonnegative extended logarithmic kernel at scale D. -/
def nonnegativeLogKernel (D : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  (ENNReal.log (ENNReal.ofReal D / edist z w)).toENNReal

theorem nonnegativeLogKernel_self {D : ℝ} (hD : 0 < D) (z : ℂ) :
    nonnegativeLogKernel D z z = ⊤ := by
  simp [nonnegativeLogKernel, ENNReal.div_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hD))]

theorem nonnegativeLogKernel_of_ne {D : ℝ} (hD : 0 < D)
    {z w : ℂ} (hzw : z ≠ w) :
    nonnegativeLogKernel D z w = ENNReal.ofReal (Real.log (D / dist z w)) := by
  have hd : 0 < dist z w := dist_pos.mpr hzw
  rw [nonnegativeLogKernel, edist_dist, ← ENNReal.ofReal_div_of_pos hd,
    ENNReal.log_ofReal_of_pos (div_pos hD hd), EReal.real_coe_toENNReal]

theorem continuous_nonnegativeLogKernel (D : ℝ) :
    Continuous (fun p : ℂ × ℂ ↦ nonnegativeLogKernel D p.1 p.2) := by
  unfold nonnegativeLogKernel
  apply EReal.continuous_toENNReal.comp
  apply ENNReal.continuous_log.comp
  simp only [div_eq_mul_inv]
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
    continuous_edist.fun_inv

/-- Weak lower semicontinuity of the actual integral of a continuous
extended nonnegative function, proved using finite continuous truncations. -/
theorem lowerSemicontinuous_lintegral_continuous_ennreal
    {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [OpensMeasurableSpace K] [CompactSpace K] (k : C(K, ℝ≥0∞)) :
    LowerSemicontinuous (fun μ : ProbabilityMeasure K ↦ ∫⁻ x, k x ∂μ) := by
  have hfinite (n : ℕ) (x : K) : min (k x) (n : ℝ≥0∞) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  let t (n : ℕ) : C(K, ℝ≥0) :=
    ⟨fun x ↦ (min (k x) (n : ℝ≥0∞)).toNNReal,
      ENNReal.continuousOn_toNNReal.comp_continuous
        (k.continuous.min continuous_const) (hfinite n)⟩
  have hcoe (n : ℕ) (x : K) : (t n x : ℝ≥0∞) = min (k x) (n : ℝ≥0∞) :=
    ENNReal.coe_toNNReal (hfinite n x)
  have hsup (x : K) : (⨆ n : ℕ, (t n x : ℝ≥0∞)) = k x := by
    simp_rw [hcoe]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hmono : Monotone (fun n : ℕ ↦ fun x : K ↦ (t n x : ℝ≥0∞)) := by
    intro n m hnm x
    change (t n x : ℝ≥0∞) ≤ (t m x : ℝ≥0∞)
    rw [hcoe, hcoe]
    exact min_le_min_left _ (Nat.cast_le.mpr hnm)
  have heq (μ : ProbabilityMeasure K) :
      (∫⁻ x, k x ∂μ) = ⨆ n : ℕ, ∫⁻ x, (t n x : ℝ≥0∞) ∂μ := by
    calc
      (∫⁻ x, k x ∂μ) = ∫⁻ x, ⨆ n : ℕ, (t n x : ℝ≥0∞) ∂μ :=
        lintegral_congr (fun x ↦ (hsup x).symm)
      _ = ⨆ n : ℕ, ∫⁻ x, (t n x : ℝ≥0∞) ∂μ :=
        lintegral_iSup (f := fun n x ↦ (t n x : ℝ≥0∞))
          (fun n ↦ by fun_prop) hmono
  simp_rw [heq]
  exact lowerSemicontinuous_iSup fun n ↦
    (ProbabilityMeasure.continuous_lintegral_continuousMap (t n)).lowerSemicontinuous

/-- The actual extended nonnegative double energy of a source probability. -/
def nonnegativeLogEnergy {S : Set ℂ} (D : ℝ) (μ : ProbabilityMeasure S) : ℝ≥0∞ :=
  ∫⁻ p : S × S, nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ) ∂(μ.prod μ)

theorem lowerSemicontinuous_nonnegativeLogEnergy {S : Set ℂ}
    (hS : IsCompact S) (D : ℝ) :
    LowerSemicontinuous (nonnegativeLogEnergy (S := S) D) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))) := by fun_prop
  let k : C(S × S, ℝ≥0∞) :=
    ⟨fun p ↦ nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ),
      by simpa only [Function.comp_def] using (continuous_nonnegativeLogKernel D).comp hc⟩
  have hprod : Continuous (fun μ : ProbabilityMeasure S ↦ μ.prod μ) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  exact (lowerSemicontinuous_lintegral_continuous_ennreal k).comp
    hprod

/-- A logarithmic-energy minimizer exists on each nonempty compact source.
The minimum is allowed to be infinite. No Frostman conclusion is assumed. -/
theorem exists_minimizer_nonnegativeLogEnergy {S : Set ℂ} (hS : IsCompact S)
    (hne : S.Nonempty) (D : ℝ) (_hD : 0 < D)
    (_hdiam : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D) :
    ∃ μ : ProbabilityMeasure S, ∀ ν : ProbabilityMeasure S,
      nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : Inhabited S := Classical.inhabited_of_nonempty hne.to_subtype
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := (Set.univ : Set (ProbabilityMeasure S))) Set.univ_nonempty isCompact_univ
    ((lowerSemicontinuous_nonnegativeLogEnergy hS D).lowerSemicontinuousOn Set.univ)
  exact ⟨μ, fun ν ↦ hμ (Set.mem_univ ν)⟩

end Erdos1040
