import Mathlib

/-!
Equal-weight atomic approximation for Banach-valued kernels.

The compact-source theorem supplies actual sample points in the original
compact subtype. Repeated points are allowed and the sample size is positive.
This is the kernel-wise norm approximation needed in the candidate; it does
not assert simultaneous weak convergence of all continuous test integrals.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace Erdos1040
variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- A probability integral is a norm limit of equal-weight prefix averages of actual sources. -/
theorem exists_sample_sequence_tendsto_integral (μ : Measure α) [IsProbabilityMeasure μ]
    (k : α → E) (hk : Measurable k) (hki : Integrable k μ) :
    ∃ points : ℕ → α,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, k (points i))
        atTop (𝓝 (∫ x, k x ∂μ)) := by
  let P : Measure (ℕ → α) := Measure.infinitePi (fun _ : ℕ => μ)
  let X : ℕ → (ℕ → α) → E := fun n ω => k (ω n)
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hd (n : ℕ) : IdentDistrib (X n) k P μ := by
    refine ⟨(hk.comp (measurable_pi_apply n)).aemeasurable, hk.aemeasurable, ?_⟩
    change P.map (k ∘ Function.eval n) = μ.map k
    rw [← Measure.map_map hk (measurable_pi_apply n)]
    congr 1
    exact Measure.infinitePi_map_eval (fun _ : ℕ => μ) n
  have hi : iIndepFun X P :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ : ℕ => k) (fun _ => hk)
  have hs := strong_law_ae X ((hd 0).integrable_iff.2 hki)
    (fun i j hij => hi.indepFun hij) (fun i => (hd i).trans (hd 0).symm)
  obtain ⟨points, hpoints⟩ := hs.exists
  refine ⟨points, ?_⟩
  simpa only [X, (hd 0).integral_eq] using hpoints

/-- Every positive tolerance admits a nonempty equal-weight average of actual sources. -/
theorem exists_equal_weight_average (μ : Measure α) [IsProbabilityMeasure μ]
    (k : α → E) (hk : Measurable k) (hki : Integrable k μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ points : Fin n → α,
      ‖(n : ℝ)⁻¹ • ∑ i, k (points i) - ∫ x, k x ∂μ‖ < ε := by
  obtain ⟨points, hp⟩ := exists_sample_sequence_tendsto_integral μ k hk hki
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hp ε hε
  refine ⟨max N 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _),
    fun i => points i, ?_⟩
  simpa only [dist_eq_norm,
    ← Fin.sum_univ_eq_sum_range (fun i => k (points i)) (max N 1)] using
    hN (max N 1) (le_max_left _ _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A continuous kernel on a compact complex source set admits equal-weight atomic approximation. -/
theorem exists_equal_weight_average_on_compact {S : Set ℂ} (hS : IsCompact S)
    (μ : Measure S) [IsProbabilityMeasure μ] (k : S → E) (hk : Continuous k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ points : Fin n → S,
      ‖(n : ℝ)⁻¹ • ∑ i, k (points i) - ∫ x, k x ∂μ‖ < ε := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  borelize E
  have hki : Integrable k μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hk.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  exact exists_equal_weight_average μ k hk.measurable hki ε hε
end Erdos1040
