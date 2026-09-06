import Erdos1040.LogEnergy

/-!
Bounded truncations of the actual singular logarithmic energy. Compactness
passes separately bounded truncations to one probability with bounded full
energy; no empirical atomic probability is assigned finite full energy.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1040

def truncatedLogEnergy {S : Set ℂ} (D : ℝ) (n : ℕ)
    (μ : ProbabilityMeasure S) : ℝ≥0∞ :=
  ∫⁻ p : S × S, min (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) n ∂(μ.prod μ)

theorem lowerSemicontinuous_truncatedLogEnergy {S : Set ℂ}
    (hS : IsCompact S) (D : ℝ) (n : ℕ) :
    LowerSemicontinuous (truncatedLogEnergy (S := S) D n) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let k : C(S × S, ℝ≥0∞) :=
    ⟨fun p ↦ min (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) n,
      ((continuous_nonnegativeLogKernel D).comp
        (by fun_prop : Continuous (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))))).min
          continuous_const⟩
  exact (lowerSemicontinuous_lintegral_continuous_ennreal k).comp
    (ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id))

theorem nonnegativeLogEnergy_eq_iSup_truncated {S : Set ℂ} (D : ℝ)
    (μ : ProbabilityMeasure S) :
    nonnegativeLogEnergy D μ = ⨆ n : ℕ, truncatedLogEnergy D n μ := by
  have hm (n : ℕ) : Measurable (fun p : S × S ↦
      min (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) (n : ℝ≥0∞)) := by
    exact (((continuous_nonnegativeLogKernel D).comp
      (by fun_prop : Continuous (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))))).min
        continuous_const).measurable
  have hmono : Monotone (fun n : ℕ ↦ fun p : S × S ↦
      min (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) (n : ℝ≥0∞)) := by
    intro n m hnm p
    exact min_le_min_left _ (Nat.cast_le.mpr hnm)
  unfold nonnegativeLogEnergy truncatedLogEnergy
  rw [← lintegral_iSup hm hmono]
  apply lintegral_congr
  intro p
  rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

theorem exists_probability_energy_le_of_truncated_bounds {S : Set ℂ}
    (hS : IsCompact S) (D : ℝ) (B : ℝ≥0∞)
    (hb : ∀ n : ℕ, ∃ μ : ProbabilityMeasure S, truncatedLogEnergy D n μ ≤ B) :
    ∃ μ : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ B := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let t : ℕ → Set (ProbabilityMeasure S) := fun n ↦ {μ | truncatedLogEnergy D n μ ≤ B}
  have hclosed (n : ℕ) : IsClosed (t n) :=
    (lowerSemicontinuous_truncatedLogEnergy hS D n).isClosed_preimage B
  have hdecreasing (n : ℕ) : t (n + 1) ⊆ t n := by
    intro μ hμ
    apply le_trans (b := truncatedLogEnergy D (n + 1) μ) _ hμ
    apply lintegral_mono
    intro p
    exact min_le_min_left _ (Nat.cast_le.mpr (Nat.le_succ n))
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    t hdecreasing hb (hclosed 0).isCompact hclosed
  refine ⟨μ, ?_⟩
  rw [nonnegativeLogEnergy_eq_iSup_truncated]
  exact iSup_le (fun n ↦ mem_iInter.mp hμ n)

theorem exists_probability_energy_le_of_approx_truncated_bounds {S : Set ℂ}
    (hS : IsCompact S) (D : ℝ) (B : ℝ≥0∞)
    (hb : ∀ n : ℕ, ∀ ε : ℝ≥0, 0 < ε →
      ∃ μ : ProbabilityMeasure S, truncatedLogEnergy D n μ ≤ B + ε) :
    ∃ μ : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ B := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  apply exists_probability_energy_le_of_truncated_bounds hS D B
  intro n
  obtain ⟨μ0, _⟩ := hb n 1 (by norm_num)
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := (Set.univ : Set (ProbabilityMeasure S))) ⟨μ0, mem_univ μ0⟩ isCompact_univ
    ((lowerSemicontinuous_truncatedLogEnergy hS D n).lowerSemicontinuousOn Set.univ)
  refine ⟨μ, ENNReal.le_of_forall_pos_le_add (fun ε hε _ ↦ ?_)⟩
  obtain ⟨ν, hν⟩ := hb n ε hε
  exact (hμ (mem_univ ν)).trans hν

end Erdos1040
