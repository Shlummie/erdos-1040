import Erdos1040.LogEnergyScale

/-!
The classical energy definition of logarithmic capacity for compact planar
sets. The Robin constant is the infimum of actual normalized extended
logarithmic energies, and capacity is its negative exponential. The diagonal
infinity and the capacity-zero convention are retained.

These Set-valued definitions are interpreted as classical capacity only on
compact or bounded sets. No unbounded-set convention is inferred from the
totalized real diameter. The main compact statements prove the canonical
diameter bound and independence of every other positive diameter bound.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos1040

def logarithmicCapacityScale (S : Set ℂ) : ℝ :=
  max 1 (Metric.diam S)

theorem one_le_logarithmicCapacityScale (S : Set ℂ) :
    1 ≤ logarithmicCapacityScale S :=
  le_max_left _ _

theorem dist_le_logarithmicCapacityScale {S : Set ℂ} (hS : IsCompact S)
    {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    dist z w ≤ logarithmicCapacityScale S :=
  (Metric.dist_le_diam_of_mem hS.isBounded hz hw).trans (le_max_right _ _)

def robinConstant (S : Set ℂ) : EReal :=
  ⨅ μ : ProbabilityMeasure S,
    (nonnegativeLogEnergy (logarithmicCapacityScale S) μ : EReal) -
      (Real.log (logarithmicCapacityScale S) : EReal)

def logarithmicCapacity (S : Set ℂ) : ℝ≥0∞ :=
  EReal.exp (-robinConstant S)

theorem robinConstant_eq_iInf_energy_sub_log {S : Set ℂ} (hS : IsCompact S)
    {D : ℝ} (hD : 0 < D) (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D) :
    robinConstant S = ⨅ μ : ProbabilityMeasure S,
      (nonnegativeLogEnergy D μ : EReal) - (Real.log D : EReal) := by
  unfold robinConstant
  apply iInf_congr
  intro μ
  exact nonnegativeLogEnergy_normalized_scale_independent
    (lt_of_lt_of_le zero_lt_one (one_le_logarithmicCapacityScale S)) hD
    (fun _ hz _ hw ↦ dist_le_logarithmicCapacityScale hS hz hw) hbound μ

theorem robinConstant_empty : robinConstant ∅ = ⊤ := by
  have : IsEmpty (ProbabilityMeasure (∅ : Set ℂ)) := ⟨fun μ ↦ by
    obtain ⟨x⟩ := μ.nonempty
    exact x.property⟩
  simp [robinConstant]

theorem logarithmicCapacity_empty : logarithmicCapacity ∅ = 0 := by
  simp [logarithmicCapacity, robinConstant_empty]

theorem logarithmicCapacity_eq_zero_iff (S : Set ℂ) :
    logarithmicCapacity S = 0 ↔ robinConstant S = ⊤ := by
  simp [logarithmicCapacity]

theorem one_le_logarithmicCapacity_iff (S : Set ℂ) :
    1 ≤ logarithmicCapacity S ↔ robinConstant S ≤ 0 := by
  simp [logarithmicCapacity, EReal.one_le_exp_iff, EReal.neg_nonneg]

theorem robinConstant_eq_energy_sub_log_of_minimizer {S : Set ℂ} (hS : IsCompact S)
    {D : ℝ} (hD : 0 < D) (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (μ : ProbabilityMeasure S)
    (hmin : ∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν) :
    robinConstant S = (nonnegativeLogEnergy D μ : EReal) - (Real.log D : EReal) := by
  rw [robinConstant_eq_iInf_energy_sub_log hS hD hbound]
  apply le_antisymm (iInf_le _ μ)
  apply le_iInf
  intro ν
  exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmin ν)) le_rfl

theorem exists_finite_minimizer_of_one_le_logarithmicCapacity {S : Set ℂ}
    (hS : IsCompact S) (hcap : 1 ≤ logarithmicCapacity S)
    {D : ℝ} (hD : 0 < D) (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D) :
    ∃ μ : ProbabilityMeasure S,
      (∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν) ∧
      nonnegativeLogEnergy D μ ≠ ⊤ ∧
      (nonnegativeLogEnergy D μ).toReal ≤ Real.log D := by
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, logarithmicCapacity_empty] at hcap
    exact (not_le_of_gt zero_lt_one) hcap
  obtain ⟨μ, hmin⟩ := exists_minimizer_nonnegativeLogEnergy hS hSne D hD hbound
  have hV := (one_le_logarithmicCapacity_iff S).mp hcap
  rw [robinConstant_eq_energy_sub_log_of_minimizer hS hD hbound μ hmin] at hV
  have hE : (nonnegativeLogEnergy D μ : EReal) ≤ (Real.log D : EReal) :=
    EReal.sub_nonpos.mp hV
  have hf : nonnegativeLogEnergy D μ ≠ ⊤ := by
    intro htop
    rw [htop, EReal.coe_ennreal_top] at hE
    exact (not_le_of_gt (EReal.coe_lt_top (Real.log D))) hE
  refine ⟨μ, hmin, hf, ?_⟩
  rw [← EReal.coe_ennreal_toReal hf] at hE
  exact EReal.coe_le_coe_iff.mp hE

end Erdos1040
