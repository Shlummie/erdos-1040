import Erdos1040.LogarithmicCapacity

/-!
Countable-source singular energy and an explicit compact infinite source.
Admission is recorded separately after all documented gates pass.
-/

noncomputable section

open MeasureTheory Topology Filter
open scoped ENNReal NNReal

namespace Erdos1040

theorem nonnegativeLogEnergy_eq_top_of_countable
    {S : Set ℂ} (hS : S.Countable) {D : ℝ} (hD : 0 < D)
    (μ : ProbabilityMeasure S) :
    nonnegativeLogEnergy D μ = ⊤ := by
  let : Countable S := hS.to_subtype
  by_contra hE
  let : NullSingletonClass (μ : Measure S) :=
    nullSingletonClass_of_finite_nonnegativeLogEnergy hD μ hE
  have hzero :=
    (Set.countable_univ : (Set.univ : Set S).Countable).measure_zero
      (μ : Measure S)
  simp at hzero

theorem logarithmicCapacity_eq_zero_of_countable
    {S : Set ℂ} (hS : S.Countable) :
    logarithmicCapacity S = 0 := by
  apply (logarithmicCapacity_eq_zero_iff S).mpr
  have hD : 0 < logarithmicCapacityScale S :=
    lt_of_lt_of_le zero_lt_one (one_le_logarithmicCapacityScale S)
  simp [robinConstant, nonnegativeLogEnergy_eq_top_of_countable hS hD]

def smallCountableSource : Set ℂ :=
  insert 0 (Set.range (fun n : ℕ ↦ 1 / ((n + 4 : ℕ) : ℂ)))

theorem smallCountableSource_countable : smallCountableSource.Countable := by
  exact (Set.countable_range (fun n : ℕ ↦ 1 / ((n + 4 : ℕ) : ℂ))).insert 0

theorem smallCountableSource_isCompact : IsCompact smallCountableSource := by
  have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n + 4 : ℕ) : ℂ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 4).2
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ))
  exact hlim.isCompact_insert_range

theorem smallCountableSource_infinite : smallCountableSource.Infinite := by
  have hinj : Function.Injective (fun n : ℕ ↦ 1 / ((n + 4 : ℕ) : ℂ)) := by
    intro m n h
    have hcast := congrArg (fun z : ℂ ↦ z⁻¹) h
    simp only [one_div, inv_inv] at hcast
    exact Nat.add_right_cancel (Nat.cast_injective hcast)
  exact (Set.infinite_range_of_injective hinj).mono (Set.subset_insert _ _)

theorem smallCountableSource_subset_closedBall :
    smallCountableSource ⊆ Metric.closedBall (0 : ℂ) (1 / 4 : ℝ) := by
  rintro z (rfl | ⟨n, rfl⟩)
  · simp
  · rw [Metric.mem_closedBall, dist_zero_right, norm_div, norm_one, Complex.norm_natCast]
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast (show 4 ≤ n + 4 by omega)

theorem zero_mem_smallCountableSource : (0 : ℂ) ∈ smallCountableSource := by
  exact Set.mem_insert _ _

end Erdos1040
