import Erdos1040.DiscretePotential
import Erdos1040.ExteriorKernel

/-! Actual finite-root potentials meet both norms with one source list. -/

open MeasureTheory Set

namespace Erdos1040

theorem exists_roots_simultaneous_potential_approximation
    {S K E : Set ℂ} [CompactSpace E]
    (hS : IsCompact S) (hK : IsCompact K) (hSE : Disjoint S E)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (εA εE : ℝ) (hεA : 0 < εA) (hεE : 0 < εE) :
    ∃ n : ℕ, 0 < n ∧ ∃ roots : Fin n → ℂ, (∀ i, roots i ∈ S) ∧
      ‖(memLp_atomicLogPotential_of_isCompact roots hK).toLp (atomicLogPotential roots) -
        ∫ w : S, areaLogKernel hK w ∂μ‖ < εA ∧
      ∀ z : E, |atomicLogPotential roots z -
        ∫ w : S, Real.log ‖(z : ℂ) - (w : ℂ)‖ ∂μ| < εE := by
  obtain ⟨n, hn, points, hA, hE⟩ :=
    exists_roots_approx_area_and_exterior_potentials hS hK hSE μ εA εE hεA hεE
  refine ⟨n, hn, fun i ↦ (points i : ℂ), fun i ↦ (points i).property, ?_, hE⟩
  rwa [atomicLogPotential_toLp_eq_average_areaLogKernel]

end Erdos1040
