import Erdos1040.CompactLemniscate
import Erdos1040.LogarithmicCapacity

/-!
The literal logarithmic-capacity endpoint for arbitrary compact planar
sources, including the capacity-one case. Capacity uses the actual Robin
energy infimum with its singular diagonal and scale independence.
-/

noncomputable section

open MeasureTheory Polynomial

namespace Erdos1040

theorem hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity
    {S : Set ℂ} (hS : IsCompact S) (hcap : 1 ≤ logarithmicCapacity S) :
    HasArbitrarilySmallLemniscates S := by
  let D := logarithmicCapacityScale S
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (one_le_logarithmicCapacityScale S)
  have hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D :=
    fun _ hz _ hw ↦ dist_le_logarithmicCapacityScale hS hz hw
  obtain ⟨μ, hmin, hμ, henergy⟩ :=
    exists_finite_minimizer_of_one_le_logarithmicCapacity hS hcap hD hbound
  exact hasArbitrarilySmallLemniscates_of_finite_minimizer hS hD hbound μ hμ hmin henergy

theorem erdos1040_capacity_one {S : Set ℂ} (hS : IsCompact S)
    (hcap : logarithmicCapacity S = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], p.Monic ∧ 0 < p.natDegree ∧
      (∀ z : ℂ, p.IsRoot z → z ∈ S) ∧
      volume {z : ℂ | ‖p.eval z‖ < 1} < ENNReal.ofReal ε := by
  exact exists_monic_polynomial_small_area
    (hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity hS hcap.ge) hε

theorem hasArbitrarilySmallLemniscates_of_one_lt_logarithmicCapacity
    {S : Set ℂ} (hS : IsCompact S) (hcap : 1 < logarithmicCapacity S) :
    HasArbitrarilySmallLemniscates S :=
  hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity hS hcap.le

end Erdos1040
