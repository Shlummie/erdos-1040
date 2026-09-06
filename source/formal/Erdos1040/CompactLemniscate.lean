import Erdos1040.GlobalFrostman
import Erdos1040.NonnegativePotentialLemniscate
import Erdos1040.EnergyDiameter

/-!
Compact-source assembly from actual singular-energy minimization and from
the exact geometric transfinite-diameter hypothesis. The only intermediate
potential hypothesis is discharged by the proved global Frostman bound.
-/

noncomputable section

open MeasureTheory

namespace Erdos1040

theorem hasArbitrarilySmallLemniscates_of_finite_minimizer
    {S : Set ℂ} (hS : IsCompact S) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (μ : ProbabilityMeasure S) (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    (hmin : ∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν)
    (henergy : (nonnegativeLogEnergy D μ).toReal ≤ Real.log D) :
    HasArbitrarilySmallLemniscates S := by
  apply hasArbitrarilySmallLemniscates_of_nonnegative_source_potential hS μ
  intro z
  have h := log_source_potential_ge_of_finite_minimizer hS hD hbound μ hμ hmin z
  linarith

theorem hasArbitrarilySmallLemniscates_of_one_le_transfiniteDiameter
    {S : Set ℂ} (hS : IsCompact S) (hτ : 1 ≤ transfiniteDiameter S) :
    HasArbitrarilySmallLemniscates S := by
  let D := max 1 (Metric.diam S)
  have hD : 1 ≤ D := le_max_left _ _
  have hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D := by
    intro z hz w hw
    exact (Metric.dist_le_diam_of_mem hS.isBounded hz hw).trans (le_max_right _ _)
  obtain ⟨μ, hmin, hμ, henergy⟩ :=
    exists_finite_minimizer_of_one_le_transfiniteDiameter hS hτ hD hbound
  exact hasArbitrarilySmallLemniscates_of_finite_minimizer hS
    (lt_of_lt_of_le zero_lt_one hD) hbound μ hμ hmin henergy

end Erdos1040
