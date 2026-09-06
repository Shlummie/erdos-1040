import Erdos1040.CapacityDependence
import Erdos1040.FullTheorem
import Erdos1040.CapacityTheorem

/-!
The already admitted positive-tolerance threshold conclusions expressed using
the exact area-infimum functional from original Problem 4. No existing
threshold proof or assumption is changed.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal

namespace Erdos1040

theorem minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials {F : Set ℂ}
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : ℂ[X], p.Monic ∧ 0 < p.natDegree ∧
      (∀ z : ℂ, p.IsRoot z → z ∈ F) ∧
      volume {z : ℂ | ‖p.eval z‖ < 1} < ENNReal.ofReal ε) :
    minimalLemniscateArea F = 0 := by
  by_contra hzero
  obtain ⟨ε, _, hε, hbound⟩ := ENNReal.lt_iff_exists_real_btwn.mp
    (pos_iff_ne_zero.mpr hzero)
  obtain ⟨p, hp, hn, hr, harea⟩ := hsmall ε (ENNReal.ofReal_pos.mp hε)
  exact not_lt_of_ge (minimalLemniscateArea_le_of_monic p hp hn hr)
    (harea.trans hbound)

theorem minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter
    {F : Set ℂ} (hF : IsClosed F) (hInfinite : F.Infinite)
    (hτ : 1 ≤ transfiniteDiameter F) : minimalLemniscateArea F = 0 :=
  minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials
    (fun _ hε ↦ erdos1040 hF hInfinite hτ hε)

theorem minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity
    {F : Set ℂ} (hF : IsCompact F) (hcap : 1 ≤ logarithmicCapacity F) :
    minimalLemniscateArea F = 0 :=
  minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials
    (fun _ hε ↦ exists_monic_polynomial_small_area
      (hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity hF hcap) hε)

end Erdos1040
