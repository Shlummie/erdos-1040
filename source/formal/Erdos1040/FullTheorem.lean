import Erdos1040.CompactLemniscate
import Erdos1040.Unbounded
import Erdos1040.PolynomialConclusion
import Erdos1040.GeometricDiameterLimit

/-!
The full closed-infinite-set implication in its explicit monic-polynomial
form. The geometric infimum is independently proved to be the classical
decreasing finite-diameter limit in GeometricDiameterLimit.
-/

noncomputable section

open MeasureTheory Polynomial

namespace Erdos1040

theorem erdos1040 {F : Set ℂ} (hF : IsClosed F) (_hInfinite : F.Infinite)
    (hτ : 1 ≤ transfiniteDiameter F) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], p.Monic ∧ 0 < p.natDegree ∧
      (∀ z : ℂ, p.IsRoot z → z ∈ F) ∧
      volume {z : ℂ | ‖p.eval z‖ < 1} < ENNReal.ofReal ε := by
  have hsmall : HasArbitrarilySmallLemniscates F := by
    by_cases hb : Bornology.IsBounded F
    · exact hasArbitrarilySmallLemniscates_of_one_le_transfiniteDiameter
        (Metric.isCompact_of_isClosed_isBounded hF hb) hτ
    · exact unbounded_hasArbitrarilySmallLemniscates hb
  exact exists_monic_polynomial_small_area hsmall hε

end Erdos1040
