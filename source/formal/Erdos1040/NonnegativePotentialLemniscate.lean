import Erdos1040.ConditionalLemniscate
import Erdos1040.ExteriorPositivity
import Erdos1040.FilledHull
import Erdos1040.PolynomialConclusion

/-!
The geometric hypotheses of the conditional lemniscate theorem are now
discharged using the actual probability support and a constructed hull.
Only global nonnegativity of the actual source potential remains as a
potential hypothesis; no boundary geometry is supplied by the caller.
-/

noncomputable section

open MeasureTheory Set

namespace Erdos1040

theorem hasArbitrarilySmallLemniscates_of_nonnegative_source_potential
    {S : Set ℂ} (hS : IsCompact S) (μ : ProbabilityMeasure S)
    (hnonneg : ∀ z : ℂ, 0 ≤ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) :
    HasArbitrarilySmallLemniscates S := by
  let T := sourceSupport μ
  let ν := sourceProbabilityOnSupport μ
  have hT : IsCompact T := isCompact_sourceSupport hS μ
  obtain ⟨K, hK, _, hTK, hconn, hfront⟩ :=
    exists_compact_hull_with_connected_complement hT (sourceSupport_nonempty μ)
  have hsame (z : ℂ) :
      (∫ w : T, Real.log ‖z - (w : ℂ)‖ ∂ν) =
      ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ :=
    integral_sourceProbabilityOnSupport hS.measurableSet μ (fun w : ℂ ↦ Real.log ‖z - w‖)
  have hboundary : frontier K ⊆ ((ν : Measure T).map ((↑) : T → ℂ)).support := by
    change frontier K ⊆ ((sourceProbabilityOnSupport μ : Measure (sourceSupport μ)).map
      ((↑) : sourceSupport μ → ℂ)).support
    rw [map_sourceProbabilityOnSupport]
    exact hfront
  have hstrict := log_source_potential_pos_on_hull_compl hS hK μ hTK hconn hnonneg
  have hsmall : HasArbitrarilySmallLemniscates T :=
    hasArbitrarilySmallLemniscates_of_potential_properties hT hK hTK
      (ν : Measure T) hconn hboundary (fun z ↦ by rw [hsame]; exact hnonneg z)
      (fun z hz ↦ by rw [hsame]; exact hstrict z hz)
  exact hsmall.mono (sourceSupport_subset hS.isClosed μ)

end Erdos1040
