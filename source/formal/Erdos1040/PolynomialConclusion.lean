import Erdos1040.Basic

/-!
Explicit passage from the checked finite-root conclusion to the original
monic-polynomial formulation. Source containment keeps every root permitted.
-/

noncomputable section

open MeasureTheory Polynomial

namespace Erdos1040

theorem HasArbitrarilySmallLemniscates.mono {S F : Set ℂ}
    (hS : HasArbitrarilySmallLemniscates S) (hSF : S ⊆ F) :
    HasArbitrarilySmallLemniscates F := by
  intro ε hε
  obtain ⟨n, hn, roots, hr, ha⟩ := hS ε hε
  exact ⟨n, hn, roots, fun i ↦ hSF (hr i), ha⟩

theorem exists_monic_polynomial_small_area {F : Set ℂ}
    (hF : HasArbitrarilySmallLemniscates F) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], p.Monic ∧ 0 < p.natDegree ∧
      (∀ z : ℂ, p.IsRoot z → z ∈ F) ∧
      volume {z : ℂ | ‖p.eval z‖ < 1} < ENNReal.ofReal ε := by
  obtain ⟨n, hn, roots, hr, ha⟩ := hF ε hε
  refine ⟨rootPolynomial roots, rootPolynomial_monic roots, ?_, ?_, ?_⟩
  · simpa only [rootPolynomial_natDegree] using hn
  · intro z hz
    obtain ⟨i, rfl⟩ := (rootPolynomial_isRoot_iff roots z).mp hz
    exact hr i
  · simpa only [rootPolynomial_eval, unitLemniscate] using ha

end Erdos1040
