import Erdos1040.LogEnergyIntegrability

/-!
Changing the positive diameter bound adds exactly the logarithm of the
scale ratio to extended logarithmic energy. Infinity is retained, and the
normalized EReal energy and minimizing measures are independent of scale.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos1040

theorem nonnegativeLogKernel_scale_change {D E : ℝ}
    (hD : 0 < D) (hDE : D ≤ E) {z w : ℂ} (hbound : dist z w ≤ D) :
    nonnegativeLogKernel E z w = nonnegativeLogKernel D z w +
      ENNReal.ofReal (Real.log (E / D)) := by
  have hE : 0 < E := lt_of_lt_of_le hD hDE
  by_cases hzw : z = w
  · subst w
    rw [nonnegativeLogKernel_self hE, nonnegativeLogKernel_self hD, top_add]
  · have hd : 0 < dist z w := dist_pos.mpr hzw
    have hlogD : 0 ≤ Real.log (D / dist z w) :=
      Real.log_nonneg ((one_le_div hd).mpr hbound)
    have hlogED : 0 ≤ Real.log (E / D) :=
      Real.log_nonneg ((one_le_div hD).mpr hDE)
    rw [nonnegativeLogKernel_of_ne hE hzw, nonnegativeLogKernel_of_ne hD hzw,
      ← ENNReal.ofReal_add hlogD hlogED]
    congr 1
    rw [Real.log_div hE.ne' hd.ne', Real.log_div hD.ne' hd.ne',
      Real.log_div hE.ne' hD.ne']
    ring

theorem nonnegativeLogEnergy_scale_change {S : Set ℂ} {D E : ℝ}
    (hD : 0 < D) (hDE : D ≤ E)
    (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (μ : ProbabilityMeasure S) :
    nonnegativeLogEnergy E μ = nonnegativeLogEnergy D μ +
      ENNReal.ofReal (Real.log (E / D)) := by
  unfold nonnegativeLogEnergy
  simp_rw [nonnegativeLogKernel_scale_change hD hDE
    (hbound _ (Subtype.property _) _ (Subtype.property _))]
  rw [lintegral_add_right _ measurable_const]
  simp

theorem finite_nonnegativeLogEnergy_scale_iff {S : Set ℂ} {D E : ℝ}
    (hD : 0 < D) (hE : 0 < E)
    (hboundD : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (hboundE : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ E)
    (μ : ProbabilityMeasure S) :
    nonnegativeLogEnergy D μ ≠ ⊤ ↔ nonnegativeLogEnergy E μ ≠ ⊤ := by
  rcases le_total D E with hDE | hED
  · rw [nonnegativeLogEnergy_scale_change hD hDE hboundD μ]
    simp
  · rw [nonnegativeLogEnergy_scale_change hE hED hboundE μ]
    simp

theorem nonnegativeLogEnergy_normalized_scale_independent {S : Set ℂ} {D E : ℝ}
    (hD : 0 < D) (hE : 0 < E)
    (hboundD : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (hboundE : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ E)
    (μ : ProbabilityMeasure S) :
    (nonnegativeLogEnergy D μ : EReal) - (Real.log D : EReal) =
      (nonnegativeLogEnergy E μ : EReal) - (Real.log E : EReal) := by
  by_cases hfD : nonnegativeLogEnergy D μ = ⊤
  · have hfE : nonnegativeLogEnergy E μ = ⊤ := by
      by_contra h
      exact (finite_nonnegativeLogEnergy_scale_iff hD hE hboundD hboundE μ).mpr h hfD
    rw [hfD, hfE, EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.top_sub_coe]
  · have hfE := (finite_nonnegativeLogEnergy_scale_iff hD hE hboundD hboundE μ).mp hfD
    rw [← EReal.coe_ennreal_toReal hfD, ← EReal.coe_ennreal_toReal hfE,
      ← EReal.coe_sub, ← EReal.coe_sub,
      nonnegativeLogEnergy_toReal_eq_log_sub_integral hD hboundD μ hfD,
      nonnegativeLogEnergy_toReal_eq_log_sub_integral hE hboundE μ hfE]
    congr 1
    ring

theorem minimizer_nonnegativeLogEnergy_scale_iff {S : Set ℂ} {D E : ℝ}
    (hD : 0 < D) (hE : 0 < E)
    (hboundD : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (hboundE : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ E)
    (μ : ProbabilityMeasure S) :
    (∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν) ↔
      (∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy E μ ≤ nonnegativeLogEnergy E ν) := by
  rcases le_total D E with hDE | hED
  · simp_rw [nonnegativeLogEnergy_scale_change hD hDE hboundD]
    simp only [ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top]
  · simp_rw [nonnegativeLogEnergy_scale_change hE hED hboundE]
    simp only [ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top]

end Erdos1040
