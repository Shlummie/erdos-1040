import Erdos1040.LogEnergy

/-!
Finite logarithmic energy makes the source-product diagonal null. Only after
that fact is proved do we identify the actual real log-distance integral and
the finite shifted extended energy. No equilibrium or Frostman fact is used.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos1040

theorem nonnegativeLogKernel_toReal_of_dist_le {D : ℝ} (hD : 0 < D)
    {z w : ℂ} (hzw : z ≠ w) (hbound : dist z w ≤ D) :
    (nonnegativeLogKernel D z w).toReal = Real.log D - Real.log (dist z w) := by
  have hd : 0 < dist z w := dist_pos.mpr hzw
  have hn : 0 ≤ Real.log (D / dist z w) :=
    Real.log_nonneg ((one_le_div hd).mpr hbound)
  rw [nonnegativeLogKernel_of_ne hD hzw, ENNReal.toReal_ofReal hn,
    Real.log_div hD.ne' hd.ne']

theorem ae_ne_of_finite_nonnegativeLogEnergy {S : Set ℂ} {D : ℝ} (hD : 0 < D)
    (μ : ProbabilityMeasure S) (hE : nonnegativeLogEnergy D μ ≠ ⊤) :
    ∀ᵐ p : S × S ∂(μ.prod μ : Measure (S × S)), (p.1 : ℂ) ≠ (p.2 : ℂ) := by
  have hm : Measurable (fun p : S × S ↦ nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) := by
    have he : Measurable (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))) := by fun_prop
    simpa only [Function.comp_def] using (continuous_nonnegativeLogKernel D).measurable.comp he
  have hf := ae_lt_top hm hE
  filter_upwards [hf] with p hp
  intro he
  rw [he, nonnegativeLogKernel_self hD] at hp
  exact (lt_irrefl _ hp)

theorem nullSingletonClass_of_finite_nonnegativeLogEnergy {S : Set ℂ} {D : ℝ}
    (hD : 0 < D) (μ : ProbabilityMeasure S) (hE : nonnegativeLogEnergy D μ ≠ ⊤) :
    NullSingletonClass (μ : Measure S) := by
  constructor
  intro x
  have hr : (μ.prod μ : Measure (S × S)) ({x} ×ˢ {x}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_ne_of_finite_nonnegativeLogEnergy hD μ hE] with p hp
    intro hx
    have hx1 : p.1 = x := by simpa using hx.1
    have hx2 : p.2 = x := by simpa using hx.2
    exact hp (by rw [hx1, hx2])
  change ((μ : Measure S).prod (μ : Measure S)) ({x} ×ˢ {x}) = 0 at hr
  rw [Measure.prod_prod] at hr
  exact (mul_self_eq_zero.mp hr)

theorem integrable_log_dist_prod_of_finite_nonnegativeLogEnergy
    {S : Set ℂ} {D : ℝ} (hD : 0 < D)
    (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (μ : ProbabilityMeasure S) (hE : nonnegativeLogEnergy D μ ≠ ⊤) :
    Integrable (fun p : S × S ↦ Real.log (dist (p.1 : ℂ) (p.2 : ℂ)))
      (μ.prod μ : Measure (S × S)) := by
  have hm : Measurable (fun p : S × S ↦ nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) := by
    have he : Measurable (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))) := by fun_prop
    simpa only [Function.comp_def] using (continuous_nonnegativeLogKernel D).measurable.comp he
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hE
  apply ((integrable_const (Real.log D)).sub hi).congr
  filter_upwards [ae_ne_of_finite_nonnegativeLogEnergy hD μ hE] with p hp
  change Real.log D - (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)).toReal =
    Real.log (dist (p.1 : ℂ) (p.2 : ℂ))
  rw [nonnegativeLogKernel_toReal_of_dist_le hD hp
    (hbound p.1 p.1.property p.2 p.2.property)]
  ring

theorem nonnegativeLogEnergy_toReal_eq_log_sub_integral
    {S : Set ℂ} {D : ℝ} (hD : 0 < D)
    (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D)
    (μ : ProbabilityMeasure S) (hE : nonnegativeLogEnergy D μ ≠ ⊤) :
    (nonnegativeLogEnergy D μ).toReal = Real.log D -
      ∫ p : S × S, Real.log (dist (p.1 : ℂ) (p.2 : ℂ)) ∂(μ.prod μ) := by
  have hm : Measurable (fun p : S × S ↦ nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) := by
    have he : Measurable (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))) := by fun_prop
    simpa only [Function.comp_def] using (continuous_nonnegativeLogKernel D).measurable.comp he
  have hi := integrable_log_dist_prod_of_finite_nonnegativeLogEnergy hD hbound μ hE
  calc
    (nonnegativeLogEnergy D μ).toReal =
        ∫ p : S × S, (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)).toReal ∂(μ.prod μ) :=
      (integral_toReal hm.aemeasurable (ae_lt_top hm hE)).symm
    _ = ∫ p : S × S, Real.log D - Real.log (dist (p.1 : ℂ) (p.2 : ℂ)) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [ae_ne_of_finite_nonnegativeLogEnergy hD μ hE] with p hp
      exact nonnegativeLogKernel_toReal_of_dist_le hD hp
        (hbound p.1 p.1.property p.2 p.2.property)
    _ = Real.log D - ∫ p : S × S, Real.log (dist (p.1 : ℂ) (p.2 : ℂ)) ∂(μ.prod μ) := by
      rw [integral_sub (integrable_const _) hi]
      simp

end Erdos1040
