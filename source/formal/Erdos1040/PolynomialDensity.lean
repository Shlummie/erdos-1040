import Erdos1040.DensityOperator
import Erdos1040.AdjointUniqueness

/-!
The conditional density conclusion for real parts of source-mean-zero
polynomials. The classical compact-source, boundary-support, and globally
nonnegative source-potential hypotheses remain explicit inputs.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Erdos1040

theorem memLp_re_polynomial {K : Set ℂ} (hK : IsCompact K)
    (p : Polynomial ℂ) : MemLp (fun z : ℂ ↦ (p.eval z).re) 2 (volume.restrict K) := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hc : Continuous (fun z : ℂ ↦ (p.eval z).re) := Complex.continuous_re.comp p.continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact hC z hz

theorem inner_re_polynomial_toLp {K : Set ℂ} (hK : IsCompact K)
    (p : Polynomial ℂ) (h : Lp ℝ 2 (volume.restrict K)) :
    ⟪h, (memLp_re_polynomial hK p).toLp (fun z : ℂ ↦ (p.eval z).re)⟫_ℝ =
      ∫ z in K, h z * (p.eval z).re := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_re_polynomial hK p).coeFn_toLp] with z hz
  simp [RCLike.inner_apply, hz, mul_comm]

theorem exists_density_approx_re_polynomial {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (hSK : S ⊆ K)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (hconn : IsPreconnected Kᶜ)
    (hboundary : frontier K ⊆ (μ.map ((↑) : S → ℂ)).support)
    (hpotential : ∀ z : ℂ, 0 ≤ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)
    (p : Polynomial ℂ) (hp : (∫ w : S, (p.eval (w : ℂ)).re ∂μ) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : S → ℝ, Measurable f ∧ (∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) ∧
      ‖(∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ) -
        (memLp_re_polynomial hK p).toLp (fun z : ℂ ↦ (p.eval z).re)‖ < ε := by
  apply exists_density_approx_of_annihilator hS hK μ _ _ ε hε
  intro h horth
  rw [inner_re_polynomial_toLp hK p h,
    integral_area_mul_re_polynomial_eq_mass_mul_source_integral_of_annihilator
      hS hK hSK μ hconn hboundary hpotential h horth p, hp, mul_zero]

end Erdos1040
