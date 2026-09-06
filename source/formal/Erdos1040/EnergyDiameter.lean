import Erdos1040.EmpiricalEnergy
import Erdos1040.GeometricDiameter

/-!
The exact geometric transfinite-diameter hypothesis supplies a finite bound
for the actual singular logarithmic energy. Atomic full energy is never used;
its bounded truncations retain the controlled diagonal contribution n/N.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Erdos1040

theorem exists_probability_energy_le_log_of_one_le_transfiniteDiameter
    {S : Set ℂ} (hS : IsCompact S) (hτ : 1 ≤ transfiniteDiameter S)
    {D : ℝ} (hD : 1 ≤ D) (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D) :
    ∃ μ : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ ENNReal.ofReal (Real.log D) := by
  apply exists_probability_energy_le_of_approx_truncated_bounds hS D
  intro n ε hε
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨k, hk⟩ := exists_nat_gt ((n : ℝ) / (ε : ℝ))
  let N := k + 2
  have hN : 2 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hratio : (n : ℝ) / N ≤ (ε : ℝ) := by
    apply (div_le_iff₀ hNR).mpr
    have hk' := (div_lt_iff₀ hεR).mp hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
    nlinarith
  obtain ⟨roots, hinj, hlog⟩ := exists_distinct_configuration_log_sum_nonneg hS hτ hN
  refine ⟨empiricalSourceProbability roots hN0, ?_⟩
  calc
    _ ≤ ENNReal.ofReal (Real.log D + (n : ℝ) / N) :=
      truncatedLogEnergy_empirical_le_of_log_sum_nonneg roots hN0 hinj hD hbound n hlog
    _ ≤ ENNReal.ofReal (Real.log D + (ε : ℝ)) :=
      ENNReal.ofReal_le_ofReal (add_le_add (le_refl _) hratio)
    _ = ENNReal.ofReal (Real.log D) + ε := by
      rw [ENNReal.ofReal_add (Real.log_nonneg hD) ε.coe_nonneg]
      simp

theorem exists_finite_minimizer_of_one_le_transfiniteDiameter
    {S : Set ℂ} (hS : IsCompact S) (hτ : 1 ≤ transfiniteDiameter S)
    {D : ℝ} (hD : 1 ≤ D) (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D) :
    ∃ μ : ProbabilityMeasure S,
      (∀ ν : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ν) ∧
      nonnegativeLogEnergy D μ ≠ ⊤ ∧
      (nonnegativeLogEnergy D μ).toReal ≤ Real.log D := by
  obtain ⟨ν, hν⟩ := exists_probability_energy_le_log_of_one_le_transfiniteDiameter hS hτ hD hbound
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, transfiniteDiameter_empty] at hτ
    exact (not_le_of_gt zero_lt_one) hτ
  obtain ⟨μ, hμ⟩ := exists_minimizer_nonnegativeLogEnergy hS hSne D
    (lt_of_lt_of_le zero_lt_one hD) hbound
  have hb := (hμ ν).trans hν
  have hf : nonnegativeLogEnergy D μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  refine ⟨μ, hμ, hf, ?_⟩
  simpa only [ENNReal.toReal_ofReal (Real.log_nonneg hD)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end Erdos1040
