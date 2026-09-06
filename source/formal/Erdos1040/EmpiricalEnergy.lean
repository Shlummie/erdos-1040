import Erdos1040.TruncatedEnergy
import Erdos1040.LogEnergyIntegrability

/-!
Actual equally weighted source probabilities and their truncated double
energies. The singular full energy is never replaced by an off-diagonal sum.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Erdos1040

def empiricalSourceProbability {S : Set ℂ} {N : ℕ} (roots : Fin N → S)
    (hN : 0 < N) : ProbabilityMeasure S :=
  ⟨(N : ℝ≥0∞)⁻¹ • Measure.sum (fun i ↦ Measure.dirac (roots i)), ⟨by
    simpa [Measure.smul_apply] using ENNReal.inv_mul_cancel
      (Nat.cast_ne_zero.mpr hN.ne' : (N : ℝ≥0∞) ≠ 0) (by simp)⟩⟩

theorem lintegral_empiricalSourceProbability {S : Set ℂ} {N : ℕ}
    (roots : Fin N → S) (hN : 0 < N) (f : S → ℝ≥0∞) :
    (∫⁻ w, f w ∂(empiricalSourceProbability roots hN)) =
      (N : ℝ≥0∞)⁻¹ * ∑ i, f (roots i) := by
  change (∫⁻ w, f w ∂((N : ℝ≥0∞)⁻¹ • Measure.sum
    (fun i ↦ Measure.dirac (roots i)))) = _
  rw [lintegral_smul_measure, lintegral_sum_measure]
  simp [tsum_fintype]

theorem truncatedLogEnergy_empirical {S : Set ℂ} {N : ℕ}
    (roots : Fin N → S) (hN : 0 < N) (D : ℝ) (n : ℕ) :
    truncatedLogEnergy D n (empiricalSourceProbability roots hN) =
      (N : ℝ≥0∞)⁻¹ ^ 2 * ∑ i, ∑ j,
        min (nonnegativeLogKernel D (roots i : ℂ) (roots j : ℂ)) n := by
  have hm : Measurable (fun p : S × S ↦
      min (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) (n : ℝ≥0∞)) := by
    exact (((continuous_nonnegativeLogKernel D).comp
      (by fun_prop : Continuous (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))))).min
        continuous_const).measurable
  change (∫⁻ p : S × S, min (nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)) n
    ∂((empiricalSourceProbability roots hN : Measure S).prod
      (empiricalSourceProbability roots hN : Measure S))) = _
  rw [lintegral_prod _ hm.aemeasurable, lintegral_empiricalSourceProbability]
  simp_rw [lintegral_empiricalSourceProbability, ← Finset.mul_sum]
  ring

theorem toReal_truncatedLogEnergy_empirical {S : Set ℂ} {N : ℕ}
    (roots : Fin N → S) (hN : 0 < N) (D : ℝ) (n : ℕ) :
    (truncatedLogEnergy D n (empiricalSourceProbability roots hN)).toReal =
      (N : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j,
        (min (nonnegativeLogKernel D (roots i : ℂ) (roots j : ℂ)) n).toReal := by
  rw [truncatedLogEnergy_empirical]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  congr 1
  have hf (i j : Fin N) :
      min (nonnegativeLogKernel D (roots i : ℂ) (roots j : ℂ)) (n : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  rw [ENNReal.toReal_sum (fun i _ ↦ ENNReal.sum_ne_top.mpr (fun j _ ↦ hf i j))]
  apply Finset.sum_congr rfl
  intro i hi
  exact ENNReal.toReal_sum (fun j _ ↦ hf i j)

theorem sum_truncated_kernel_le_of_log_sum_nonneg {S : Set ℂ} {N : ℕ}
    (roots : Fin N → S) (hinj : Function.Injective roots) {D : ℝ} (hD : 1 ≤ D)
    (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D) (n : ℕ)
    (hlog : 0 ≤ ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      Real.log (dist (roots p.1 : ℂ) (roots p.2 : ℂ))) :
    (∑ i, ∑ j, (min (nonnegativeLogKernel D (roots i : ℂ) (roots j : ℂ))
      (n : ℝ≥0∞)).toReal) ≤ (N : ℝ) * n + (N : ℝ) ^ 2 * Real.log D := by
  classical
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let t (p : Fin N × Fin N) :=
    (min (nonnegativeLogKernel D (roots p.1 : ℂ) (roots p.2 : ℂ)) (n : ℝ≥0∞)).toReal
  have hoff : (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, t p) ≤
      (N : ℝ) ^ 2 * Real.log D := by
    calc
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
          (Real.log D - Real.log (dist (roots p.1 : ℂ) (roots p.2 : ℂ))) := by
        apply Finset.sum_le_sum
        intro p hp
        have hne : (roots p.1 : ℂ) ≠ (roots p.2 : ℂ) := by
          intro he
          exact (Finset.mem_offDiag.mp hp).2.2 (hinj (Subtype.ext he))
        have hk : nonnegativeLogKernel D (roots p.1 : ℂ) (roots p.2 : ℂ) ≠ ⊤ := by
          rw [nonnegativeLogKernel_of_ne hD0 hne]
          exact ENNReal.ofReal_ne_top
        exact (ENNReal.toReal_mono hk (min_le_left _ _)).trans_eq
          (nonnegativeLogKernel_toReal_of_dist_le hD0 hne
            (hbound _ (roots p.1).property _ (roots p.2).property))
      _ = ((Finset.univ : Finset (Fin N)).offDiag.card : ℝ) * Real.log D -
          ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
            Real.log (dist (roots p.1 : ℂ) (roots p.2 : ℂ)) := by
        rw [Finset.sum_sub_distrib]
        simp
      _ ≤ (N : ℝ) ^ 2 * Real.log D := by
        have hc : (((Finset.univ : Finset (Fin N)).offDiag.card : ℕ) : ℝ) ≤ (N : ℝ)^2 := by
          have hcN : (Finset.univ : Finset (Fin N)).offDiag.card ≤ N * N := by
            simpa only [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] using
              Nat.sub_le (N * N) N
          exact_mod_cast (show (Finset.univ : Finset (Fin N)).offDiag.card ≤ N ^ 2 by
            simpa only [pow_two] using hcN)
        exact (sub_le_self _ hlog).trans (mul_le_mul_of_nonneg_right hc (Real.log_nonneg hD))
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ, t p := by
      rw [Finset.sum_product]
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N)).diag, t p +
        ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, t p := by
      rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
    _ = (N : ℝ) * n + ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, t p := by
      congr 1
      simp [t, nonnegativeLogKernel_self hD0]
    _ ≤ _ := add_le_add (le_refl _) hoff

theorem truncatedLogEnergy_empirical_le_of_log_sum_nonneg {S : Set ℂ} {N : ℕ}
    (roots : Fin N → S) (hN : 0 < N) (hinj : Function.Injective roots)
    {D : ℝ} (hD : 1 ≤ D) (hbound : ∀ z ∈ S, ∀ w ∈ S, dist z w ≤ D) (n : ℕ)
    (hlog : 0 ≤ ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      Real.log (dist (roots p.1 : ℂ) (roots p.2 : ℂ))) :
    truncatedLogEnergy D n (empiricalSourceProbability roots hN) ≤
      ENNReal.ofReal (Real.log D + (n : ℝ) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn : truncatedLogEnergy D n (empiricalSourceProbability roots hN) ≤ n := by
    calc
      _ ≤ ∫⁻ _ : S × S, (n : ℝ≥0∞) ∂((empiricalSourceProbability roots hN).prod
          (empiricalSourceProbability roots hN)) := lintegral_mono (fun _ ↦ min_le_right _ _)
      _ = n := by simp
  have hf : truncatedLogEnergy D n (empiricalSourceProbability roots hN) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hn
  apply (ENNReal.toReal_le_toReal hf ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (add_nonneg (Real.log_nonneg hD) (by positivity)),
    toReal_truncatedLogEnergy_empirical]
  calc
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * n + (N : ℝ)^2 * Real.log D) :=
      mul_le_mul_of_nonneg_left
        (sum_truncated_kernel_le_of_log_sum_nonneg roots hinj hD hbound n hlog) (by positivity)
    _ = Real.log D + (n : ℝ) / N := by field_simp; ring

end Erdos1040
