import Erdos1040.LogEnergy

/-!
First variation of the actual extended nonnegative logarithmic energy.
Probability mixtures are defined by their actual weighted measures, and the
quadratic identity remains valid for infinite energies. Real-number
conversion is used only after all three relevant energies are finite.

The minimizer inequality covers every finite-energy probability competitor,
including infinite cross energy as a separate case. It is a variational
inequality for the defined shifted/clipped kernel. Its classical untruncated
interpretation still requires the positive scale and source-distance bounds
of the energy correspondence; no Frostman conclusion is assumed here.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace Erdos1040

/-- The probability measure with actual weights 1-t and t for a parameter in the unit interval. -/
def probabilityMixture {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : ProbabilityMeasure Ω) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ProbabilityMeasure Ω :=
  ⟨ENNReal.ofReal (1 - t) • (μ : Measure Ω) + ENNReal.ofReal t • (ν : Measure Ω),
    ⟨by
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht1) ht0]
      simp⟩⟩

/-- The actual extended cross energy of two source probabilities for the nonnegative logarithmic kernel. -/
def nonnegativeLogCrossEnergy {S : Set ℂ} (D : ℝ)
    (μ ν : ProbabilityMeasure S) : ℝ≥0∞ :=
  ∫⁻ p : S × S, nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ) ∂(μ.prod ν)

/-- The actual cross energy is symmetric, including infinite values. -/
theorem nonnegativeLogCrossEnergy_comm {S : Set ℂ} (D : ℝ)
    (μ ν : ProbabilityMeasure S) :
    nonnegativeLogCrossEnergy D μ ν = nonnegativeLogCrossEnergy D ν μ := by
  calc nonnegativeLogCrossEnergy D μ ν =
      ∫⁻ p : S × S, nonnegativeLogKernel D (p.2 : ℂ) (p.1 : ℂ)
        ∂(ν : Measure S).prod (μ : Measure S) :=
          (lintegral_prod_swap (μ := (μ : Measure S)) (ν := (ν : Measure S))
            (fun p : S × S ↦ nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ))).symm
    _ = nonnegativeLogCrossEnergy D ν μ := by
      apply lintegral_congr
      intro p
      simp only [nonnegativeLogKernel, edist_comm]

/-- The exact extended quadratic energy identity for actual convex probability mixtures. -/
theorem nonnegativeLogEnergy_probabilityMixture {S : Set ℂ} (D : ℝ) (μ ν : ProbabilityMeasure S)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    nonnegativeLogEnergy D (probabilityMixture μ ν t ht0 ht1) =
      ENNReal.ofReal (1 - t) ^ 2 * nonnegativeLogEnergy D μ +
      2 * ENNReal.ofReal (1 - t) * ENNReal.ofReal t * nonnegativeLogCrossEnergy D μ ν +
      ENNReal.ofReal t ^ 2 * nonnegativeLogEnergy D ν := by
  change (∫⁻ p : S × S, nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)
    ∂(ENNReal.ofReal (1 - t) • (μ : Measure S) + ENNReal.ofReal t • (ν : Measure S)).prod
      (ENNReal.ofReal (1 - t) • (μ : Measure S) + ENNReal.ofReal t • (ν : Measure S))) = _
  simp only [Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
    Measure.prod_smul_right, lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
  change
    ENNReal.ofReal (1 - t) *
      (ENNReal.ofReal (1 - t) * nonnegativeLogEnergy D μ +
        ENNReal.ofReal t * nonnegativeLogCrossEnergy D ν μ) +
    ENNReal.ofReal t *
      (ENNReal.ofReal (1 - t) * nonnegativeLogCrossEnergy D μ ν +
        ENNReal.ofReal t * nonnegativeLogEnergy D ν) = _
  rw [nonnegativeLogCrossEnergy_comm D ν μ]
  ring

/-- The real quadratic mixture identity under explicit finiteness of both self-energies and the cross energy. -/
theorem toReal_nonnegativeLogEnergy_probabilityMixture {S : Set ℂ} (D : ℝ) (μ ν : ProbabilityMeasure S)
    (hμ : nonnegativeLogEnergy D μ ≠ ⊤) (hν : nonnegativeLogEnergy D ν ≠ ⊤)
    (hcross : nonnegativeLogCrossEnergy D μ ν ≠ ⊤)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (nonnegativeLogEnergy D (probabilityMixture μ ν t ht0 ht1)).toReal =
      (1 - t) ^ 2 * (nonnegativeLogEnergy D μ).toReal +
      2 * (1 - t) * t * (nonnegativeLogCrossEnergy D μ ν).toReal +
      t ^ 2 * (nonnegativeLogEnergy D ν).toReal := by
  rw [nonnegativeLogEnergy_probabilityMixture]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ht1), ENNReal.toReal_ofReal ht0]
  norm_num

/-- A finite global minimizer has self-energy at most its cross energy with every finite-energy probability competitor. -/
theorem nonnegativeLogEnergy_le_crossEnergy_of_minimizer {S : Set ℂ} (D : ℝ) (μ : ProbabilityMeasure S)
    (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    (hmin : ∀ ρ : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ρ)
    (ν : ProbabilityMeasure S) (hν : nonnegativeLogEnergy D ν ≠ ⊤) :
    nonnegativeLogEnergy D μ ≤ nonnegativeLogCrossEnergy D μ ν := by
  by_cases hcross : nonnegativeLogCrossEnergy D μ ν = ⊤
  · rw [hcross]
    exact le_top
  · apply (ENNReal.toReal_le_toReal hμ hcross).mp
    let a : ℝ := (nonnegativeLogEnergy D μ).toReal
    let b : ℝ := (nonnegativeLogCrossEnergy D μ ν).toReal
    let d : ℝ := (nonnegativeLogEnergy D ν).toReal
    have hquad (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
        a ≤ (1 - t) ^ 2 * a + 2 * (1 - t) * t * b + t ^ 2 * d := by
      have hfinite : nonnegativeLogEnergy D (probabilityMixture μ ν t ht0 ht1) ≠ ⊤ := by
        rw [nonnegativeLogEnergy_probabilityMixture]
        finiteness
      have hm := ENNReal.toReal_mono hfinite (hmin (probabilityMixture μ ν t ht0 ht1))
      rw [toReal_nonnegativeLogEnergy_probabilityMixture D μ ν hμ hν hcross t ht0 ht1] at hm
      exact hm
    change a ≤ b
    by_contra hab
    have hgap : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
    let B : ℝ := |a - 2 * b + d| + 1
    have hB : 0 < B := by dsimp [B]; positivity
    let t : ℝ := min (1 / 2) ((a - b) / B)
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hgap hB)
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have htB : t * B ≤ a - b := (le_div_iff₀ hB).mp (min_le_right _ _)
    have hcoef : a - 2 * b + d ≤ B := by
      dsimp [B]
      linarith [le_abs_self (a - 2 * b + d)]
    have htcoef : t * (a - 2 * b + d) ≤ a - b :=
      (mul_le_mul_of_nonneg_left hcoef ht0.le).trans htB
    have hprod := mul_le_mul_of_nonneg_left htcoef ht0.le
    have hq := hquad t ht0.le ht1
    nlinarith [mul_pos ht0 hgap]
end Erdos1040

