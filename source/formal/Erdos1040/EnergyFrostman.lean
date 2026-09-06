import Erdos1040.EnergyVariation

/-!
The variational source-potential inequality for a finite minimizer of the
actual extended nonnegative logarithmic energy. The exceptional-set predicate
is transparent: no finite-energy source probability can be carried by the
set. It is not assumed to equal any unformalized notion of polar set.

Normalized restrictions preserve finite energy. Consequently every
measurable exceptional set is null for every finite-energy probability, and
the minimizing potential equals its energy almost everywhere for its own
measure. These are statements about the defined shifted/clipped kernel;
raw-logarithmic and classical-capacity correspondences remain separate.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace Erdos1040

/-- The actual extended nonnegative logarithmic potential at an arbitrary complex observation. -/
def nonnegativeLogPotential {S : Set ℂ} (D : ℝ) (μ : ProbabilityMeasure S) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ w : S, nonnegativeLogKernel D z (w : ℂ) ∂μ

/-- A source set carries no finite-energy probability if every source probability almost everywhere carried by it has infinite actual energy. -/
def HasNoFiniteLogEnergyProbability {S : Set ℂ} (D : ℝ) (A : Set S) : Prop :=
  ∀ ν : ProbabilityMeasure S, (∀ᵐ z : S ∂(ν : Measure S), z ∈ A) →
    nonnegativeLogEnergy D ν = ⊤

/-- The actual extended source potential is measurable in the observation point. -/
theorem measurable_nonnegativeLogPotential {S : Set ℂ} (D : ℝ) (μ : ProbabilityMeasure S) :
    Measurable (nonnegativeLogPotential D μ) := by
  unfold nonnegativeLogPotential
  apply Measurable.lintegral_prod_right' (ν := (μ : Measure S))
    (f := fun p : ℂ × S ↦ nonnegativeLogKernel D p.1 (p.2 : ℂ))
  exact ((continuous_nonnegativeLogKernel D).comp
    (by fun_prop : Continuous (fun p : ℂ × S ↦ (p.1, (p.2 : ℂ))))).measurable

/-- Tonelli identifies actual cross energy with the integral of one source potential against the other probability. -/
theorem nonnegativeLogCrossEnergy_eq_lintegral_potential {S : Set ℂ}
    (D : ℝ) (μ ν : ProbabilityMeasure S) :
    nonnegativeLogCrossEnergy D μ ν =
      ∫⁻ z : S, nonnegativeLogPotential D μ (z : ℂ) ∂ν := by
  rw [nonnegativeLogCrossEnergy_comm D μ ν]
  apply lintegral_prod
  exact ((continuous_nonnegativeLogKernel D).comp
    (by fun_prop : Continuous (fun p : S × S ↦ ((p.1 : ℂ), (p.2 : ℂ))))).measurable.aemeasurable

/-- The strict sublevel below the finite minimum energy carries no finite-energy source probability. -/
theorem hasNoFiniteLogEnergyProbability_sublevel_of_minimizer {S : Set ℂ} (D : ℝ) (μ : ProbabilityMeasure S)
    (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    (hmin : ∀ ρ : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ρ) :
    HasNoFiniteLogEnergyProbability D
      {z : S | nonnegativeLogPotential D μ (z : ℂ) < nonnegativeLogEnergy D μ} := by
  intro ν hνA
  by_contra hν
  have hvar := nonnegativeLogEnergy_le_crossEnergy_of_minimizer D μ hμ hmin ν hν
  rw [nonnegativeLogCrossEnergy_eq_lintegral_potential] at hvar
  have hle : (∫⁻ z : S, nonnegativeLogPotential D μ (z : ℂ) ∂ν) ≤
      nonnegativeLogEnergy D μ := by
    simpa only [lintegral_const, measure_univ, mul_one] using
      lintegral_mono_ae (ae_le_of_ae_lt hνA)
  have hfinite : (∫⁻ z : S, nonnegativeLogPotential D μ (z : ℂ) ∂ν) ≠ ⊤ :=
    ne_top_of_le_ne_top hμ hle
  have hlt := lintegral_strict_mono (IsProbabilityMeasure.ne_zero (ν : Measure S))
    aemeasurable_const hfinite hνA
  simp only [lintegral_const, measure_univ, mul_one] at hlt
  exact (not_lt_of_ge hvar) hlt

/-- The actual conditional probability obtained by normalizing a restriction of positive measure. -/
def probabilityRestriction {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (A : Set Ω) (hA : (μ : Measure Ω) A ≠ 0) :
    ProbabilityMeasure Ω :=
  ⟨ProbabilityTheory.cond (μ : Measure Ω) A, ProbabilityTheory.cond_isProbabilityMeasure hA⟩

/-- Normalizing a positive-measure restriction of a finite-energy source probability preserves finite energy. -/
theorem finite_nonnegativeLogEnergy_probabilityRestriction {S : Set ℂ} (D : ℝ) (μ : ProbabilityMeasure S)
    (hμ : nonnegativeLogEnergy D μ ≠ ⊤) (A : Set S) (hA : (μ : Measure S) A ≠ 0) :
    nonnegativeLogEnergy D (probabilityRestriction μ A hA) ≠ ⊤ := by
  have hle : (∫⁻ p : S × S, nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)
      ∂((μ : Measure S).restrict A).prod ((μ : Measure S).restrict A)) ≤
      nonnegativeLogEnergy D μ :=
    lintegral_mono' (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
      (fun _ ↦ le_rfl)
  have hfinite := ne_top_of_le_ne_top hμ hle
  change (∫⁻ p : S × S, nonnegativeLogKernel D (p.1 : ℂ) (p.2 : ℂ)
    ∂(((μ : Measure S) A)⁻¹ • (μ : Measure S).restrict A).prod
      (((μ : Measure S) A)⁻¹ • (μ : Measure S).restrict A)) ≠ ⊤
  rw [Measure.prod_smul_left, Measure.prod_smul_right,
    lintegral_smul_measure, lintegral_smul_measure]
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA) hfinite)

/-- Every measurable set carrying no finite-energy source probability is null for every finite-energy source probability. -/
theorem measure_eq_zero_of_hasNoFiniteLogEnergyProbability {S : Set ℂ}
    (D : ℝ) (μ : ProbabilityMeasure S) (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    {A : Set S} (hA : MeasurableSet A) (hnull : HasNoFiniteLogEnergyProbability D A) :
    (μ : Measure S) A = 0 := by
  by_contra hA0
  have hfinite := finite_nonnegativeLogEnergy_probabilityRestriction D μ hμ A hA0
  have hcarried : ∀ᵐ z : S ∂(probabilityRestriction μ A hA0 : Measure S), z ∈ A :=
    ProbabilityTheory.ae_cond_mem hA
  exact hfinite (hnull (probabilityRestriction μ A hA0) hcarried)

/-- The actual extended potential of a finite energy minimizer equals its energy almost everywhere for that minimizer. -/
theorem nonnegativeLogPotential_ae_eq_energy_of_minimizer {S : Set ℂ} (D : ℝ) (μ : ProbabilityMeasure S)
    (hμ : nonnegativeLogEnergy D μ ≠ ⊤)
    (hmin : ∀ ρ : ProbabilityMeasure S, nonnegativeLogEnergy D μ ≤ nonnegativeLogEnergy D ρ) :
    (fun z : S ↦ nonnegativeLogPotential D μ (z : ℂ)) =ᵐ[(μ : Measure S)]
      fun _ ↦ nonnegativeLogEnergy D μ := by
  have hmeas : Measurable (fun z : S ↦ nonnegativeLogPotential D μ (z : ℂ)) :=
    (measurable_nonnegativeLogPotential D μ).comp measurable_subtype_coe
  have hbad := measure_eq_zero_of_hasNoFiniteLogEnergyProbability D μ hμ
    (measurableSet_lt hmeas measurable_const)
    (hasNoFiniteLogEnergyProbability_sublevel_of_minimizer D μ hμ hmin)
  have hge : (fun _ : S ↦ nonnegativeLogEnergy D μ) ≤ᵐ[(μ : Measure S)]
      fun z : S ↦ nonnegativeLogPotential D μ (z : ℂ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad] with z hz
    exact le_of_not_gt hz
  have henergy : (∫⁻ z : S, nonnegativeLogPotential D μ (z : ℂ) ∂μ) =
      nonnegativeLogEnergy D μ :=
    (nonnegativeLogCrossEnergy_eq_lintegral_potential D μ μ).symm
  apply Filter.EventuallyEq.symm
  apply ae_eq_of_ae_le_of_lintegral_le hge
  · simpa only [lintegral_const, measure_univ, mul_one] using hμ
  · exact hmeas.aemeasurable
  · simp only [henergy, lintegral_const, measure_univ, mul_one, le_refl]
end Erdos1040

