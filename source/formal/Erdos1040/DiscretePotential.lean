import Erdos1040.AtomicApproximation
import Erdos1040.LogContinuity
import Erdos1040.AtomicPotential

/-!
Discretization of the area-L² logarithmic kernel using actual roots from the
original compact source set. Arbitrary-source potentials here are Bochner
integrals of L² classes. Pointwise source integrals are not implicitly equated
with those classes. Finite atomic expressions include the documented
totalized zero-degree case, while approximation always has positive degree.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Erdos1040

/-- Every finite atomic log potential belongs to area-L² on compact domains.
At degree zero the already defined atomic potential is identically zero. -/
theorem memLp_atomicLogPotential_of_isCompact {n : ℕ} (roots : Fin n → ℂ)
    {K : Set ℂ} (hK : IsCompact K) :
    MemLp (atomicLogPotential roots) 2 (volume.restrict K) := by
  have hs : MemLp (fun z : ℂ ↦ ∑ i, Real.log ‖z - roots i‖) 2 (volume.restrict K) :=
    memLp_finsetSum Finset.univ (fun i _ ↦ memLp_log_norm_sub_of_isCompact (roots i) hK)
  change MemLp (fun z : ℂ ↦ (∑ i, Real.log ‖z - roots i‖) / (n : ℝ))
    2 (volume.restrict K)
  simpa only [div_eq_mul_inv] using hs.mul_const ((n : ℝ)⁻¹)

/-- The equal-weight L² average has the actual atomic log potential as an
area-almost-everywhere representative, including the zero-degree convention. -/
theorem areaLogKernel_average_ae_eq_atomicLogPotential {n : ℕ} (roots : Fin n → ℂ)
    {K : Set ℂ} (hK : IsCompact K) :
    ⇑((n : ℝ)⁻¹ • ∑ i, areaLogKernel hK (roots i)) =ᵐ[volume.restrict K]
      atomicLogPotential roots := by
  have hall : ∀ᵐ z : ℂ ∂volume.restrict K,
      ∀ i, areaLogKernel hK (roots i) z = Real.log ‖z - roots i‖ :=
    Filter.eventually_all.mpr (fun i ↦
      (memLp_log_norm_sub_of_isCompact (roots i) hK).coeFn_toLp)
  filter_upwards [Lp.coeFn_smul ((n : ℝ)⁻¹) (∑ i, areaLogKernel hK (roots i)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ areaLogKernel hK (roots i)), hall]
    with z hsm hsum hlog
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hsm, hsum]
  simp only [hlog, atomicLogPotential, div_eq_mul_inv]
  exact mul_comm _ _

/-- The atomic potential's L² class is exactly the equal-weight sum of kernel classes. -/
theorem atomicLogPotential_toLp_eq_average_areaLogKernel {n : ℕ} (roots : Fin n → ℂ)
    {K : Set ℂ} (hK : IsCompact K) :
    (memLp_atomicLogPotential_of_isCompact roots hK).toLp (atomicLogPotential roots) =
      (n : ℝ)⁻¹ • ∑ i, areaLogKernel hK (roots i) := by
  apply Lp.ext
  exact (memLp_atomicLogPotential_of_isCompact roots hK).coeFn_toLp.trans
    (areaLogKernel_average_ae_eq_atomicLogPotential roots hK).symm

/-- The L²-valued logarithmic kernel is Bochner-integrable against every
probability measure on a compact source set. -/
theorem integrable_areaLogKernel_on_compact {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsProbabilityMeasure μ] :
    Integrable (fun w : S ↦ areaLogKernel hK (w : ℂ)) μ := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hk : Continuous (fun w : S ↦ areaLogKernel hK (w : ℂ)) :=
    (continuous_areaLogKernel hK).comp continuous_subtype_val
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hk.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

/-- Any probability on a compact source set admits positive-degree atomic
log potentials with roots in that same set approximating its Bochner L²
potential class to every positive tolerance. -/
theorem exists_roots_approx_areaLogKernel_integral {S K : Set ℂ} (hS : IsCompact S)
    (hK : IsCompact K) (μ : Measure S) [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ roots : Fin n → ℂ, (∀ i, roots i ∈ S) ∧
      ‖(memLp_atomicLogPotential_of_isCompact roots hK).toLp (atomicLogPotential roots) -
        ∫ w : S, areaLogKernel hK (w : ℂ) ∂μ‖ < ε := by
  obtain ⟨n, hn, points, hp⟩ := exists_equal_weight_average_on_compact hS μ
    (fun w : S ↦ areaLogKernel hK (w : ℂ))
    ((continuous_areaLogKernel hK).comp continuous_subtype_val) ε hε
  refine ⟨n, hn, (fun i ↦ (points i : ℂ)), (fun i ↦ (points i).property), ?_⟩
  rwa [atomicLogPotential_toLp_eq_average_areaLogKernel]

end Erdos1040
