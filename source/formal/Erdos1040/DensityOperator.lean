import Erdos1040.SourceDensity
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
The actual bounded measurable source-density space and its logarithmic
potential operator. The closure criterion is conditional Hilbert-space
duality; annihilator vanishing must still be supplied by the potential proof.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Erdos1040

def boundedMeasurableDensities (S : Set ℂ) : Submodule ℝ (S → ℝ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C}
  zero_mem' := ⟨measurable_const, 0, fun _ ↦ by simp⟩
  add_mem' := by
    intro f g hf hg
    obtain ⟨C, hC⟩ := hf.2
    obtain ⟨D, hD⟩ := hg.2
    exact ⟨hf.1.add hg.1, C + D, fun w ↦ (norm_add_le (f w) (g w)).trans
      (add_le_add (hC w) (hD w))⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨C, hC⟩ := hf.2
    refine ⟨measurable_const.smul hf.1, ‖c‖ * C, fun w ↦ ?_⟩
    simpa only [Pi.smul_apply, norm_smul] using
      mul_le_mul_of_nonneg_left (hC w) (norm_nonneg c)

def sourceDensityOperator {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (μ : Measure S) [IsFiniteMeasure μ] :
    boundedMeasurableDensities S →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun f := ∫ w : S, f.val w • areaLogKernel hK (w : ℂ) ∂μ
  map_add' := by
    intro f g
    change (∫ w : S, (f.val w + g.val w) • areaLogKernel hK (w : ℂ) ∂μ) = _
    simp_rw [add_smul]
    exact integral_add
      (integrable_areaLogKernel_density hS hK μ f.val f.property.1
        f.property.2.choose f.property.2.choose_spec)
      (integrable_areaLogKernel_density hS hK μ g.val g.property.1
        g.property.2.choose g.property.2.choose_spec)
  map_smul' := by
    intro c f
    change (∫ w : S, (c * f.val w) • areaLogKernel hK (w : ℂ) ∂μ) =
      c • ∫ w : S, f.val w • areaLogKernel hK (w : ℂ) ∂μ
    simp_rw [mul_smul]
    exact integral_smul c _

theorem exists_density_approx_of_annihilator {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (μ : Measure S) [IsFiniteMeasure μ]
    (u : Lp ℝ 2 (volume.restrict K))
    (hu : ∀ h : Lp ℝ 2 (volume.restrict K),
      (∀ f : S → ℝ, Measurable f → (∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) →
        ⟪h, ∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ⟫_ℝ = 0) →
      ⟪h, u⟫_ℝ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : S → ℝ, Measurable f ∧ (∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) ∧
      ‖(∫ w : S, f w • areaLogKernel hK (w : ℂ) ∂μ) - u‖ < ε := by
  let T := sourceDensityOperator hS hK μ
  let R := LinearMap.range T
  have huO : u ∈ R.orthogonal.orthogonal := by
    apply (R.orthogonal.mem_orthogonal u).2
    intro h hh
    apply hu h
    intro f hf hb
    let v : boundedMeasurableDensities S := ⟨f, hf, hb⟩
    exact (R.mem_orthogonal' h).1 hh (T v) ⟨v, rfl⟩
  rw [R.orthogonal_orthogonal_eq_closure] at huO
  change u ∈ closure (R : Set (Lp ℝ 2 (volume.restrict K))) at huO
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp huO ε hε
  obtain ⟨v, rfl⟩ := hy
  refine ⟨v.val, v.property.1, v.property.2, ?_⟩
  change ‖T v - u‖ < ε
  simpa only [dist_eq_norm, norm_sub_rev] using hdist

end Erdos1040
