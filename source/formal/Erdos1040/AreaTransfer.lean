import Mathlib

/-! The quantitative sign-transfer step used after L² approximation. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos1040

/-- A positive margin for `g` and an L² approximation error control the negative set of `f`. -/
theorem measure_neg_le_margin_add_sq_eLpNorm (μ : Measure ℂ) (f g : ℂ → ℝ)
    (hfg : AEStronglyMeasurable (fun z ↦ f z - g z) μ)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    μ {z | f z < 0} ≤ μ {z | g z < (δ : ℝ)} +
      (δ : ℝ≥0∞)⁻¹ ^ 2 * eLpNorm (fun z ↦ f z - g z) 2 μ ^ 2 := by
  have hcover : {z | f z < 0} ⊆ {z | g z < (δ : ℝ)} ∪
      {z | (δ : ℝ≥0∞) ≤ ‖f z - g z‖ₑ} := by
    intro z hz
    change f z < 0 at hz
    by_cases hg : g z < (δ : ℝ)
    · exact Or.inl hg
    · right
      have hreal : (δ : ℝ) ≤ |f z - g z| := by
        have habs := neg_le_abs (f z - g z)
        push_neg at hg
        linarith
      change (δ : ℝ≥0∞) ≤ ‖f z - g z‖ₑ
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hreal
  have hmarkov : μ {z | (δ : ℝ≥0∞) ≤ ‖f z - g z‖ₑ} ≤
      (δ : ℝ≥0∞)⁻¹ ^ 2 * eLpNorm (fun z ↦ f z - g z) 2 μ ^ 2 := by
    simpa using meas_ge_le_mul_pow_eLpNorm_enorm (p := 2) (ε := (δ : ℝ≥0∞)) μ
      (by norm_num) (by norm_num) hfg
      (by exact_mod_cast hδ.ne') (by simp)
  exact (measure_mono hcover).trans
    ((measure_union_le _ _).trans (add_le_add_right hmarkov _))

end Erdos1040
