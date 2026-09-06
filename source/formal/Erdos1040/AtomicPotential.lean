import Erdos1040.Basic

/-!
The finite atomic potential uses Lean's totalized real logarithm. Its sign
matches the strict polynomial sublevel away from the finite root set. The
almost-everywhere and area identities below explicitly remove that null set.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Erdos1040

/-- An area-almost-everywhere representative of the equal-weight log potential. -/
def atomicLogPotential {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℝ :=
  (∑ i, Real.log ‖z - roots i‖) / (n : ℝ)

theorem atomicLogPotential_eq_log_product {n : ℕ} (roots : Fin n → ℂ)
    (z : ℂ) (hz : ∀ i, z ≠ roots i) :
    atomicLogPotential roots z = Real.log ‖∏ i, (z - roots i)‖ / (n : ℝ) := by
  rw [atomicLogPotential, norm_prod, Real.log_prod]
  intro i _
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz i))

theorem atomicLogPotential_neg_iff {n : ℕ} (hn : 0 < n)
    (roots : Fin n → ℂ) (z : ℂ) (hz : ∀ i, z ≠ roots i) :
    atomicLogPotential roots z < 0 ↔ z ∈ unitLemniscate roots := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < ‖∏ i, (z - roots i)‖ := by
    apply norm_pos_iff.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ sub_ne_zero.mpr (hz i))
  rw [atomicLogPotential_eq_log_product roots z hz, div_lt_iff₀ hnR,
    zero_mul, Real.log_neg_iff hp]
  rfl

theorem ae_ne_roots {n : ℕ} (roots : Fin n → ℂ) :
    ∀ᵐ z : ℂ ∂volume, ∀ i, z ≠ roots i := by
  exact Filter.eventually_all.mpr (fun i ↦ volume.ae_ne (roots i))

theorem unitLemniscate_ae_eq_atomicLogPotential_neg {n : ℕ} (hn : 0 < n)
    (roots : Fin n → ℂ) :
    unitLemniscate roots =ᵐ[volume] {z | atomicLogPotential roots z < 0} := by
  filter_upwards [ae_ne_roots roots] with z hz
  exact propext (atomicLogPotential_neg_iff hn roots z hz).symm

theorem volume_unitLemniscate_eq_atomicLogPotential_neg {n : ℕ} (hn : 0 < n)
    (roots : Fin n → ℂ) :
    volume (unitLemniscate roots) = volume {z | atomicLogPotential roots z < 0} := by
  exact measure_congr (unitLemniscate_ae_eq_atomicLogPotential_neg hn roots)

end Erdos1040
