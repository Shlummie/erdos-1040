import Mathlib

/-!
Exact finite-root objects for Erdős #1040. The area is planar Lebesgue
measure and the sublevel inequality is strict. Repeated roots are allowed.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Polynomial

namespace Erdos1040

/-- The monic polynomial with the given list of roots, including multiplicities. -/
def rootPolynomial {n : ℕ} (roots : Fin n → ℂ) : ℂ[X] :=
  ∏ i, (X - C (roots i))

/-- The open unit lemniscate of the product with the given roots. -/
def unitLemniscate {n : ℕ} (roots : Fin n → ℂ) : Set ℂ :=
  {z | ‖∏ i, (z - roots i)‖ < 1}

/-- The exact small-area conclusion, with a positive degree and roots in `F`. -/
def HasArbitrarilySmallLemniscates (F : Set ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∃ roots : Fin n → ℂ,
    (∀ i, roots i ∈ F) ∧ volume (unitLemniscate roots) < ENNReal.ofReal ε

theorem rootPolynomial_monic {n : ℕ} (roots : Fin n → ℂ) :
    (rootPolynomial roots).Monic := by
  exact monic_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C (roots i))

theorem rootPolynomial_eval {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) :
    (rootPolynomial roots).eval z = ∏ i, (z - roots i) := by
  simp [rootPolynomial, eval_prod]

theorem rootPolynomial_natDegree {n : ℕ} (roots : Fin n → ℂ) :
    (rootPolynomial roots).natDegree = n := by
  simp only [rootPolynomial,
    natDegree_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C (roots i)),
    natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem rootPolynomial_isRoot_iff {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) :
    (rootPolynomial roots).IsRoot z ↔ ∃ i, z = roots i := by
  simp [IsRoot, rootPolynomial_eval, Finset.prod_eq_zero_iff, sub_eq_zero]

end Erdos1040
