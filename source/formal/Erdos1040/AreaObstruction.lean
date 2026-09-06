import Erdos1040.Unbounded
import Erdos1040.PolynomialConclusion

/-!
Area obstruction for the separate capacity-only-dependence question.
Theorems here do not establish a capacity or transfinite-diameter identity.
The positive-degree hypothesis is retained throughout the lower bounds.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace Erdos1040

theorem ball_three_quarters_subset_unitLemniscate {n : ℕ} (hn : 0 < n)
    (roots : Fin n → ℂ) (hr : ∀ i, ‖roots i‖ ≤ (1 / 4 : ℝ)) :
    Metric.ball (0 : ℂ) (3 / 4 : ℝ) ⊆ unitLemniscate roots := by
  intro z hz
  have hz' : ‖z‖ < (3 / 4 : ℝ) := by simpa using hz
  have hc0 : 0 ≤ ‖z‖ + (1 / 4 : ℝ) := by positivity
  have hc1 : ‖z‖ + (1 / 4 : ℝ) < 1 := by linarith
  have hprod : (∏ i, ‖z - roots i‖) ≤ (‖z‖ + (1 / 4 : ℝ)) ^ n := by
    calc
      (∏ i, ‖z - roots i‖) ≤ ∏ _i : Fin n, (‖z‖ + (1 / 4 : ℝ)) :=
        Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦
          (norm_sub_le z (roots i)).trans (add_le_add le_rfl (hr i)))
      _ = _ := by simp
  change ‖∏ i, (z - roots i)‖ < 1
  rw [norm_prod]
  exact lt_of_le_of_lt hprod (pow_lt_one₀ hc0 hc1 (Nat.ne_of_gt hn))

theorem volume_ball_three_quarters :
    volume (Metric.ball (0 : ℂ) (3 / 4 : ℝ)) =
      ENNReal.ofReal (9 * Real.pi / 16) := by
  have hball : volume (Metric.ball (0 : ℂ) (3 / 4 : ℝ)) =
      ENNReal.ofReal ((3 / 4 : ℝ) ^ 2 * Real.pi) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    congr 1
    simpa only [NNReal.coe_real_pi] using
      (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm
  convert hball using 1 <;> congr 1 <;> ring

theorem volume_unitLemniscate_ge_nine_pi_sixteenths {n : ℕ} (hn : 0 < n)
    (roots : Fin n → ℂ) (hr : ∀ i, ‖roots i‖ ≤ (1 / 4 : ℝ)) :
    ENNReal.ofReal (9 * Real.pi / 16) ≤ volume (unitLemniscate roots) := by
  rw [← volume_ball_three_quarters]
  exact measure_mono (ball_three_quarters_subset_unitLemniscate hn roots hr)

theorem ball_three_quarters_subset_monic_sublevel (p : ℂ[X]) (hp : p.Monic)
    (hn : 0 < p.natDegree) (hr : ∀ z : ℂ, p.IsRoot z → ‖z‖ ≤ (1 / 4 : ℝ)) :
    Metric.ball (0 : ℂ) (3 / 4 : ℝ) ⊆ {z : ℂ | ‖p.eval z‖ < 1} := by
  intro z hz
  have hz' : ‖z‖ < (3 / 4 : ℝ) := by simpa using hz
  have hc0 : 0 ≤ ‖z‖ + (1 / 4 : ℝ) := by positivity
  have hc1 : ‖z‖ + (1 / 4 : ℝ) < 1 := by linarith
  have hsplit := IsAlgClosed.splits p
  have hcard : 0 < p.roots.card := by rwa [← hsplit.natDegree_eq_card_roots]
  have hprod : (p.roots.map (fun a ↦ ‖z - a‖)).prod ≤
      (‖z‖ + (1 / 4 : ℝ)) ^ p.roots.card := by
    calc
      _ ≤ (p.roots.map (fun _ : ℂ ↦ ‖z‖ + (1 / 4 : ℝ))).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun a _ ↦ norm_nonneg _) (fun a ha ↦
          (norm_sub_le z a).trans
            (add_le_add le_rfl (hr a (Polynomial.isRoot_of_mem_roots ha))))
      _ = _ := by simp
  have hnorm : ‖(p.roots.map (z - ·)).prod‖ =
      (p.roots.map (fun a ↦ ‖z - a‖)).prod := by
    suffices h : ∀ m : Multiset ℂ, ‖(m.map (z - ·)).prod‖ =
        (m.map (fun a ↦ ‖z - a‖)).prod from h p.roots
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]
  change ‖p.eval z‖ < 1
  rw [hsplit.eval_eq_prod_roots_of_monic hp z, hnorm]
  exact lt_of_le_of_lt hprod (pow_lt_one₀ hc0 hc1 (Nat.ne_of_gt hcard))

theorem volume_monic_sublevel_ge_nine_pi_sixteenths (p : ℂ[X]) (hp : p.Monic)
    (hn : 0 < p.natDegree) (hr : ∀ z : ℂ, p.IsRoot z → ‖z‖ ≤ (1 / 4 : ℝ)) :
    ENNReal.ofReal (9 * Real.pi / 16) ≤ volume {z : ℂ | ‖p.eval z‖ < 1} := by
  rw [← volume_ball_three_quarters]
  exact measure_mono (ball_three_quarters_subset_monic_sublevel p hp hn hr)

theorem volume_plus_minus_four_quadratic_le :
    volume {z : ℂ | ‖(z - 4) * (z - (-4))‖ < 1} ≤
      ENNReal.ofReal (Real.pi / 8) := by
  have h := volume_quadratic_sublevel_le (4 : ℂ) (-4) (by norm_num)
  have hdist : ‖(4 : ℂ) - (-4)‖ = 8 := by norm_num
  rw [hdist] at h
  convert h using 1 <;> congr 1 <;> ring

theorem exists_plus_minus_four_monic_small_area :
    ∃ p : ℂ[X], p.Monic ∧ 0 < p.natDegree ∧
      (∀ z : ℂ, p.IsRoot z ↔ z = 4 ∨ z = -4) ∧
      volume {z : ℂ | ‖p.eval z‖ < 1} ≤ ENNReal.ofReal (Real.pi / 8) := by
  let roots : Fin 2 → ℂ := ![4, -4]
  refine ⟨rootPolynomial roots, rootPolynomial_monic roots, ?_, ?_, ?_⟩
  · simp [rootPolynomial_natDegree]
  · intro z
    rw [rootPolynomial_isRoot_iff]
    simp [roots, Fin.exists_fin_two]
  · simpa [rootPolynomial_eval, roots, Fin.prod_univ_two] using
      volume_plus_minus_four_quadratic_le

theorem plus_minus_four_area_bound_lt_ball_obstruction :
    ENNReal.ofReal (Real.pi / 8) < ENNReal.ofReal (9 * Real.pi / 16) := by
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
  nlinarith [Real.pi_pos]

end Erdos1040
