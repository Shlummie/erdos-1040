import Erdos1040.GeometricDiameter

/-!
Saff's finite geometric diameters decrease with their order. The proof uses
deletion of each point from a configuration and averages the exact logarithms
of its pair products. It includes repeated configurations by treating their
zero pair product separately. Consequently the geometric infimum already
defined in GeometricDiameter is the actual decreasing-sequence limit.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1040

theorem sum_matrix_succAbove_eq {n : ℕ} (L : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, L i j = L j i) (hdiag : ∀ i, L i i = 0) (k : Fin (n + 1)) :
    (∑ i : Fin n, ∑ j : Fin n, L (k.succAbove i) (k.succAbove j)) =
      (∑ i, ∑ j, L i j) - 2 * ∑ j, L k j := by
  have hcol : (∑ i : Fin n, L (k.succAbove i) k) = ∑ j, L k j := by
    have heq : (∑ i, L i k) = ∑ j, L k j :=
      Finset.sum_congr rfl (fun i _ ↦ hsym i k)
    rw [Fin.sum_univ_succAbove (fun i ↦ L i k) k, hdiag, zero_add] at heq
    exact heq
  have hfull : (∑ i, ∑ j, L i j) = 2 * (∑ j, L k j) +
      ∑ i : Fin n, ∑ j : Fin n, L (k.succAbove i) (k.succAbove j) := by
    rw [Fin.sum_univ_succAbove (fun i ↦ ∑ j, L i j) k]
    have hrows : (∑ i : Fin n, ∑ j, L (k.succAbove i) j) =
        ∑ i : Fin n, (L (k.succAbove i) k +
          ∑ j : Fin n, L (k.succAbove i) (k.succAbove j)) :=
      Finset.sum_congr rfl (fun i _ ↦ Fin.sum_univ_succAbove
        (fun j ↦ L (k.succAbove i) j) k)
    rw [hrows, Finset.sum_add_distrib, hcol]
    ring
  linarith

theorem sum_succAbove_matrix_eq {n : ℕ} (L : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, L i j = L j i) (hdiag : ∀ i, L i i = 0) :
    (∑ k : Fin (n + 1), ∑ i : Fin n, ∑ j : Fin n,
      L (k.succAbove i) (k.succAbove j)) =
      ((n + 1 : ℝ) - 2) * ∑ i, ∑ j, L i j := by
  simp_rw [sum_matrix_succAbove_eq L hsym hdiag]
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem sum_log_dist_eq_twice_log_unorderedPairProduct {N : ℕ}
    (x : Fin N → ℂ) (hx : Function.Injective x) :
    (∑ i, ∑ j, Real.log (dist (x i) (x j))) =
      2 * Real.log (unorderedPairProduct x) := by
  calc
    _ = ∑ p : Fin N × Fin N, Real.log (dist (x p.1) (x p.2)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        Real.log (dist (x p.1) (x p.2)) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ hp
      have heq : p.1 = p.2 := by simpa using hp
      simp [heq]
    _ = _ := sum_offDiag_log_dist_eq_twice_log_unorderedPairProduct x hx

theorem unorderedPairProduct_pos_of_injective {N : ℕ}
    (x : Fin N → ℂ) (hx : Function.Injective x) :
    0 < unorderedPairProduct x := by
  apply Finset.prod_pos
  intro p hp
  exact dist_pos.mpr (fun heq ↦ (ne_of_lt (Finset.mem_filter.mp hp).2) (hx heq))

theorem log_geometricMeanSeparation_eq {N : ℕ}
    (x : Fin N → ℂ) (hx : Function.Injective x) :
    Real.log (geometricMeanSeparation x) =
      (∑ i, ∑ j, Real.log (dist (x i) (x j))) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  rw [geometricMeanSeparation, Real.log_rpow (unorderedPairProduct_pos_of_injective x hx),
    sum_log_dist_eq_twice_log_unorderedPairProduct x hx]
  ring

theorem sum_log_geometricMeanSeparation_succAbove {n : ℕ}
    (x : Fin (n + 3) → ℂ) (hx : Function.Injective x) :
    (∑ k : Fin (n + 3), Real.log (geometricMeanSeparation
      (fun i : Fin (n + 2) ↦ x (k.succAbove i)))) =
      (n + 3 : ℝ) * Real.log (geometricMeanSeparation x) := by
  have hdel (k : Fin (n + 3)) : Function.Injective
      (fun i : Fin (n + 2) ↦ x (k.succAbove i)) :=
    hx.comp Fin.succAbove_right_injective
  simp_rw [log_geometricMeanSeparation_eq _ (hdel _)]
  rw [← Finset.sum_div, sum_succAbove_matrix_eq (fun i j ↦ Real.log (dist (x i) (x j)))
    (fun i j ↦ by rw [dist_comm]) (fun i ↦ by simp), log_geometricMeanSeparation_eq x hx]
  push_cast
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have h2' : (n : ℝ) + 2 - 1 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h3' : (n : ℝ) + 3 - 1 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  field_simp
  ring

theorem exists_geometricMeanSeparation_le_succAbove {n : ℕ}
    (x : Fin (n + 3) → ℂ) :
    ∃ k : Fin (n + 3), geometricMeanSeparation x ≤
      geometricMeanSeparation (fun i : Fin (n + 2) ↦ x (k.succAbove i)) := by
  by_cases hp : unorderedPairProduct x = 0
  · have hq : 0 < 2 / (((n + 3 : ℕ) : ℝ) * (((n + 3 : ℕ) : ℝ) - 1)) := by
      have hn : (1 : ℝ) < (n + 3 : ℕ) := by exact_mod_cast (show 1 < n + 3 by omega)
      positivity
    have hz : geometricMeanSeparation x = 0 := by
      rw [geometricMeanSeparation, hp, Real.zero_rpow hq.ne']
    refine ⟨0, ?_⟩
    rw [hz]
    exact Real.rpow_nonneg (Finset.prod_nonneg (fun _ _ ↦ dist_nonneg)) _
  · have hx : Function.Injective x := by
      have hprod := Finset.prod_ne_zero_iff.mp hp
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hprod (i, j) (by simp [hlt])) (dist_eq_zero.mpr hij)
      · exact (hprod (j, i) (by simp [hgt])) (dist_eq_zero.mpr hij.symm)
    have hsum : (∑ _k : Fin (n + 3), Real.log (geometricMeanSeparation x)) ≤
        ∑ k : Fin (n + 3), Real.log (geometricMeanSeparation
          (fun i : Fin (n + 2) ↦ x (k.succAbove i))) := by
      simpa using (sum_log_geometricMeanSeparation_succAbove x hx).ge
    obtain ⟨k, _, hk⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    refine ⟨k, (Real.log_le_log_iff ?_ ?_).mp hk⟩
    · exact Real.rpow_pos_of_pos (unorderedPairProduct_pos_of_injective x hx) _
    · exact Real.rpow_pos_of_pos (unorderedPairProduct_pos_of_injective _
        (hx.comp Fin.succAbove_right_injective)) _

theorem finiteDiameter_succ_le (S : Set ℂ) {N : ℕ} (hN : 2 ≤ N) :
    finiteDiameter S (N + 1) ≤ finiteDiameter S N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, (Nat.sub_add_cancel hN).symm⟩
  unfold finiteDiameter
  apply iSup_le
  intro x
  obtain ⟨k, hk⟩ := exists_geometricMeanSeparation_le_succAbove (fun i ↦ (x i : ℂ))
  exact (ENNReal.ofReal_le_ofReal hk).trans (le_iSup
    (fun y : Fin (n + 2) → S ↦ ENNReal.ofReal (geometricMeanSeparation
      (fun i ↦ (y i : ℂ)))) (fun i ↦ x (k.succAbove i)))

theorem antitone_finiteDiameter (S : Set ℂ) :
    Antitone (fun n : ℕ ↦ finiteDiameter S (n + 2)) := by
  apply antitone_nat_of_succ_le
  intro n
  exact finiteDiameter_succ_le S (by omega : 2 ≤ n + 2)

theorem tendsto_finiteDiameter_transfiniteDiameter (S : Set ℂ) :
    Tendsto (fun n : ℕ ↦ finiteDiameter S (n + 2)) atTop (𝓝 (transfiniteDiameter S)) :=
  tendsto_atTop_iInf (antitone_finiteDiameter S)

end Erdos1040
