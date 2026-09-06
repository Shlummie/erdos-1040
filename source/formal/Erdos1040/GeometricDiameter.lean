import Mathlib

/-!
The geometric definition in Saff, equations (1.1) and (1.4), pp. 167-169.
Finite diameters use the exact unordered-pair product and exponent 2/(N(N-1)).
The extended supremum allows arbitrary source sets; it is an attained finite
maximum on nonempty compacts. Orders zero and one use the totalized displayed
formula and are excluded from the transfinite diameter's N >= 2 sequence.
The empty source has transfinite diameter zero. Extended suprema retain any
unbounded values; no energy or capacity predicate is substituted here.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1040

def unorderedPairProduct {N : ℕ} (x : Fin N → ℂ) : ℝ :=
  ∏ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p ↦ p.1 < p.2),
    dist (x p.1) (x p.2)

def geometricMeanSeparation {N : ℕ} (x : Fin N → ℂ) : ℝ :=
  (unorderedPairProduct x) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1)))

def finiteDiameter (S : Set ℂ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ x : Fin N → S, ENNReal.ofReal (geometricMeanSeparation (fun i ↦ (x i : ℂ)))

def transfiniteDiameter (S : Set ℂ) : ℝ≥0∞ :=
  ⨅ n : ℕ, finiteDiameter S (n + 2)

theorem continuous_unorderedPairProduct (N : ℕ) :
    Continuous (unorderedPairProduct (N := N)) := by
  apply continuous_finsetProd
  intro p _
  exact (continuous_apply p.1).dist (continuous_apply p.2)

theorem continuous_geometricMeanSeparation {N : ℕ} (hN : 2 ≤ N) :
    Continuous (geometricMeanSeparation (N := N)) := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hN)
  exact (continuous_unorderedPairProduct N).rpow_const (fun _ ↦ Or.inr (by positivity))

theorem finiteDiameter_eq_max_of_compact {S : Set ℂ} (hS : IsCompact S)
    (hne : S.Nonempty) {N : ℕ} (hN : 2 ≤ N) :
    ∃ x : Fin N → S, finiteDiameter S N =
      ENNReal.ofReal (geometricMeanSeparation (fun i ↦ (x i : ℂ))) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have : Nonempty S := hne.to_subtype
  have ht : Continuous (fun x : Fin N → S ↦ fun i ↦ (x i : ℂ)) :=
    continuous_pi (fun i ↦ continuous_subtype_val.comp (continuous_apply i))
  have hc := (continuous_geometricMeanSeparation hN).comp ht
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  unfold finiteDiameter
  refine ⟨x, le_antisymm ?_ (le_iSup
    (fun y : Fin N → S ↦ ENNReal.ofReal (geometricMeanSeparation (fun i ↦ (y i : ℂ)))) x)⟩
  exact iSup_le (fun y ↦ ENNReal.ofReal_le_ofReal (hx (Set.mem_univ y)))

theorem finiteDiameter_empty {N : ℕ} (hN : 0 < N) : finiteDiameter ∅ N = 0 := by
  unfold finiteDiameter
  apply iSup_eq_bot.mpr
  intro x
  exact (x ⟨0, hN⟩).property.elim

theorem transfiniteDiameter_empty : transfiniteDiameter ∅ = 0 := by
  apply bot_unique
  exact (iInf_le (fun n : ℕ ↦ finiteDiameter ∅ (n + 2)) 0).trans_eq
    (finiteDiameter_empty (by decide : 0 < 2))

theorem finiteDiameter_lt_top_of_compact {S : Set ℂ} (hS : IsCompact S)
    {N : ℕ} (hN : 2 ≤ N) : finiteDiameter S N < ⊤ := by
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx⟩ := finiteDiameter_eq_max_of_compact hS hne hN
    rw [hx]
    exact ENNReal.ofReal_lt_top
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, finiteDiameter_empty (by omega)]
    exact ENNReal.zero_lt_top

theorem exists_distinct_configuration_of_one_le_transfiniteDiameter {S : Set ℂ}
    (hS : IsCompact S) (hτ : 1 ≤ transfiniteDiameter S) {N : ℕ} (hN : 2 ≤ N) :
    ∃ x : Fin N → S, Function.Injective x ∧
      1 ≤ unorderedPairProduct (fun i ↦ (x i : ℂ)) := by
  have hτ2 : transfiniteDiameter S ≤ finiteDiameter S 2 :=
    iInf_le (fun n : ℕ ↦ finiteDiameter S (n + 2)) 0
  have hSne : S.Nonempty := by
    have hd : 0 < finiteDiameter S 2 := zero_lt_one.trans_le (hτ.trans hτ2)
    obtain ⟨x, _⟩ := lt_iSup_iff.mp hd
    exact ⟨(x 0 : ℂ), (x 0).property⟩
  have hτN : transfiniteDiameter S ≤ finiteDiameter S N := by
    change (⨅ n : ℕ, finiteDiameter S (n + 2)) ≤ finiteDiameter S N
    simpa only [Nat.sub_add_cancel hN] using
      (iInf_le (fun n : ℕ ↦ finiteDiameter S (n + 2)) (N - 2))
  obtain ⟨x, hx⟩ := finiteDiameter_eq_max_of_compact hS hSne hN
  have hsep : 1 ≤ geometricMeanSeparation (fun i ↦ (x i : ℂ)) := by
    exact ENNReal.one_le_ofReal.mp (hx ▸ hτ.trans hτN)
  have hNR : (1 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hq : 0 < 2 / ((N : ℝ) * ((N : ℝ) - 1)) := by positivity
  have hprod : 1 ≤ unorderedPairProduct (fun i ↦ (x i : ℂ)) := by
    apply (Real.rpow_le_rpow_iff (by norm_num)
      (Finset.prod_nonneg (fun _ _ ↦ dist_nonneg)) hq).mp
    simpa only [Real.one_rpow, geometricMeanSeparation, unorderedPairProduct] using hsep
  refine ⟨x, ?_, hprod⟩
  have hp0 : unorderedPairProduct (fun i ↦ (x i : ℂ)) ≠ 0 :=
    (zero_lt_one.trans_le hprod).ne'
  have hp := Finset.prod_ne_zero_iff.mp hp0
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hdist := hp (i, j) (by simp [hlt])
    exact hdist (dist_eq_zero.mpr (congrArg Subtype.val hij))
  · have hdist := hp (j, i) (by simp [hgt])
    exact hdist (dist_eq_zero.mpr (congrArg Subtype.val hij.symm))

theorem sum_offDiag_log_dist_eq_twice_log_unorderedPairProduct {N : ℕ}
    (x : Fin N → ℂ) (hx : Function.Injective x) :
    (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, Real.log (dist (x p.1) (x p.2))) =
      2 * Real.log (unorderedPairProduct x) := by
  let I := (Finset.univ : Finset (Fin N × Fin N)).filter (fun p ↦ p.1 < p.2)
  let J := (Finset.univ : Finset (Fin N × Fin N)).filter (fun p ↦ p.2 < p.1)
  have hlog : Real.log (unorderedPairProduct x) =
      ∑ p ∈ I, Real.log (dist (x p.1) (x p.2)) := by
    apply Real.log_prod
    intro p hp
    apply dist_ne_zero.mpr
    intro heq
    exact (ne_of_lt (Finset.mem_filter.mp hp).2) (hx heq)
  have hdis : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact lt_asymm (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hOff : (Finset.univ : Finset (Fin N)).offDiag = I ∪ J := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_union,
      I, J, Finset.mem_filter]
    exact ne_iff_lt_or_gt
  have hJI : (∑ p ∈ J, Real.log (dist (x p.1) (x p.2))) =
      ∑ p ∈ I, Real.log (dist (x p.1) (x p.2)) := by
    apply Finset.sum_equiv (Equiv.prodComm (Fin N) (Fin N))
    · intro p
      simp [I, J]
    · intro p _
      simp [dist_comm]
  rw [hOff, Finset.sum_union hdis, hJI, ← hlog]
  ring

theorem exists_distinct_configuration_log_sum_nonneg {S : Set ℂ}
    (hS : IsCompact S) (hτ : 1 ≤ transfiniteDiameter S) {N : ℕ} (hN : 2 ≤ N) :
    ∃ x : Fin N → S, Function.Injective x ∧
      0 ≤ ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        Real.log (dist (x p.1 : ℂ) (x p.2 : ℂ)) := by
  obtain ⟨x, hx, hprod⟩ := exists_distinct_configuration_of_one_le_transfiniteDiameter hS hτ hN
  refine ⟨x, hx, ?_⟩
  have hx' : Function.Injective (fun i ↦ (x i : ℂ)) := Subtype.val_injective.comp hx
  rw [sum_offDiag_log_dist_eq_twice_log_unorderedPairProduct (fun i ↦ (x i : ℂ)) hx']
  exact mul_nonneg (by norm_num) (Real.log_nonneg hprod)

end Erdos1040
