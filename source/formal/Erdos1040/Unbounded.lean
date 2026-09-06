import Erdos1040.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

open MeasureTheory

namespace Erdos1040

/-- The unit lemniscate of a quadratic with distinct roots lies in two small disks. -/
theorem quadratic_sublevel_subset_balls (a b : ℂ) (hab : a ≠ b) :
    {z : ℂ | ‖(z - a) * (z - b)‖ < 1} ⊆
      Metric.ball a (2 / ‖a - b‖) ∪ Metric.ball b (2 / ‖a - b‖) := by
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  intro z hz
  change ‖(z - a) * (z - b)‖ < 1 at hz
  rw [norm_mul] at hz
  have hx : 0 ≤ ‖z - a‖ := norm_nonneg _
  have hy : 0 ≤ ‖z - b‖ := norm_nonneg _
  have htriangle : ‖a - b‖ ≤ ‖z - a‖ + ‖z - b‖ := by
    simpa only [norm_sub_rev a z] using norm_sub_le_norm_sub_add_norm_sub a z b
  rcases le_total ‖z - a‖ ‖z - b‖ with hxy | hyx
  · left
    rw [Metric.mem_ball, dist_eq_norm]
    apply (lt_div_iff₀ hD).2
    have hlarge : ‖a - b‖ ≤ 2 * ‖z - b‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hlarge hx
    nlinarith
  · right
    rw [Metric.mem_ball, dist_eq_norm]
    apply (lt_div_iff₀ hD).2
    have hlarge : ‖a - b‖ ≤ 2 * ‖z - a‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hlarge hy
    nlinarith

/-- Planar area is at most `8π` divided by the square of the root separation. -/
theorem volume_quadratic_sublevel_le (a b : ℂ) (hab : a ≠ b) :
    volume {z : ℂ | ‖(z - a) * (z - b)‖ < 1} ≤
      ENNReal.ofReal (8 * Real.pi / ‖a - b‖ ^ 2) := by
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hr : 0 ≤ 2 / ‖a - b‖ := by positivity
  have harea : 0 ≤ (2 / ‖a - b‖) ^ 2 * Real.pi := by positivity
  have hball (c : ℂ) : volume (Metric.ball c (2 / ‖a - b‖)) =
      ENNReal.ofReal ((2 / ‖a - b‖) ^ 2 * Real.pi) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_pow hr]
    congr 1
    simpa only [NNReal.coe_real_pi] using
      (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm
  calc
    volume {z : ℂ | ‖(z - a) * (z - b)‖ < 1} ≤
        volume (Metric.ball a (2 / ‖a - b‖) ∪ Metric.ball b (2 / ‖a - b‖)) :=
      measure_mono (quadratic_sublevel_subset_balls a b hab)
    _ ≤ volume (Metric.ball a (2 / ‖a - b‖)) +
        volume (Metric.ball b (2 / ‖a - b‖)) := measure_union_le _ _
    _ = ENNReal.ofReal (8 * Real.pi / ‖a - b‖ ^ 2) := by
      rw [hball a, hball b, ← ENNReal.ofReal_add harea harea]
      congr 1
      field_simp
      <;> ring

/-- An unbounded root set supplies a quadratic of arbitrarily small unit-lemniscate area. -/
theorem unbounded_exists_quadratic_small_area (F : Set ℂ)
    (hF : ¬ Bornology.IsBounded F) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧
      volume {z : ℂ | ‖(z - a) * (z - b)‖ < 1} < ENNReal.ofReal ε := by
  obtain ⟨a, ha⟩ := Bornology.nonempty_of_not_isBounded hF
  have hfar : ∃ b ∈ F, max 1 (8 * Real.pi / ε) < dist b a := by
    by_contra! h
    apply hF
    exact (Metric.isBounded_iff_subset_closedBall a).2
      ⟨max 1 (8 * Real.pi / ε), fun b hb => h b hb⟩
  obtain ⟨b, hb, hdist⟩ := hfar
  have hnorm : max 1 (8 * Real.pi / ε) < ‖a - b‖ := by
    simpa only [dist_eq_norm, norm_sub_rev b a] using hdist
  have hD1 : 1 < ‖a - b‖ := lt_of_le_of_lt (le_max_left _ _) hnorm
  have hD : 0 < ‖a - b‖ := lt_trans zero_lt_one hD1
  have hab : a ≠ b := sub_ne_zero.mp (norm_pos_iff.mp hD)
  have hlarge : 8 * Real.pi / ε < ‖a - b‖ :=
    lt_of_le_of_lt (le_max_right _ _) hnorm
  have hnum : 8 * Real.pi < ‖a - b‖ * ε := (div_lt_iff₀ hε).1 hlarge
  have hsquare : ‖a - b‖ < ‖a - b‖ ^ 2 := by nlinarith
  have hbound : 8 * Real.pi / ‖a - b‖ ^ 2 < ε := by
    apply (div_lt_iff₀ (pow_pos hD 2)).2
    have hmul := mul_lt_mul_of_pos_left hsquare hε
    nlinarith
  refine ⟨a, ha, b, hb, hab, ?_⟩
  exact lt_of_le_of_lt (volume_quadratic_sublevel_le a b hab)
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 hbound)

/-- The unbounded branch of the full Erdős #1040 implication. -/
theorem unbounded_hasArbitrarilySmallLemniscates {F : Set ℂ}
    (hF : ¬ Bornology.IsBounded F) : HasArbitrarilySmallLemniscates F := by
  intro ε hε
  obtain ⟨a, ha, b, hb, _hab, harea⟩ :=
    unbounded_exists_quadratic_small_area F hF ε hε
  refine ⟨2, by decide, ![a, b], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ha, hb]
  · simpa [unitLemniscate, Fin.prod_univ_two] using harea

end Erdos1040
