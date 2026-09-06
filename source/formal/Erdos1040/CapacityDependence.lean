import Erdos1040.CountableSources
import Erdos1040.GeometricScaling
import Erdos1040.AreaObstruction

/-!
The separate first question in Erdős--Herzog--Piranian (1958), Problem 4.
The minimum-area functional is an infimum over actual monic positive-degree
complex polynomials whose every root belongs to the original source. No
attainment is asserted. The explicit compact infinite witnesses have both
geometric transfinite diameter and logarithmic capacity zero, but separated
area infima. This records a known negative answer, not a novelty claim.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal

namespace Erdos1040

def minimalLemniscateArea (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ p : ℂ[X], ⨅ (_ : p.Monic), ⨅ (_ : 0 < p.natDegree),
    ⨅ (_ : ∀ z : ℂ, p.IsRoot z → z ∈ F), volume {z : ℂ | ‖p.eval z‖ < 1}

theorem minimalLemniscateArea_le_of_monic {F : Set ℂ} (p : ℂ[X]) (hp : p.Monic)
    (hn : 0 < p.natDegree) (hr : ∀ z : ℂ, p.IsRoot z → z ∈ F) :
    minimalLemniscateArea F ≤ volume {z : ℂ | ‖p.eval z‖ < 1} := by
  exact iInf_le_of_le p (iInf_le_of_le hp (iInf_le_of_le hn (iInf_le_of_le hr le_rfl)))

theorem smallCountableSource_minimalLemniscateArea_ge :
    ENNReal.ofReal (9 * Real.pi / 16) ≤ minimalLemniscateArea smallCountableSource := by
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  apply le_iInf
  intro hn
  apply le_iInf
  intro hr
  apply volume_monic_sublevel_ge_nine_pi_sixteenths p hp hn
  intro z hz
  simpa using smallCountableSource_subset_closedBall (hr z hz)

def largeCountableSource : Set ℂ :=
  insert (4 : ℂ) (insert (-4 : ℂ) smallCountableSource)

theorem largeCountableSource_countable : largeCountableSource.Countable :=
  (smallCountableSource_countable.insert (-4)).insert 4

theorem largeCountableSource_isCompact : IsCompact largeCountableSource :=
  (smallCountableSource_isCompact.insert (-4)).insert 4

theorem largeCountableSource_infinite : largeCountableSource.Infinite := by
  apply smallCountableSource_infinite.mono
  intro z hz
  exact Or.inr (Or.inr hz)

theorem largeCountableSource_minimalLemniscateArea_le :
    minimalLemniscateArea largeCountableSource ≤ ENNReal.ofReal (Real.pi / 8) := by
  obtain ⟨p, hp, hn, hr, harea⟩ := exists_plus_minus_four_monic_small_area
  apply le_trans (minimalLemniscateArea_le_of_monic p hp hn ?_) harea
  intro z hz
  rcases (hr z).mp hz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem capacity_only_dependence_counterexample :
    ∃ S T : Set ℂ, IsCompact S ∧ S.Infinite ∧ IsCompact T ∧ T.Infinite ∧
      transfiniteDiameter S = 0 ∧ transfiniteDiameter T = 0 ∧
      logarithmicCapacity S = 0 ∧ logarithmicCapacity T = 0 ∧
      minimalLemniscateArea T < minimalLemniscateArea S := by
  refine ⟨smallCountableSource, largeCountableSource,
    smallCountableSource_isCompact, smallCountableSource_infinite,
    largeCountableSource_isCompact, largeCountableSource_infinite,
    transfiniteDiameter_eq_zero_of_countable_compact smallCountableSource_isCompact
      smallCountableSource_countable,
    transfiniteDiameter_eq_zero_of_countable_compact largeCountableSource_isCompact
      largeCountableSource_countable,
    logarithmicCapacity_eq_zero_of_countable smallCountableSource_countable,
    logarithmicCapacity_eq_zero_of_countable largeCountableSource_countable, ?_⟩
  exact lt_of_le_of_lt largeCountableSource_minimalLemniscateArea_le
    (lt_of_lt_of_le plus_minus_four_area_bound_lt_ball_obstruction
      smallCountableSource_minimalLemniscateArea_ge)

theorem minimalLemniscateArea_not_determined_by_transfiniteDiameter :
    ¬ ∃ f : ℝ≥0∞ → ℝ≥0∞, ∀ F : Set ℂ, IsClosed F → F.Infinite →
      minimalLemniscateArea F = f (transfiniteDiameter F) := by
  rintro ⟨f, hf⟩
  obtain ⟨S, T, hS, hSi, hT, hTi, hSd, hTd, _, _, harea⟩ :=
    capacity_only_dependence_counterexample
  rw [hf T hT.isClosed hTi, hf S hS.isClosed hSi, hSd, hTd] at harea
  exact lt_irrefl _ harea

theorem minimalLemniscateArea_not_determined_by_logarithmicCapacity :
    ¬ ∃ f : ℝ≥0∞ → ℝ≥0∞, ∀ F : Set ℂ, IsCompact F → F.Infinite →
      minimalLemniscateArea F = f (logarithmicCapacity F) := by
  rintro ⟨f, hf⟩
  obtain ⟨S, T, hS, hSi, hT, hTi, _, _, hSc, hTc, harea⟩ :=
    capacity_only_dependence_counterexample
  rw [hf T hT hTi, hf S hS hSi, hSc, hTc] at harea
  exact lt_irrefl _ harea

end Erdos1040
