import Erdos1040.SourceSupport
import Erdos1040.PotentialAsymptotics
import Erdos1040.HarmonicMaximum

/-!
Actual compact-source probability potentials grow to positive infinity.
Global nonnegativity and the proved harmonic maximum principle make them
strictly positive on a compact hull's connected exterior.
-/

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

namespace Erdos1040

theorem tendsto_log_source_potential_atTop {S : Set ℂ} (hS : IsCompact S)
    (μ : ProbabilityMeasure S) :
    Tendsto (fun z : ℂ ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ)
      (cocompact ℂ) atTop := by
  have he : Tendsto (fun z : ℂ ↦ (∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) -
      Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
    simpa using tendsto_log_density_potential_sub_mass_log hS (μ : Measure S)
      (fun _ ↦ (1 : ℝ)) (integrable_const 1)
  have hl : Tendsto (fun z : ℂ ↦ Real.log ‖z‖) (cocompact ℂ) atTop :=
    Real.tendsto_log_atTop.comp tendsto_norm_cocompact_atTop
  simpa only [sub_add_cancel] using he.add_atTop hl

theorem log_source_potential_pos_on_hull_compl {S K : Set ℂ}
    (hS : IsCompact S) (hK : IsCompact K) (μ : ProbabilityMeasure S)
    (hTK : sourceSupport μ ⊆ K) (hconn : IsPreconnected Kᶜ)
    (hnonneg : ∀ z : ℂ, 0 ≤ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ) :
    ∀ z ∉ K, 0 < ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ := by
  let U : ℂ → ℝ := fun z ↦ ∫ w : S, Real.log ‖z - (w : ℂ)‖ ∂μ
  have hh : HarmonicOnNhd U Kᶜ :=
    (harmonicOnNhd_source_potential_compl_support hS μ).mono
      (Set.compl_subset_compl.mpr hTK)
  intro z hz
  by_contra hpos
  have hz0 : U z = 0 := le_antisymm (le_of_not_gt hpos) (hnonneg z)
  have hmax : IsMaxOn (fun w ↦ -U w) Kᶜ z := by
    intro w hw
    have hw0 := hnonneg w
    change -U w ≤ -U z
    rw [hz0]
    simpa only [neg_zero] using neg_nonpos.mpr hw0
  have hc := harmonic_eqOn_of_isPreconnected_of_isMaxOn hconn hK.isClosed.isOpen_compl
    hh.neg hz hmax
  have hKevent : ∀ᶠ w : ℂ in cocompact ℂ, w ∉ K := hK.compl_mem_cocompact
  obtain ⟨w, hwK, hwU⟩ := (hKevent.and
    ((tendsto_log_source_potential_atTop hS μ).eventually_gt_atTop 0)).exists
  have hcw := hc hwK
  change -U w = -U z at hcw
  rw [hz0] at hcw
  change 0 < U w at hwU
  linarith

end Erdos1040
