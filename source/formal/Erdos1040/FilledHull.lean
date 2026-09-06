import Mathlib

/-!
An actual compact filled-hull witness in the complex plane. Its complement
is the component containing the whole exterior of a sufficiently large disk.
No measure or potential assumptions enter the construction.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Erdos1040

theorem isPreconnected_complex_norm_gt {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected {z : ℂ | R < ‖z‖} := by
  have hs : IsPreconnected (sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (by simp [Complex.rank_real_complex]) 0 1
  have hp : IsPreconnected (Ioi R ×ˢ sphere (0 : ℂ) 1) :=
    isPreconnected_Ioi.prod hs
  have hc : Continuous (fun p : ℝ × ℂ ↦ p.1 • p.2) := by fun_prop
  have he : (fun p : ℝ × ℂ ↦ p.1 • p.2) '' (Ioi R ×ˢ sphere (0 : ℂ) 1) =
      {z : ℂ | R < ‖z‖} := by
    apply Subset.antisymm
    · rintro z ⟨⟨r, w⟩, ⟨hr, hw⟩, rfl⟩
      have hr0 : 0 < r := lt_of_le_of_lt hR hr
      have hw1 : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
      simpa only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hw1, mul_one] using
        (show R < r from hr)
    · intro z hz
      have hz0 : 0 < ‖z‖ := lt_of_le_of_lt hR hz
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
      · simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hz0), inv_mul_cancel₀ hz0.ne']
      · simp only [smul_smul, mul_inv_cancel₀ hz0.ne', one_smul]
  rw [← he]
  exact hp.image _ hc.continuousOn

theorem frontier_connectedComponentIn_compl_subset {T : Set ℂ} (hT : IsClosed T)
    (x : ℂ) : frontier (connectedComponentIn Tᶜ x) ⊆ T := by
  intro z hz
  by_contra hzT
  have hO : IsOpen (connectedComponentIn Tᶜ x) := hT.isOpen_compl.connectedComponentIn
  have hN : connectedComponentIn Tᶜ z ∈ 𝓝 z :=
    connectedComponentIn_mem_nhds (hT.isOpen_compl.mem_nhds hzT)
  obtain ⟨w, hwz, hwx⟩ := mem_closure_iff_nhds.mp hz.1 _ hN
  have heq : connectedComponentIn Tᶜ x = connectedComponentIn Tᶜ z :=
    (connectedComponentIn_eq hwx).trans (connectedComponentIn_eq hwz).symm
  have hzO : z ∈ connectedComponentIn Tᶜ x := by
    rw [heq]
    exact mem_connectedComponentIn hzT
  exact hz.2 (hO.interior_eq.symm ▸ hzO)

theorem exists_compact_hull_with_connected_complement {T : Set ℂ}
    (hT : IsCompact T) (hne : T.Nonempty) :
    ∃ K : Set ℂ, IsCompact K ∧ K.Nonempty ∧ T ⊆ K ∧
      IsPreconnected Kᶜ ∧ frontier K ⊆ T := by
  obtain ⟨R, hR, hTR⟩ := hT.isBounded.exists_pos_norm_lt
  let x : ℂ := (R + 1 : ℝ)
  let O : Set ℂ := connectedComponentIn Tᶜ x
  have hx : R < ‖x‖ := by
    dsimp [x]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)]
    linarith
  have hextT : {z : ℂ | R < ‖z‖} ⊆ Tᶜ := by
    intro z hz hzT
    exact (not_lt_of_ge hz.le) (hTR z hzT)
  have hextO : {z : ℂ | R < ‖z‖} ⊆ O :=
    (isPreconnected_complex_norm_gt hR.le).subset_connectedComponentIn hx hextT
  have hO : IsOpen O := hT.isClosed.isOpen_compl.connectedComponentIn
  have hsub : Oᶜ ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    exact le_of_not_gt fun h ↦ hz (hextO h)
  have hTK : T ⊆ Oᶜ := by
    intro z hz hzO
    exact (connectedComponentIn_subset Tᶜ x hzO) hz
  refine ⟨Oᶜ, (isCompact_closedBall 0 R).of_isClosed_subset hO.isClosed_compl hsub,
    hne.mono hTK, hTK, ?_, ?_⟩
  · simpa only [compl_compl] using (isPreconnected_connectedComponentIn (F := Tᶜ) (x := x))
  · simpa only [frontier_compl] using frontier_connectedComponentIn_compl_subset hT.isClosed x

end Erdos1040
