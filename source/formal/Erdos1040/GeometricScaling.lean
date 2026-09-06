import Erdos1040.GeometricDiameter
import Erdos1040.EnergyDiameter
import Erdos1040.LogarithmicCapacity
import Erdos1040.LogEnergyIntegrability

noncomputable section
open scoped ENNReal BigOperators
namespace Erdos1040

theorem geometricMeanSeparation_dilate {N : ℕ} (hN : 2 ≤ N)
    (x : Fin N → ℂ) {c : ℝ} (hc : 0 < c) :
    geometricMeanSeparation (fun i ↦ (c : ℂ) * x i) =
      c * geometricMeanSeparation x := by
  have hd (i j : Fin N) : dist ((c : ℂ) * x i) ((c : ℂ) * x j) =
      c * dist (x i) (x j) := by
    rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, dist_eq_norm]
  have hcard : ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p ↦ p.1 < p.2)).card = N.choose 2 := by
    simpa using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))
  have hp : unorderedPairProduct (fun i ↦ (c : ℂ) * x i) =
      c ^ (N.choose 2) * unorderedPairProduct x := by
    simp only [unorderedPairProduct, hd, Finset.prod_mul_distrib,
      Finset.prod_const, hcard]
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hden : (N : ℝ) * ((N : ℝ) - 1) ≠ 0 := by positivity
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have he : (N.choose 2 : ℝ) * (2 / ((N : ℝ) * ((N : ℝ) - 1))) = 1 := by
    rw [Nat.cast_choose_two]
    field_simp [hn1]
  have hpnonneg : 0 ≤ unorderedPairProduct x :=
    Finset.prod_nonneg (fun _ _ ↦ dist_nonneg)
  rw [geometricMeanSeparation, hp,
    Real.mul_rpow (by positivity) hpnonneg,
    ← Real.rpow_natCast_mul hc.le, he, Real.rpow_one]
  rfl

theorem finiteDiameter_dilate (S : Set ℂ) {N : ℕ} (hN : 2 ≤ N)
    {c : ℝ} (hc : 0 < c) :
    finiteDiameter ((fun z : ℂ ↦ (c : ℂ) * z) '' S) N =
      ENNReal.ofReal c * finiteDiameter S N := by
  classical
  unfold finiteDiameter
  rw [ENNReal.mul_iSup]
  apply le_antisymm
  · apply iSup_le
    intro y
    choose x hxS hxy using fun i ↦ (y i).property
    let a : Fin N → S := fun i ↦ ⟨x i, hxS i⟩
    have heq : (fun i ↦ (y i : ℂ)) = fun i ↦ (c : ℂ) * (a i : ℂ) := by
      funext i
      exact (hxy i).symm
    rw [heq, geometricMeanSeparation_dilate hN _ hc, ENNReal.ofReal_mul hc.le]
    exact le_iSup (fun a : Fin N → S ↦ ENNReal.ofReal c *
      ENNReal.ofReal (geometricMeanSeparation (fun i ↦ (a i : ℂ)))) a
  · apply iSup_le
    intro x
    let y : Fin N → ((fun z : ℂ ↦ (c : ℂ) * z) '' S) :=
      fun i ↦ ⟨(c : ℂ) * (x i : ℂ), Set.mem_image_of_mem _ (x i).property⟩
    have h := le_iSup (fun a : Fin N → ((fun z : ℂ ↦ (c : ℂ) * z) '' S) ↦
      ENNReal.ofReal (geometricMeanSeparation (fun i ↦ (a i : ℂ)))) y
    simpa only [y, geometricMeanSeparation_dilate hN _ hc,
      ENNReal.ofReal_mul hc.le] using h

theorem transfiniteDiameter_dilate (S : Set ℂ) {c : ℝ} (hc : 0 < c) :
    transfiniteDiameter ((fun z : ℂ ↦ (c : ℂ) * z) '' S) =
      ENNReal.ofReal c * transfiniteDiameter S := by
  unfold transfiniteDiameter
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top]
  apply iInf_congr
  intro n
  exact finiteDiameter_dilate S (by omega) hc

theorem transfiniteDiameter_eq_zero_of_countable_compact {S : Set ℂ}
    (hS : IsCompact S) (hcount : S.Countable) : transfiniteDiameter S = 0 := by
  have hfinite : transfiniteDiameter S ≠ ⊤ := ne_top_of_le_ne_top
    (finiteDiameter_lt_top_of_compact hS (by decide : 2 ≤ 2)).ne
    (iInf_le (fun n : ℕ ↦ finiteDiameter S (n + 2)) 0)
  by_contra hzero
  have hpos : 0 < (transfiniteDiameter S).toReal :=
    ENNReal.toReal_pos hzero hfinite
  let c : ℝ := (transfiniteDiameter S).toReal⁻¹
  have hc : 0 < c := inv_pos.mpr hpos
  let T : Set ℂ := (fun z : ℂ ↦ (c : ℂ) * z) '' S
  have hT : IsCompact T := hS.image (continuous_const.mul continuous_id)
  have hTcount : T.Countable := hcount.image _
  have hdiam : transfiniteDiameter T = 1 := by
    rw [transfiniteDiameter_dilate S hc]
    simp only [c, ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_toReal hfinite]
    exact ENNReal.inv_mul_cancel hzero hfinite
  obtain ⟨μ, hμ⟩ := exists_probability_energy_le_log_of_one_le_transfiniteDiameter
    hT hdiam.ge (one_le_logarithmicCapacityScale T)
    (fun _ hz _ hw ↦ dist_le_logarithmicCapacityScale hT hz hw)
  let : Countable T := hTcount.to_subtype
  let : MeasureTheory.NullSingletonClass (μ : MeasureTheory.Measure T) :=
    nullSingletonClass_of_finite_nonnegativeLogEnergy
      (lt_of_lt_of_le zero_lt_one (one_le_logarithmicCapacityScale T)) μ
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμ)
  have hm := (Set.countable_univ : (Set.univ : Set T).Countable).measure_zero
    (μ : MeasureTheory.Measure T)
  simp at hm

end Erdos1040
