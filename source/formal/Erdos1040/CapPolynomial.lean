import Mathlib

/-!
Polynomial separation of two bounded caps from the origin, by geometric-series
pole moving in the uniform closure of polynomial functions. No general Runge
or polynomial-approximation theorem is assumed.
-/

noncomputable section

open scoped BigOperators
open ContinuousMap Polynomial

namespace Erdos1040

/-- The two closed caps outside a horizontal strip in a closed disk. -/
def capSet (M a : ℝ) : Set ℂ := {z | ‖z‖ ≤ M ∧ a ≤ |z.im|}

theorem isCompact_capSet (M a : ℝ) : IsCompact (capSet M a) := by
  apply (isCompact_closedBall (0 : ℂ) M).of_isClosed_subset
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im.abs)
  · intro z hz
    simpa using hz.1

@[instance]
theorem capSet_compactSpace (M a : ℝ) : CompactSpace (capSet M a) :=
  isCompact_iff_compactSpace.mp (isCompact_capSet M a)

theorem cap_denominator_ne_zero {M a : ℝ} (ha : 0 < a)
    (b : ℝ) (z : capSet M a) : (b : ℂ) - z ≠ 0 := by
  intro h
  have heq : (b : ℂ) = (z : ℂ) := sub_eq_zero.mp h
  have him : (z : ℂ).im = 0 := by rw [← heq]; simp
  have := z.property.2
  rw [him, abs_zero] at this
  linarith

/-- The continuous resolvent with a real pole, restricted to the two caps. -/
def capResolvent (M a : ℝ) (ha : 0 < a) (b : ℝ) : C(capSet M a, ℂ) :=
  ⟨fun z ↦ ((b : ℂ) - z)⁻¹,
    (continuous_const.sub continuous_subtype_val).inv₀
      (cap_denominator_ne_zero ha b)⟩

/-- A closed subalgebra contains a geometric inverse whenever the ratio norm
is less than one and the proposed inverse satisfies the exact identity. -/
theorem closed_subalgebra_geometric_inverse_mem {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (A : Subalgebra ℂ C(K, ℂ))
    (hA : IsClosed (A : Set C(K, ℂ))) {f g : C(K, ℂ)}
    (hf : f ∈ A) (hn : ‖f‖ < 1) (hg : g * (1 - f) = 1) : g ∈ A := by
  have hs : (∑' n : ℕ, f ^ n) ∈ A := tsum_mem hA (fun n ↦ A.pow_mem hf n)
  have heq : g = ∑' n : ℕ, f ^ n := by
    calc
      g = g * 1 := (mul_one g).symm
      _ = g * ((1 - f) * ∑' n : ℕ, f ^ n) := by
        rw [mul_neg_geom_series f hn]
      _ = (g * (1 - f)) * ∑' n : ℕ, f ^ n := (mul_assoc _ _ _).symm
      _ = ∑' n : ℕ, f ^ n := by rw [hg, one_mul]
  rwa [heq]

/-- A sufficiently distant positive real pole has its resolvent in the
uniform closure of polynomial functions on the caps. -/
theorem capResolvent_far_mem {M a : ℝ} (ha : 0 < a) (hM : 0 < M)
    (B : ℝ) (hMB : M < B) :
    capResolvent M a ha B ∈ (polynomialFunctions (capSet M a)).topologicalClosure := by
  let A := (polynomialFunctions (capSet M a)).topologicalClosure
  let f := (Polynomial.C (B : ℂ)⁻¹ * X).toContinuousMapOn (capSet M a)
  let g := (B : ℂ) • capResolvent M a ha B
  have hB : 0 < B := hM.trans hMB
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hf : f ∈ A := by
    apply (polynomialFunctions (capSet M a)).le_topologicalClosure
    rw [← SetLike.mem_coe, polynomialFunctions_coe]
    exact ⟨Polynomial.C (B : ℂ)⁻¹ * X, rfl⟩
  have hn : ‖f‖ < 1 := by
    apply (ContinuousMap.norm_lt_iff f zero_lt_one).mpr
    intro z
    simp only [f, Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
      eval_mul, eval_C, eval_X]
    change ‖(B : ℂ)⁻¹ * (z : ℂ)‖ < 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    rw [mul_comm, ← div_eq_mul_inv, div_lt_one hB]
    exact z.property.1.trans_lt hMB
  have hg : g * (1 - f) = 1 := by
    ext z
    simp only [g, f, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, ContinuousMap.smul_apply, capResolvent,
      ContinuousMap.coe_mk, smul_eq_mul, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply, eval_mul, eval_C, eval_X]
    change (B : ℂ) * ((B : ℂ) - z)⁻¹ * (1 - (B : ℂ)⁻¹ * z) = 1
    field_simp [hBc, cap_denominator_ne_zero ha B z]
  have hgm : g ∈ A := closed_subalgebra_geometric_inverse_mem A
    (polynomialFunctions (capSet M a)).isClosed_topologicalClosure hf hn hg
  convert A.smul_mem hgm (B : ℂ)⁻¹ using 1
  ext z
  change ((B : ℂ) - z)⁻¹ = (B : ℂ)⁻¹ * ((B : ℂ) * ((B : ℂ) - z)⁻¹)
  simp [hBc]

/-- A real pole can move by any real step shorter than the strip half-width,
while its resolvent remains in the uniform polynomial closure. -/
theorem capResolvent_step_mem {M a : ℝ} (ha : 0 < a) (b h : ℝ)
    (hh : |h| < a)
    (hb : capResolvent M a ha b ∈ (polynomialFunctions (capSet M a)).topologicalClosure) :
    capResolvent M a ha (b - h) ∈ (polynomialFunctions (capSet M a)).topologicalClosure := by
  let A := (polynomialFunctions (capSet M a)).topologicalClosure
  let f := (h : ℂ) • capResolvent M a ha b
  let g := (Polynomial.C (b : ℂ) - X).toContinuousMapOn (capSet M a) *
    capResolvent M a ha (b - h)
  have hf : f ∈ A := A.smul_mem hb (h : ℂ)
  have hn : ‖f‖ < 1 := by
    apply (ContinuousMap.norm_lt_iff f zero_lt_one).mpr
    intro z
    have hd : a ≤ ‖(b : ℂ) - (z : ℂ)‖ := by
      have hi := Complex.abs_im_le_norm ((b : ℂ) - (z : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at hi
      exact z.property.2.trans hi
    change ‖(h : ℂ) * ((b : ℂ) - z)⁻¹‖ < 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      ← div_eq_mul_inv, div_lt_one (ha.trans_le hd)]
    exact hh.trans_le hd
  have hg : g * (1 - f) = 1 := by
    ext z
    simp only [g, f, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, ContinuousMap.smul_apply, capResolvent,
      ContinuousMap.coe_mk, smul_eq_mul, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply, eval_sub, eval_C, eval_X]
    change (((b : ℂ) - z) * (((b - h : ℝ) : ℂ) - z)⁻¹) *
      (1 - (h : ℂ) * ((b : ℂ) - z)⁻¹) = 1
    have hd := cap_denominator_ne_zero ha b z
    have he := cap_denominator_ne_zero ha (b - h) z
    push_cast at he ⊢
    field_simp [hd, he]
    ring
  have hgm : g ∈ A := closed_subalgebra_geometric_inverse_mem A
    (polynomialFunctions (capSet M a)).isClosed_topologicalClosure hf hn hg
  convert A.mul_mem hb hgm using 1
  ext z
  simp only [g, ContinuousMap.mul_apply, capResolvent, ContinuousMap.coe_mk,
    Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
    eval_sub, eval_C, eval_X]
  change (((b - h : ℝ) : ℂ) - z)⁻¹ =
    ((b : ℂ) - z)⁻¹ * (((b : ℂ) - z) * (((b - h : ℝ) : ℂ) - z)⁻¹)
  simp [cap_denominator_ne_zero ha b z]

/-- Finitely many equal real pole moves put the reciprocal with pole zero in
the uniform closure of polynomial functions on the caps. -/
theorem capResolvent_zero_mem {M a : ℝ} (ha : 0 < a) (hM : 0 < M) :
    capResolvent M a ha 0 ∈ (polynomialFunctions (capSet M a)).topologicalClosure := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * M / a)
  let h := a / 2
  let B := (N : ℝ) * h
  have hNa : 4 * M ≤ (N : ℝ) * a := (div_le_iff₀ ha).mp hN
  have hMB : M < B := by
    dsimp [B, h]
    nlinarith
  have hh : |h| < a := by
    dsimp [h]
    rw [abs_of_pos (by positivity : 0 < a / 2)]
    linarith
  have hall : ∀ n : ℕ, capResolvent M a ha (B - (n : ℝ) * h) ∈
      (polynomialFunctions (capSet M a)).topologicalClosure := by
    intro n
    induction n with
    | zero => simpa using capResolvent_far_mem ha hM B hMB
    | succ n ih =>
      have hs := capResolvent_step_mem ha (B - (n : ℝ) * h) h hh ih
      convert hs using 1
      congr 1
      push_cast
      ring
  simpa [B] using hall N

/-- Exact separator needed in the harmonic rotation construction: the value
at zero is one and the modulus is less than one quarter on both closed caps. -/
theorem exists_cap_polynomial {M a : ℝ} (ha : 0 < a) (haM : a < M) :
    ∃ Q : ℂ[X], Q.eval 0 = 1 ∧
      ∀ z : ℂ, ‖z‖ ≤ M → a ≤ |z.im| → ‖Q.eval z‖ < 1 / 4 := by
  have hM : 0 < M := ha.trans haM
  have hr := capResolvent_zero_mem ha hM
  change capResolvent M a ha 0 ∈
    closure (polynomialFunctions (capSet M a) : Set C(capSet M a, ℂ)) at hr
  obtain ⟨p, hp, hd⟩ := Metric.mem_closure_iff.mp hr (1 / (8 * M)) (by positivity)
  change p ∈ (polynomialFunctions (capSet M a) : Set C(capSet M a, ℂ)) at hp
  rw [polynomialFunctions_coe] at hp
  obtain ⟨P, rfl⟩ := hp
  rw [dist_comm, dist_eq_norm] at hd
  let Q : ℂ[X] := 1 + X * P
  refine ⟨Q, by simp [Q], ?_⟩
  intro z hzM hza
  let zz : capSet M a := ⟨z, hzM, hza⟩
  have hz0 : z ≠ 0 := by
    intro he
    simp only [he, Complex.zero_im, abs_zero] at hza
    linarith
  have hpz := (ContinuousMap.norm_coe_le_norm
    (P.toContinuousMapOn (capSet M a) - capResolvent M a ha 0) zz).trans_lt hd
  have hQ : Q.eval z = z *
      ((P.toContinuousMapOn (capSet M a) - capResolvent M a ha 0) zz) := by
    simp [Q, capResolvent, zz]
    field_simp [hz0]
    ring
  calc
    ‖Q.eval z‖ = ‖z‖ *
        ‖(P.toContinuousMapOn (capSet M a) - capResolvent M a ha 0) zz‖ := by
      rw [hQ, norm_mul]
    _ ≤ M * ‖(P.toContinuousMapOn (capSet M a) - capResolvent M a ha 0) zz‖ :=
      mul_le_mul_of_nonneg_right hzM (norm_nonneg _)
    _ < M * (1 / (8 * M)) := mul_lt_mul_of_pos_left hpz hM
    _ = 1 / 8 := by field_simp
    _ < 1 / 4 := by norm_num

end Erdos1040
