# AreaObstruction independent correspondence review

Reviewer: `formalization_preflight` (separate agent from the author of AreaObstruction).
Reviewed at: 2026-09-05T19:06:35.330335+00:00.

Verdict: **PASS** for the eight installed theorems in `Erdos1040.AreaObstruction` at the source and signature versions recorded below. No mathematical or informal-to-formal correspondence defect was found in this bounded review.

This agent authored the separate CountableSources draft and deliberately did not review that module. This is an agent review on the same host, not external human peer review. No proof, manifest, canonical research record, or trusted index was edited during this review.

## Machine evidence and version

- Source: `formal/Erdos1040/AreaObstruction.lean`.
- Source SHA-256: `fde0f797bd6473a57a81e310fa251e32c1dd702f0aca1ee612505cdaccf15836`.
- Machine report: `formal/.audit/report.json`, checked at `2026-09-05T19:03:17.475803+00:00`.
- Machine report SHA-256: `e0d517065c7f077bba2633e9eb12d46cb23ece2e62acef4f1dca3c41da3bda1b`.
- The report has `machine_checks_pass: true`, `source_scan_pass: true`, no errors, build exit code 0, audit exit code 0, and 271 tracked declarations.
- Every reviewed theorem has `axiom_audit_pass: true`; the only foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Lean is pinned to `leanprover/lean4:v4.33.1` and Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`.
- The report still has `main_target_complete: false` and 31 unreviewed declarations because the new correspondence bindings have not yet been attached. This review supplies only the eight AreaObstruction bindings; integration, the final required checker run, and admission remain the root agent responsibility.

The earlier failed inventory detected `normHom.congr_simp`. The author replaced only the local norm-product proof with a direct multiset induction. I read the final proof: its empty case is the norm of one, and its cons case uses norm multiplication and the induction hypothesis. All eight intended statements and printed signature hashes remain unchanged. The fresh passing report is the version used here.

## Scope and mathematical review

The ball argument works for every positive degree, with repeated roots allowed. The inequality is strict inside the open observation ball because each factor is at most norm(z)+1/4 < 1; positive degree is essential and retained. The arbitrary-polynomial form uses the actual complex polynomial, its full root multiset and monicity, so it covers every permitted polynomial.

The canonical complex volume is planar Lebesgue area. The ball calculation is pi*(3/4)^2 = 9*pi/16. Roots +4 and -4 have separation 8, and the admitted quadratic bound is 8*pi/8^2 = pi/8. Their strict numerical separation is correctly transported to ENNReal through positive ofReal inputs.

These eight theorems establish area bounds and an explicit polynomial. They do not themselves establish countability, compactness, capacity zero, transfinite diameter zero, or the complete counterexample involving an infimum over all polynomials. Those are separate declarations reviewed elsewhere. No positive-capacity example, general capacity/diameter equivalence, quantitative algorithm, novelty claim, or P versus NP consequence is asserted. The earlier external crosscheck of the original 240 declarations is not presented as an external check of these new declarations.

## Exact declarations and correspondence

### `Erdos1040.ball_three_quarters_subset_unitLemniscate`

For any positive number n and any complex root list indexed by Fin n, if every root has norm at most 1/4 then the strict unit lemniscate contains the open ball of radius 3/4 centered at zero.

```lean
theorem Erdos1040.ball_three_quarters_subset_unitLemniscate : ∀ {n : ℕ},
  LT.lt.{0} 0 n →
    ∀ (roots : Fin n → ℂ),
      (∀ (i : Fin n), LE.le.{0} (Norm.norm.{0} (roots i)) (1 / 4)) →
        Metric.ball.{0} 0 (3 / 4) ⊆ Erdos1040.unitLemniscate roots
```

The signature quantifies over every natural n with 0 < n and every Fin n complex root list, including multiplicities. Each norm(z-root) is bounded by norm(z)+1/4 < 1 on the open ball, and the strictly positive exponent keeps the product strictly below one. The conclusion is literal inclusion in the already defined strict unitLemniscate; no boundary inclusion or degree-zero case is claimed.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `846051bb46a52bb96da95629e971c026dc6ff0c3372991ed03815696d1fe2c49`.
- Source-statement UTF-8 SHA-256: `71f338669bd030920fccf8be73001c63d91869d8e031a327e3b8d1651be1314d`.

### `Erdos1040.volume_ball_three_quarters`

The planar Lebesgue measure of the open complex ball centered at zero with radius 3/4 equals ENNReal.ofReal (9*pi/16).

```lean
theorem Erdos1040.volume_ball_three_quarters : Eq.{1}
  (MeasureTheory.MeasureSpace.volume.{0} (Metric.ball.{0} 0 (3 / 4)))
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
```

The signature uses the canonical planar Lebesgue volume on the complex plane and the open ball centered at zero. The checked Complex.volume_ball formula gives pi*(3/4)^2 = 9*pi/16; conversion to ENNReal.ofReal preserves this positive finite number. No normalization by pi or real-line measure is substituted.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `ebe8cf29179597b3b17dcc6e9b627818a17dca3102ff4e7ce8a2d57130480be1`.
- Source-statement UTF-8 SHA-256: `e067e6d90161ece47af7812709837655a2df26e8bdd1c7dda53bf48eee979825`.

### `Erdos1040.volume_unitLemniscate_ge_nine_pi_sixteenths`

For any positive finite root list whose roots have norm at most 1/4, the planar Lebesgue measure of its strict unit lemniscate is at least ENNReal.ofReal (9*pi/16).

```lean
theorem Erdos1040.volume_unitLemniscate_ge_nine_pi_sixteenths : ∀ {n : ℕ},
  LT.lt.{0} 0 n →
    ∀ (roots : Fin n → ℂ),
      (∀ (i : Fin n), LE.le.{0} (Norm.norm.{0} (roots i)) (1 / 4)) →
        LE.le.{0} (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
          (MeasureTheory.MeasureSpace.volume.{0} (Erdos1040.unitLemniscate roots))
```

Every positive Fin n root list is quantified, every root has the stated non-strict norm bound 1/4, and the volume is that of the strict unit sublevel. Measure monotonicity and the exact open-ball volume yield the lower bound 9*pi/16. There is no compactness, root distinctness, source regularity, or attainment hypothesis.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `a88e711c01edeb6db53202275037c26e281cc499636f0b002ef315d4be6970cd`.
- Source-statement UTF-8 SHA-256: `64eba2e6a6e7bc6ba01159c744819bc5880c3eb5ce296aaf53d354f67d9323e8`.

### `Erdos1040.ball_three_quarters_subset_monic_sublevel`

For every monic complex polynomial of positive natural degree whose every complex root has norm at most 1/4, its strict unit sublevel contains the open ball centered at zero of radius 3/4.

```lean
theorem Erdos1040.ball_three_quarters_subset_monic_sublevel : ∀ (p : Polynomial.{0} ℂ),
  Polynomial.Monic.{0} p →
    LT.lt.{0} 0 (Polynomial.natDegree.{0} p) →
      (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → LE.le.{0} (Norm.norm.{0} z) (1 / 4)) →
        Metric.ball.{0} 0 (3 / 4) ⊆ Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1
```

The signature quantifies over every actual complex polynomial with monicity, positive natural degree, and the stated norm bound on every complex root. Algebraic closedness of the actual coefficient field supplies splitting, the roots multiset retains multiplicities, and monicity removes the leading coefficient. The repaired local norm-product induction proves the same norm identity without changing any hypothesis or conclusion. Thus the open ball lies in the literal strict unit polynomial sublevel.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `8347df3b8be17a3f20def3fb17a54c3293a96433b4b0e907ae62c96c316c4a25`.
- Source-statement UTF-8 SHA-256: `da4b7bcf2bed9cc84155c4ca5c4b952c3ca1eed352c642c62688fe255a0fb582`.

### `Erdos1040.volume_monic_sublevel_ge_nine_pi_sixteenths`

For every monic complex polynomial of positive natural degree whose every complex root has norm at most 1/4, its strict unit sublevel has planar Lebesgue measure at least ENNReal.ofReal (9*pi/16).

```lean
theorem Erdos1040.volume_monic_sublevel_ge_nine_pi_sixteenths : ∀ (p : Polynomial.{0} ℂ),
  Polynomial.Monic.{0} p →
    LT.lt.{0} 0 (Polynomial.natDegree.{0} p) →
      (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → LE.le.{0} (Norm.norm.{0} z) (1 / 4)) →
        LE.le.{0} (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
          (MeasureTheory.MeasureSpace.volume.{0}
            (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
```

The full polynomial domain, monicity, positive natural degree, and universal actual-root bound match the source statement exactly. Inclusion of the open radius-3/4 ball and measure monotonicity prove the planar lower bound for every eligible polynomial, not merely products selected by the construction. The zero and constant polynomials are excluded by the displayed hypotheses.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `fcb29926a2507613c0b701def2372c18adb8ed34e16ce354ed3f701c21a2155f`.
- Source-statement UTF-8 SHA-256: `37e94d291cc7c3d93c571bd38dd60fa1f72ed0fd8a59beca91d20e0b0808ac25`.

### `Erdos1040.volume_plus_minus_four_quadratic_le`

The strict unit sublevel of the explicit complex function (z-4)*(z-(-4)) has planar Lebesgue measure at most ENNReal.ofReal (pi/8).

```lean
theorem Erdos1040.volume_plus_minus_four_quadratic_le : LE.le.{0}
  (MeasureTheory.MeasureSpace.volume.{0}
    (Set.ofPred.{0} fun z =>
      LT.lt.{0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} z 4) (HSub.hSub.{0, 0, 0} z (-4)))) 1))
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} Real.pi 8))
```

The literal complex function is (z-4)*(z-(-4)), with a strict norm sublevel. The admitted quadratic estimate uses distinct roots at separation 8, so 8*pi/8^2 is exactly pi/8. The result is an upper bound, not an asserted exact area or infimum value.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `8ff371878762a779c4270899045544c63eb2aa57a08c09a68fd04513e30a404f`.
- Source-statement UTF-8 SHA-256: `44c9a07a1f2ef549e818a87de4f5a1e485b5897e01c86f3f9192349a3069126f`.

### `Erdos1040.exists_plus_minus_four_monic_small_area`

There exists a monic complex polynomial of positive natural degree whose complex roots are exactly 4 and -4 and whose strict unit sublevel has planar Lebesgue measure at most ENNReal.ofReal (pi/8).

```lean
theorem Erdos1040.exists_plus_minus_four_monic_small_area : ∃ p,
  Polynomial.Monic.{0} p ∧
    LT.lt.{0} 0 (Polynomial.natDegree.{0} p) ∧
      (∀ (z : ℂ), Polynomial.IsRoot.{0} p z ↔ Eq.{1} z 4 ∨ Eq.{1} z (-4)) ∧
        LE.le.{0}
          (MeasureTheory.MeasureSpace.volume.{0}
            (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
          (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} Real.pi 8))
```

The proof constructs rootPolynomial of the two-entry list [4,-4]. Admitted product facts give monicity, positive degree, the bidirectional actual-root characterization for all complex z, and exact evaluation. The signature requires roots exactly at plus/minus four, retains the strict unit sublevel, and concludes the stated non-strict area upper bound. It does not assert minimality or a degree bound for other polynomials.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `4180164c10918d2db19e688dcbe5d59c67d99ae22ffeeb6d6688a011ca2244cd`.
- Source-statement UTF-8 SHA-256: `bf22a1e655f144969c924e1b317d5413545775710be9dcb04ad2339c3b7336e7`.

### `Erdos1040.plus_minus_four_area_bound_lt_ball_obstruction`

ENNReal.ofReal (pi/8) is strictly less than ENNReal.ofReal (9*pi/16).

```lean
theorem Erdos1040.plus_minus_four_area_bound_lt_ball_obstruction : LT.lt.{0}
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} Real.pi 8))
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
```

The signature is the exact strict ENNReal comparison of ofReal(pi/8) and ofReal(9*pi/16). Real.pi_pos makes both quantities positive and proves strict separation; ENNReal.ofReal does not collapse either term to zero.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found.

- Signature UTF-8 SHA-256: `5427060aebb44c95211fb047e67786e27967c162862dd254d2d7240c20252a0f`.
- Source-statement UTF-8 SHA-256: `c5f33e6f919f971b935f08a5e77c92ce16b9eeb1fde8195e8df5e8e7545ffb83`.

## Inspected supporting source bytes

The proof review used the following actual local source files. The full dependency, build and axiom audit remains the separate machine report; these selected reads are not described as a second independent kernel execution.

| File | SHA-256 | Extent |
| --- | --- | --- |
| `formal/Erdos1040/Basic.lean` | `8ad9a2349f6cc49d3042bcb01c67bc63c09286655df5d48bb2afa028cbbc3dc7` | Full exact root-polynomial and unit-lemniscate definitions and lemmas |
| `formal/Erdos1040/Unbounded.lean` | `805c0dd336dee7456891b029688d5e332f2138a799c62a34d0956e93321c9156` | Full quadratic inclusion/area bound and existing unbounded branch |
| `formal/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean` | `c3510458d0561b9f8e9166dab50e88c1cce6adb1ca3a1bdec7934a877a80d61d` | Complex.volume_ball section |
| `formal/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Splits.lean` | `53f65488639f9933b5f4994ea5d0d91d5d0159f36db0bb1fc4f5f95e7ed8e554` | Monic root factorization/evaluation and degree/root-cardinality APIs |
| `formal/.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Multiset.lean` | `a9d0db842689f4f9d11c50f86227fe216c5e5a9244f02d65d1a760c276a5d199` | prod_map_le_prod_map0 statement and proof |
| `formal/.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean` | `6006dca22dde49b3525d2d701e37ba93671e6ab1d47649a77f66fea36a1ff6c8` | pow_lt_one0 statement and proof |

The companion `formalization-preflight-area-obstruction-bindings.json` is a declaration-name mapping with the exact source-byte hash, printed-signature UTF-8 hash, source-statement UTF-8 hash, reviewer and individual review notes expected by the manifest integrator.
