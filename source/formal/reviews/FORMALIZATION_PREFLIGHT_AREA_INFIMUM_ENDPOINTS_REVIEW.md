# AreaInfimumEndpoints independent correspondence review

Reviewer: `formalization_preflight`, independently reviewing the root-authored endpoint module.
Reviewed at: 2026-09-05T19:12:09.806467+00:00.

Verdict: **PASS** for all three installed declarations in `Erdos1040.AreaInfimumEndpoints` at the exact versions below. The two unconditional endpoints explicitly close the original vanishing-infimum wording by using the previously established positive-tolerance polynomial statements.

## Machine evidence and version

- Source: `formal/Erdos1040/AreaInfimumEndpoints.lean`.
- Source SHA-256: `a5e1c815c673d8d37a609c5348d2c9c9ccfdecc4be4ed62ee216358c224b57ce`.
- Report: `formal/.audit/report.json`, checked at `2026-09-05T19:09:02.564332+00:00`.
- Report SHA-256: `7428c7c7c17b7f331fec33c19e66943c271fe0298e3b7ad4ab08f58027e04e90`.
- The report has 274 tracked declarations, `machine_checks_pass: true`, `source_scan_pass: true`, no errors, build exit code 0, and audit exit code 0.
- All three reviewed declarations pass the reported axiom audit and use only `propext`, `Classical.choice`, and `Quot.sound`.
- Pinned toolchain: `leanprover/lean4:v4.33.1`; pinned Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- At this snapshot, `main_target_complete: false` and 34 declarations await attached correspondence records. This review provides only the three endpoint records. Attaching all records, rerunning the required full checker, and admitting the final version remain the root agent responsibility.

This review did not run a separate Lean build or external proof checker. It combines independent source-and-signature correspondence review with the separately produced passing machine report. The original 240-declaration external crosscheck does not extend automatically to these new declarations. This is same-host agent review, not external human peer review. No proof source, manifest, canonical research record or trusted index was edited. The reviewer authored CountableSources and did not review that module.

## The exact area functional

The inspected definition in `CapacityDependence.lean` is an ENNReal infimum over actual complex polynomials, followed by proof-indexed infima enforcing monicity, positive natural degree, and membership in the original source for every actual complex root. The measured set is the strict norm sublevel `norm(p.eval z) < 1`, and the measure is the canonical complex planar Lebesgue volume. It is not an infimum over an arbitrarily selected subfamily of root lists. No least-area polynomial or attainment is part of the definition or the reviewed conclusions.

The conditional conversion does not smuggle in the threshold result: it explicitly assumes the positive-tolerance polynomial statement as its source statement requires. Each endpoint then discharges that assumption with an existing theorem. The ENNReal interpolation lemma handles a positive infinite candidate infimum as well as finite positive values; the argument has no unmentioned finiteness assumption.

The geometric endpoint retains closedness and infinitude and uses the actual geometric diameter. The capacity endpoint retains compactness and explicitly uses the actual Robin-energy capacity at least one. Thus the capacity-one specialization follows without changing the functional or the eligible polynomial class. No general capacity/transfinite-diameter identity, quantitative degree or runtime conclusion, novelty claim, or P versus NP implication is asserted.

## Exact declarations and review

### `Erdos1040.minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials`

Claim ID: `E1040-FULL`; role: `supporting`.

For every complex source F, if for every positive real epsilon there is an actual monic positive-degree complex polynomial with every root in F and strict unit-sublevel planar area below epsilon, then the exact area infimum minimalLemniscateArea F is zero. This is an explicitly conditional conversion lemma, not an assumed threshold result.

```lean
theorem Erdos1040.minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials : ∀ {F : Set.{0} ℂ},
  (∀ (ε : ℝ),
      LT.lt.{0} 0 ε →
        ∃ p,
          Polynomial.Monic.{0} p ∧
            LT.lt.{0} 0 (Polynomial.natDegree.{0} p) ∧
              (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → Membership.mem.{0, 0} F z) ∧
                LT.lt.{0}
                  (MeasureTheory.MeasureSpace.volume.{0}
                    (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
                  (ENNReal.ofReal ε)) →
    Eq.{1} (Erdos1040.minimalLemniscateArea F) 0
```

The source and exact signature quantify over every complex source F and explicitly assume every positive real tolerance has an actual monic complex polynomial of positive natural degree, every root in F, and strict unit-sublevel planar area below that tolerance. The conclusion is zero for the literal infimum over exactly this same polynomial class. A hypothetically positive ENNReal infimum admits a strictly intermediate ofReal epsilon even if the infimum is infinity; the supplied polynomial then contradicts the infimum lower-bound property. This is a conditional order-theoretic conversion, not a new assumed threshold theorem, a converse, or attainment of area zero.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found relative to the registered statement.

- Signature UTF-8 SHA-256: `14121dbcd68b6ad808d7262b1727d4cc2172d4bed95416601af49c62079150aa`.
- Source-statement UTF-8 SHA-256: `92ebd050c50fd28605f452d7627a3c0d6b1121ef51b12b435a206fb9f430a239`.

### `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter`

Claim ID: `E1040-FULL`; role: `target`.

For every closed infinite complex source F with its actual geometric transfinite diameter at least one, its exact monic positive-degree strict-lemniscate area infimum minimalLemniscateArea F equals zero. This is the literal vanishing-infimum formulation of original Problem 4, derived from the previously admitted positive-tolerance theorem.

```lean
theorem Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter : ∀ {F : Set.{0} ℂ},
  IsClosed.{0} F →
    Set.Infinite.{0} F → LE.le.{0} 1 (Erdos1040.transfiniteDiameter F) → Eq.{1} (Erdos1040.minimalLemniscateArea F) 0
```

The exact signature retains arbitrary closed infinite complex F and the inequality one <= the already defined geometric transfiniteDiameter F. Its conclusion is the literal minimalLemniscateArea F = 0. The proof supplies the conversion premise directly from the admitted erdos1040 theorem for each positive real epsilon. It adds no compactness, boundedness, source measure, equilibrium or regularity hypothesis, and covers the existing unbounded branch through that theorem. No minimizer polynomial or computational bound is asserted.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found relative to the registered statement.

- Signature UTF-8 SHA-256: `3c33b338c2abd32e0f843d5b45c95ec5398eea85a5c4d21b501c96b9b401fce8`.
- Source-statement UTF-8 SHA-256: `f104662aa3476c23fead51c3185c13cd21019200ed6b238f21b847c1de59f3ef`.

### `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity`

Claim ID: `E1040-CAP1`; role: `target`.

For every compact complex source F with its literal Robin-energy logarithmic capacity at least one, its exact monic positive-degree strict-lemniscate area infimum minimalLemniscateArea F equals zero. No regularity, positive-area or supplied measure hypothesis is added; capacity exactly one is included.

```lean
theorem Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity : ∀ {F : Set.{0} ℂ},
  IsCompact.{0} F → LE.le.{0} 1 (Erdos1040.logarithmicCapacity F) → Eq.{1} (Erdos1040.minimalLemniscateArea F) 0
```

The exact signature retains arbitrary compact complex F and one <= the existing Robin-energy logarithmicCapacity F. It concludes zero for the literal infimum over all monic positive-degree actual complex polynomials with every root in F and strict unit sublevels. The proof uses the admitted capacity-at-least-one arbitrarily-small theorem and the admitted actual-polynomial conversion to discharge the conditional conversion premise. Capacity exactly one is included; the explicitly registered source statement already states at least one. No positive-area, boundary regularity, supplied probability, geometric-capacity equivalence or root distinctness assumption is added.

Correspondence: **PASS**. No extra assumption, omitted quantifier, weakening, strengthening, domain change or hidden measure convention was found relative to the registered statement.

- Signature UTF-8 SHA-256: `c5295da6af3231e93e43e2bf96cb455b7433dfad30f08ed65f5e06c6e8a8751f`.
- Source-statement UTF-8 SHA-256: `0abe0136fc535e4dbdc202b0e52003a333617a08d2d5ba68a50dc6e7bdb8c836`.

## Supporting sources inspected

| File | SHA-256 | Review extent |
| --- | --- | --- |
| `formal/Erdos1040/CapacityDependence.lean` | `4c89800720e3208bccd5c044fc3013dba5d69d37648e940ee319119fc626a60b` | Literal minimalLemniscateArea definition and its lower-than-each-feasible-area lemma; no review of the rest of the counterexample module is asserted here |
| `formal/Erdos1040/FullTheorem.lean` | `f6693aa7defbc2f7328600f82423260b5b8eeb070ab4d54bc2a2ee347e59aeb2` | Complete existing positive-tolerance geometric endpoint |
| `formal/Erdos1040/CapacityTheorem.lean` | `b44f1b93006d7f5b689bc7563ceef2b4186982e3807818e0853765a0dc4b09cf` | Complete capacity-at-least-one and capacity-one endpoint module |
| `formal/Erdos1040/PolynomialConclusion.lean` | `adf239ac7dcb215854cd5b9c5d083edc40d0d6eb8e2d2120021b96d2d878ff68` | Complete actual-polynomial conversion module |
| `formal/.lake/packages/mathlib/Mathlib/Data/ENNReal/Basic.lean` | `78f9471c55fe2cfaa8fec97195c4e8a11156dfd0366d50e187a743f5f077330f` | Exact lt_iff_exists_real_btwn statement and proof at lines 589-595 |

The companion `formalization-preflight-area-infimum-endpoints-bindings.json` maps each of the three declaration names to the required five manifest-review fields: source-byte SHA-256, exact printed-signature UTF-8 SHA-256, exact source-statement UTF-8 SHA-256, reviewer name and individual notes.
