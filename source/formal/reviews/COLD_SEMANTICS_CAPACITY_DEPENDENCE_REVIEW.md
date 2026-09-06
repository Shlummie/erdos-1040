# Independent correspondence review: geometric scaling and capacity-only dependence

Reviewer: cold_semantics. Review completed at 2026-09-05T19:06:38.602929+00:00.

## Scope, versions and verification status

This review covers all 15 declarations in the two root-authored installed modules below: four in GeometricScaling and eleven in CapacityDependence. The reviewer read both complete source files, all 15 exact printed signatures and registered natural-language statements, the displayed axiom results, and the relevant definitions and dependency statements. The reviewer suggested the dilation/countability mathematical route earlier but did not author or edit these Lean proofs. This is a separate agent correspondence review, not an independent human review or a claim of independent conceptual discovery.

- `formal/Erdos1040/GeometricScaling.lean`: `9e9207aed62a7d92814f32a68a28094219c55b3c63a9ca4fdb0582594253b684`.
- `formal/Erdos1040/CapacityDependence.lean`: `4c89800720e3208bccd5c044fc3013dba5d69d37648e940ee319119fc626a60b`.

The observed full-check report is `formal/.audit/report.json`, checked at 2026-09-05T19:03:17.475803+00:00, SHA-256 `e0d517065c7f077bba2633e9eb12d46cb23ece2e62acef4f1dca3c41da3bda1b`. It reports machine_checks_pass=true, no errors, and 271 tracked declarations. All 15 reviewed declarations have successful axiom audits and use only propext, Classical.choice and Quot.sound. The report main_target_complete value is false at this pre-admission stage. This correspondence approval does not set final admission or replace separate dependency reviews and final record synchronization. The earlier report with the foreign generated normHom helper was not accepted as a passing run.

For every declaration, source_sha256 was independently recomputed from the complete installed module bytes, signature_sha256 from the exact report signature encoded as UTF-8, and statement_sha256 from the exact registered source_statement encoded as UTF-8. All match the report and current manifest. The companion `cold-semantics-capacity-dependence-bindings.json` contains those 15 independent bindings and per-declaration review notes.

## Original source and exact admissible family

The reviewer visually inspected complete printed pages 125, 135 and 136 of Erdős, Herzog and Piranian, *Metric properties of polynomials* (1958), including Equation (1), the entire Problem 4, and its continuation. The local primary PDF is `erdos-research/sources/EHP1958-metric-properties.pdf`, SHA-256 `5d20ad770563e425ac3343e31581859a24facabf744f10489b8f8d201b0ec12a`; primary URL: https://users.renyi.hu/~p_erdos/1958-05.pdf. Equation (1) uses a monic finite product of z minus its roots. Its E(f) is the strict unit sublevel set, and the area in this section is two-dimensional measure. Problem 4 first asks whether the infimum of these areas for roots in a closed infinite F is determined by its transfinite diameter, then separately asks for zero infimum at diameter at least one. The continuation records known segment and disk cases; it adds no hypothesis to the first question.

The new functional ranges over actual p : C[X], with p.Monic, 0 < p.natDegree, and every complex z satisfying p.IsRoot z belonging to F. This is the same positive-degree monic polynomial family as the original root products, including multiplicities. The existing Basic module proves monicity, evaluation, exact degree and the root characterization of finite root products. Conversely, complex algebraic closure gives IsAlgClosed.splits p; Polynomial.Splits.eval_eq_prod_roots_of_monic recovers the exact evaluated root product and Splits.natDegree_eq_card_roots preserves its positive length. The current AreaObstruction proof actually uses those checked factorization facts for every admissible polynomial. Thus the lower bound does not cover only an arbitrarily selected polynomial subclass. No new theorem equating two separately defined infimum functionals is claimed or needed: only the actual-polynomial infimum is defined here.

The three proof-valued infimum indices do not weaken the restrictions. An uninhabited condition contributes the top element of ENNReal, while inhabited proof indices repeat the same area. Taking the polynomial infimum therefore gives exactly the admissible areas, with infinity for an empty family. Positive natural degree excludes the constant-one empty-product case. Monicity excludes arbitrary scaling. The source condition applies to all complex roots in the original F. The set uses norm(p.eval z) < 1, not a nonstrict inequality or a real-line sublevel, and volume is the standard complex planar Lebesgue measure. There is no arbitrary measure parameter and no conversion of infinite area to real zero. Despite the functional name, no minimum attainment is asserted.

## Declaration-by-declaration comparison

1. `Erdos1040.geometricMeanSeparation_dilate`: Every finite complex tuple is quantified, including repeated points. The only restrictions are order N >= 2 and a strictly positive real dilation c. The exact unordered-pair product, exponent 2/(N(N-1)), and complex coercion of c agree; no injectivity or nonzero-product assumption is added.

2. `Erdos1040.finiteDiameter_dilate`: The source is an arbitrary complex set, and N >= 2 and c > 0 are explicit. Both tuple-image directions preserve the exact supremum, repeated entries, empty source and extended infinity. The coefficient is ENNReal.ofReal c; no compactness or finiteness is assumed.

3. `Erdos1040.transfiniteDiameter_dilate`: The arbitrary source and positive real dilation match the statement. The definition remains the infimum of the N=n+2 geometric finite diameters; positive finite ofReal c justifies transport through the infimum, including zero and infinity. No energy definition is substituted.

4. `Erdos1040.transfiniteDiameter_eq_zero_of_countable_compact`: The only hypotheses are compactness and countability of a complex set. Compactness gives finite geometric diameter, positive diameter would dilate to one, and the admitted energy-existence theorem then contradicts countable probability nonatomicity. No capacity-diameter identity or supplied energy measure is assumed.

5. `Erdos1040.minimalLemniscateArea`: The full definition body was inspected, not only its Set-to-ENNReal signature. It infimizes actual complex polynomials subject to monicity, positive natural degree and every complex root in F, using planar volume of the strict norm(eval)<1 set. Proof-indexed infima exclude inadmissible cases by top; no attainment is asserted. The original monic root-product family agrees by complex factorization with multiplicities.

6. `Erdos1040.minimalLemniscateArea_le_of_monic`: The exact actual polynomial, monicity, positive natural degree and universal root containment are hypotheses. Four infimum projections bound the defined area by this polynomial strict-sublevel planar volume. No geometric or analytic assumption on F is added.

7. `Erdos1040.smallCountableSource_minimalLemniscateArea_ge`: The exact source is zero together with all reciprocals 1/(n+4). The lower bound is ofReal(9*pi/16) for the complete admissible-polynomial infimum. The proof quantifies over every admissible actual polynomial and uses the separately reviewed universal monic-polynomial ball obstruction, with no restriction to a selected root tuple.

8. `Erdos1040.largeCountableSource`: The full definition body is exactly insert 4 (insert (-4) smallCountableSource), with all points complex. The small source retains zero and every reciprocal 1/(n+4); there is no closure, hull, deletion or replacement of roots.

9. `Erdos1040.largeCountableSource_countable`: The exact defined enlarged source is countable by two singleton insertions into the countable small source. No additional hypothesis is present.

10. `Erdos1040.largeCountableSource_isCompact`: The exact defined enlarged source is compact in the usual complex topology by two finite insertions into the compact small source. No closedness-only substitute or boundedness assumption is hidden.

11. `Erdos1040.largeCountableSource_infinite`: The exact enlarged source contains the independently proved infinite small source. The conclusion is set infinitude, without any extra parameter or hypothesis.

12. `Erdos1040.largeCountableSource_minimalLemniscateArea_le`: The exact enlarged source area infimum is at most ofReal(pi/8). The proof uses the separately checked actual monic positive-degree quadratic with roots exactly 4 and -4, verifies both roots belong to the original enlarged source, and invokes the admissible-polynomial infimum bound.

13. `Erdos1040.capacity_only_dependence_counterexample`: The existential witnesses are compact infinite complex sets, each with actual geometric transfinite diameter zero and energy-defined logarithmic capacity zero. The strict area inequality has the intended direction, large source below small source. Both invariants are separately proved zero; no general equality between them is assumed. The capacity interpretation is classical on these compact witnesses.

14. `Erdos1040.minimalLemniscateArea_not_determined_by_transfiniteDiameter`: The negation forbids one ENNReal-to-ENNReal function that determines the exact area infimum for every closed infinite complex source from its geometric transfinite diameter. Compact witnesses are closed in the complex topology and share diameter zero but have unequal areas. This answers the original first question, with no extra regularity or boundedness restriction in its universal domain.

15. `Erdos1040.minimalLemniscateArea_not_determined_by_logarithmicCapacity`: The negation forbids one ENNReal-to-ENNReal function that determines the exact area infimum from logarithmic capacity for every compact infinite complex source. The compact domain is deliberate and expressly registered, preserving the classical-capacity interpretation; this is a separate companion statement to the original closed-infinite geometric question.

## Mathematical assembly and limits

The exact witnesses are S = {0} union {1/(n+4) : n is natural} and T = S union {-4,4}. The small source lies in the closed disk of radius 1/4. Every admissible positive-degree monic polynomial for S has its strict unit sublevel containing the open disk of radius 3/4, so its area infimum is at least 9*pi/16. The admissible quadratic with roots 4 and -4 gives area infimum for T at most pi/8. Since pi/8 < 9*pi/16, the strict inequality follows without requiring either infimum to be attained or computing either exact value. Countability and compactness give geometric diameter zero through the reviewed dilation and finite-energy argument, while a separately reviewed theorem proves logarithmic capacity zero. General equality of capacity and transfinite diameter is not assumed.

The geometric diameter remains the actual pair-distance-product supremum/infimum definition. The previously admitted GeometricDiameterLimit support establishes its decreasing geometric-limit interpretation; this review does not replace that dependency review. Empty and infinite-diameter conventions are preserved by the dilation statements. The countable-zero theorem explicitly retains compactness, which is needed by its finite-diameter and energy-existence argument. The witnesses are compact and infinite, and the final geometric negation quantifies over all closed infinite complex sources. The logarithmic-capacity companion explicitly quantifies over compact infinite sources, consistent with the classical interpretation of that definition.

No extra assumption, omitted quantifier, hidden weakening, unsupported strengthening or mathematical circularity was found in these 15 statements. The additional equal-zero logarithmic-capacity assertions strengthen the explicit counterexample while remaining independently justified. This formalizes a known negative answer to the separate first question and makes no novelty, priority, publication, external acceptance or P-versus-NP claim. It neither contradicts nor reproves the existing positive threshold theorem. CountableSources and AreaObstruction remain subject to their own independent version-bound reviews. Final trusted-core admission is owned by the root workflow after all documented gates pass.
