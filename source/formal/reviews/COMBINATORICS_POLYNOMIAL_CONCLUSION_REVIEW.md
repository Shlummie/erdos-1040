# Independent correspondence review of PolynomialConclusion

Reviewer: combinatorics_scout. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/PolynomialConclusion.lean`, SHA-256
`adf239ac7dcb215854cd5b9c5d083edc40d0d6eb8e2d2120021b96d2d878ff68`.
The root agent authored the proofs; this reviewer did not modify them.
The source, both natural-language statements, and both exact printed
signatures were compared against the passing immutable report
`formal/admissions/2026-09-05-polynomial-conclusion-pre-admission-205.json`,
checked at 2026-09-05T05:56:43.541238+00:00. Exact declaration bindings are
recorded in `combinatorics-polynomial-conclusion-bindings.json`.

1. `HasArbitrarilySmallLemniscates.mono` transfers the previously defined
   property from an arbitrary complex set S to any containing set F. It
   reuses the same positive degree, all finite roots, and the same strict
   unit lemniscate area bound for every positive real tolerance. It assumes
   neither compactness nor closedness and introduces no change of scale.

2. `exists_monic_polynomial_small_area` takes the exact finite-root property
   for an arbitrary F and returns an actual complex polynomial for every
   positive real tolerance. The polynomial is monic, its natural degree is
   strictly positive, every one of its complex roots lies in F, and its strict
   norm sublevel at one has planar Lebesgue volume below the tolerance. The
   proof uses the already checked product polynomial and its exact degree,
   evaluation, and root-characterization identities. Multiplicities and
   repeated selected roots are allowed. Root containment is universal over
   every complex polynomial root, not just the chosen finite tuple. The
   strict inequality and area convention agree exactly with the statement.

No extra assumption, omitted quantifier, domain change, hidden weakening,
or unsupported strengthening was found. Both declarations are conditional
on the finite-root property; neither establishes it for a new source class.
The immutable report passes all machine checks, and both declarations use
only the standard logical axioms propext, Classical.choice, and Quot.sound.
This separate correspondence review confirms the stated supporting scope.
It does not establish E1040-CAP1, E1040-FULL, or any P versus NP implication.
