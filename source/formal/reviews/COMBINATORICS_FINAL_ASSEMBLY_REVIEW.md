# Independent correspondence review of compact and full theorem assembly

Reviewer: combinatorics_scout. Date: 2026-09-05 UTC.

## Reviewed versions and scope

The root agent authored both reviewed modules. This reviewer read their
complete current sources and compared the three exact printed signatures
and registered natural-language statements with the immutable passing report
`formal/admissions/2026-09-05-full-candidate-pre-admission-240.json`, checked
at 2026-09-05T06:15:08.856723+00:00. Actual source hashes were checked against
that report immediately before writing this review:

- `formal/Erdos1040/CompactLemniscate.lean`:
  `60b037f951929fa6049fee6dadf841e37a5139262e68263cb55c6819d5279174`.
- `formal/Erdos1040/FullTheorem.lean`:
  `f6693aa7defbc2f7328600f82423260b5b8eeb070ab4d54bc2a2ee347e59aeb2`.

Per-declaration source, exact-signature and natural-statement hash bindings
are in `combinatorics-final-assembly-bindings.json`.

The reviewer also read Basic, PolynomialConclusion, GlobalFrostman,
NonnegativePotentialLemniscate and EnergyDiameter to trace the assembly's
actual meanings and discharged hypotheses. The reviewer authored the
geometric-diameter and geometric-limit modules and some earlier analytic
components; their independent correspondence reviews belong to other agents.
This review is independent of authorship of the three assembly declarations
only. It does not substitute for the separate dependency reviews.

## Original mathematical target and notation

The saved primary source, Erdős, Herzog and Piranian, *Metric properties of
polynomials* (1958), was visually checked on complete printed pages 125 and
135. Equation (1) on p.125 defines the monic product of z minus its finitely
many zeros and defines E(f) by the strict inequality |f(z)| < 1. The same page
identifies the relevant quantity as two-dimensional measure. Problem 4 on
p.135 asks, for a closed infinite F, whether the infimum of these areas over
polynomials with all zeros in F vanishes whenever its transfinite diameter
is at least one. The original separate question about dependence only on
transfinite diameter is not part of the asserted theorem and is already
recorded as false in the research sources.

Source: `erdos-research/sources/EHP1958-metric-properties.pdf`, SHA-256
`5d20ad770563e425ac3343e31581859a24facabf744f10489b8f8d201b0ec12a`;
primary URL: https://users.renyi.hu/~p_erdos/1958-05.pdf.
The frozen candidate's section 1, statement (T), the canonical ledger and
statement map express the same every-positive-tolerance formulation.

The geometric definition is not an energy predicate or a bundled potential
assumption. `unorderedPairProduct` is exactly the product of Euclidean
pair distances for i < j; `geometricMeanSeparation` raises it to 2/(N(N-1));
`finiteDiameter` takes the extended supremum over all N points in the source.
For nonempty compact sources of order at least two it is a finite attained
maximum. The orders used in `transfiniteDiameter` are exactly N = n+2.
`finiteDiameter_succ_le`, `antitone_finiteDiameter`, and
`tendsto_finiteDiameter_transfiniteDiameter` prove that this infimum is the
actual decreasing geometric limit. Thus there is no limit-versus-infimum
specification gap. The explicit GeometricDiameterLimit import makes this
correspondence available with the final theorem. Separate reviewers must
still approve those dependency versions.

## Declaration comparisons

1. `hasArbitrarilySmallLemniscates_of_finite_minimizer` has exactly the
   registered conditional hypotheses: compact complex S, a positive real
   scale D bounding every pair distance in S, an actual probability on S,
   finite extended singular energy, minimization against every probability
   on S, and energy.toReal <= log D. It applies the proved pointwise global
   Frostman lower bound log D - energy.toReal <= integral(log norm(z-w))
   and the numerical energy hypothesis to obtain nonnegativity for every
   complex z. The nonnegative-potential assembly then discharges support,
   hull and strict-exterior requirements. The conclusion is the exact
   finite-root property for S. This lemma is visibly conditional; it is not
   presented as a capacity theorem by itself. No potential regularity or
   support geometry is assumed covertly, and the finite-energy assumption
   is explicit before any real conversion.

2. `hasArbitrarilySmallLemniscates_of_one_le_transfiniteDiameter` has only
   compactness of an arbitrary complex set S and its actual geometric
   transfinite diameter at least one as hypotheses. It constructs the
   distance bound D = max(1, diam S), invokes the proved geometric-to-energy
   theorem to construct a finite global minimizing probability, and applies
   the preceding conditional lemma. Its exact conclusion means every
   positive real tolerance has a positive natural degree and a finite root
   tuple entirely in the original S with strict unit-lemniscate planar area
   below that tolerance. There is no supplied measure, density, smoothness,
   regularity, energy bound or potential hypothesis. This covers arbitrary
   compact sources at diameter one as well as larger diameters.

3. `erdos1040` quantifies over every complex set F, assumes exactly closedness,
   infinitude and transfinite diameter at least one, then quantifies over
   every positive real epsilon. Its output is an actual complex polynomial
   p with four exact properties: monicity, positive natural degree, universal
   containment in F of every complex root, and planar Lebesgue volume of the
   strict set norm(p.eval z) < 1 below ofReal(epsilon). Positive degree rules
   out the vacuous constant polynomial. The proof splits on boundedness.
   Closed and bounded F is compact, so the compact geometric theorem applies.
   Unbounded F uses the already proved unconditional quadratic construction;
   no compactness or capacity convention for unbounded sets is smuggled into
   that branch. PolynomialConclusion constructs the same monic finite-root
   product and preserves the exact strict area bound. The stated infinitude
   hypothesis is unused because the proved argument is stronger in this
   respect; keeping that redundant original hypothesis changes no quantifier
   or conclusion. No roots move into an enlarged hull. Repeated roots remain
   permitted, just as for the original monic products.

## Result and remaining admission distinction

No extra assumption, omitted quantifier, domain change, hidden weakening or
unsupported strengthening was found in any of the three registered
statements. The final theorem matches the original target's explicit
positive-tolerance content. Its conclusion gives zero infimum because
Lebesgue area is nonnegative; the reverse characterization of the infimum
is elementary and is not used as a hidden premise of this theorem.

The immutable full report passes the machine build, source/dependency scans
and axiom audits. Each of these three declarations depends only on propext,
Classical.choice and Quot.sound. This document supplies the separate
correspondence approval for the recorded assembly versions. Trusted-core
promotion and any statement that the complete research target is established
still require all dependency reviews, final manifest/record synchronization
and the project's final admission gate. It makes no claim about P versus NP,
priority, publication, or independent human mathematical review.
