# Independent correspondence review: SourceDensity

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/SourceDensity.lean`, SHA-256
`897026f5e0c071a9bf2ae271d745adcb029c6455212241d8419e7354b8f9f25f`.
The first complete machine PASS including these eight declarations is dated
`2026-09-05T04:26:19.631608+00:00` and is preserved in
`formal/admissions/2026-09-05-analytic-bridges-pre-admission.json`.
All eight signatures were also independently printed with their axiom lists;
that Lean invocation exited zero and its output is preserved in
`formal/.audit/preflight-source-density.log`. A later console encoding error
while displaying the saved Unicode output did not affect that Lean run.
The source was unchanged across the independent print run and review.

This reviewer read the full source, all eight manifest statements, the actual
definitions and prerequisite results in `SourcePotential.lean` and
`AdjointPotential.lean`, and the candidate's section 5. The review bindings
are in `preflight-source-density-bindings.json`. No mathematical source was
edited and no theorem was promoted by this reviewer.

## Quantifiers, measures, and signed densities

Every theorem has arbitrary compact planar source and observation sets S and
K. The source measure mu is an arbitrary finite positive measure on subtype S;
the zero measure and singular measures are allowed. It need not be a
probability measure or an equilibrium measure. The observation measure is
ordinary planar Lebesgue measure restricted to K, without normalization.
The real Hilbert space is exactly `Lp Real 2 (volume.restrict K)`.

The first six theorems use a measurable real function f on S and a real
constant C bounding its norm at every source point. The signed source is
represented by the real multiplier f against positive mu. No positivity,
mass-zero condition, or continuity of f is assumed. A separate nonnegativity
assumption on C is unnecessary: on a nonempty source its bounding property
already forces C to be nonnegative, and empty sources are harmless.
The pointwise bounded measurable representative is faithful to the
candidate's bounded real Borel test functions. These statements do not claim
an unproved equivalence with an arbitrary unchosen essential-boundedness
class.

## Six actual-integral and L2 identities

`integrable_areaLogKernel_density` proves genuine Bochner integrability of
the area-L2-valued function `f(w) * areaLogKernel(w)`. Continuity of the kernel
map on compact S supplies its integrability under finite mu; the bounded
measurable scalar multiplier preserves it.

`integrable_log_density_prod` proves absolute integrability of the actual
scalar kernel `f(w) log(norm(z-w))` for the product of source measure and
restricted planar area. Its prerequisite establishes joint integrability
of the logarithmic kernel using square integrability and the compact
source kernel-norm bound. Thus the scalar Fubini step has an explicit
integrability justification even when sources lie in K.

`areaLogKernel_density_integral_ae_eq_source_potential` identifies the
representative of the Bochner integral with the actual scalar source
potential almost everywhere for restricted area. It tests both integrable
functions against every measurable finite-area set, using the L2 indicator
of that set and the continuous inner-product functional. It does not treat
point evaluation as a continuous functional on L2. The restricted product
measure in the Fubini argument is exactly source measure times the further
restriction of area to that test set.

The claimed equality is area-almost everywhere, not pointwise at every
observation. Mathlib totalizes the logarithm and nonintegrable scalar
integrals; joint absolute integrability ensures the represented source
integral has integrable sections almost everywhere. No false all-point
singular-integral claim is used. Values at exceptional observations do not
alter the L2 class or later area estimates.

`memLp_source_density_potential` transports the Bochner integral's real L2
membership through precisely that almost-everywhere equality.
`source_density_potential_toLp_eq_integral_areaLogKernel` identifies the
resulting L2 class with the same Bochner integral using representative
equality. These results preserve the observation set, exponent, and measure.

`inner_integral_areaLogKernel_density` pairs any real area-L2 element h with
this Bochner integral. Pulling the continuous inner-product functional
through the integrable Bochner integral yields the source integral of
`f(w) * adjointAreaPotential(h,w)`. The previously checked adjoint identity
identifies that value with the actual finite area integral
`integral_K h(z) log(norm(w-z)) darea(z)` at every source point. Symmetry of
the complex norm reconciles the two displayed subtraction orders. No
surrogate potential or unstated triple-integral exchange is introduced.

## Conditional annihilator consequences

`adjointAreaPotential_ae_zero_of_annihilator` has an explicit hypothesis:
h is orthogonal to the Bochner source potential of every pointwise bounded
measurable real density. This is exactly the arbitrary-bounded-test-function
step in candidate equation (7), not a proof that any particular h satisfies
that hypothesis or that the source potentials are dense.

The actual adjoint potential is continuous on the plane. Its restriction to
compact S is therefore bounded and measurable and can itself be substituted
as the test density. Orthogonality gives the integral of its square equal
to zero. The square is integrable because it is continuous on the compact
source and mu is finite. Nonnegativity then gives zero mu-almost everywhere.
This argument is valid for either sign of h and for arbitrary finite mu.

`adjointAreaPotential_zero_on_support_of_annihilator` transports that exact
almost-everywhere statement along the measurable subtype inclusion into the
plane. Continuity makes the zero set closed, so it contains the topological
support of the pushforward measure. The conclusion is on
`support(mu.map Subtype.val)`, not automatically on every point of S.
Identifying this support with an intended equilibrium support is a separate
application obligation. No full-support assumption is hidden here.

## Outcome and limits

All eight printed signatures agree with the supplied statements. No changed
domain, omitted quantifier, extra mathematical premise, measure alteration,
or unreported strengthening was found. The distinction between actual scalar
integrals, their almost-everywhere representatives, and exact L2 class
identities is maintained throughout.

The frozen whole-project machine report passes build, owned-declaration,
placeholder, dependency-pin, immutable-input, and axiom checks. Each of these
eight declarations depends only on `propext`, `Classical.choice`, and
`Quot.sound`, allowing universe annotations. The separate printed signatures
and axiom outputs match that report exactly.

This correspondence review supports the bounded-density source identities
and the two conditional annihilator consequences only. It proves no
equilibrium/Frostman theorem, exterior uniqueness statement, moment identity,
complete approximation-density theorem, capacity-one conclusion, or final
target E1040-CAP1/E1040-FULL. Trusted-core admission remains a separate gate.
