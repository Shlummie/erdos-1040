# Independent correspondence review: DiscretePotential

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/DiscretePotential.lean`, SHA-256
`1a7602dd174d34e6b963207ec581884b0761824f21faf38fe6712cbe8fd61db8`.
The author, the root agent, froze the module after a successful full checker
run. This reviewer did not edit it. The review compares all five proof bodies,
the five manifest statements, their previously reviewed atomic-potential and
kernel-class definitions, and separately printed exact signatures. The fresh
signature and axiom print run exited 0 and is recorded in
`formal/.audit/preflight-discrete-potential.log`. The source hash was checked
again after that run. Bindings are in `preflight-discrete-potential-bindings.json`.

## Finite root lists and L2 representatives

`memLp_atomicLogPotential_of_isCompact` quantifies over every natural list
length, every `Fin n`-indexed complex root list, and every compact observation
set K. Every shifted logarithmic kernel belongs to real L2 on K by the checked
kernel theorem. Finite summation and multiplication by the reciprocal of n
then give the required membership for the actual `atomicLogPotential`.
There is no hypothesis that roots lie in K and none is needed for this lemma.
The underlying measure is exactly planar Lebesgue measure restricted to K.

The root indices, rather than distinct root values, are summed over. Repeated
roots therefore retain their multiplicity and weight; no distinctness is
introduced. The definition permits `n = 0`: the sum is empty and the reciprocal
is totalized to zero, so this potential is identically zero. This case is
explicitly documented in the manifest and is included in the first three
supporting theorems. It is not used to satisfy positive-degree approximation.

`areaLogKernel_average_ae_eq_atomicLogPotential` identifies an almost-everywhere
representative of the L2 average, not a pointwise value of an L2 equivalence
class. The proof combines the representative identity for each kernel, the
finite-sum representative identity, and the scalar-multiplication identity.
All these almost-everywhere statements use the same restricted area measure.
The finite intersection of their full-measure sets is sufficient even with
repeated roots. The order of scalar multiplication agrees with division by n
in the real-valued atomic potential. Empty sums are handled without a hidden
positive-length hypothesis.

`atomicLogPotential_toLp_eq_average_areaLogKernel` then uses Lp extensionality
and the two almost-everywhere representative identities to prove actual
equality of L2 classes. The `toLp` membership proof is supplied by the preceding
proved theorem. It is not an assumed class equality or an unrelated definition
of an atomic potential. The equality includes exactly the same empty-list and
repeated-root conventions as the natural-language statement.

## Compact sources and the Bochner potential

`integrable_areaLogKernel_on_compact` has separate compact source and observation
sets S and K, and an explicit probability measure on the source subtype S.
The subtype inherits its measurable structure from the complex plane. The map
from this compact subtype to the L2 class on K is continuous by the established
kernel norm-continuity theorem. Continuity on a compact space and finiteness
of the probability measure give its Bochner integrability. No absolute
continuity of the source measure, separation of S from K, boundary regularity,
positive area, connectedness, or extra separability assumption is added.

The Bochner integral is valued in the fixed real L2 space for area on K. It is
not yet identified with the class represented by the arbitrary-measure
pointwise source integral `z -> integral log(norm(z-w)) dmu(w)`. Establishing
that representation would require a separate justified interchange and
almost-everywhere argument. Both the module text and final manifest statement
explicitly preserve this distinction, so there is no hidden correspondence
claim for an arbitrary source measure or singular point.

`exists_roots_approx_areaLogKernel_integral` applies the previously checked
equal-weight Banach-kernel approximation theorem to this continuous compact
source map. For each positive real tolerance it returns a natural `n > 0`,
then n complex roots, each accompanied by membership in the original S.
Those roots come directly from the source subtype; they are not chosen in an
expanded hull, a closure substituted for S, or the observation set K. Repetition
is allowed. The finite L2 class identity then converts the kernel average into
the class of the actual totalized atomic potential. The strict error bound is
an L2 norm bound on K against the genuine Bochner integral.

Probability is explicit, rather than inferred from a general measure. It also
precludes an empty source subtype, so no missing nonemptiness premise is needed
for the positive list. An empty or zero-area observation set is permitted and
produces its usual trivial L2 space. The theorem provides neither a prescribed
degree nor a convergence rate, and does not claim simultaneous convergence
against every continuous test function or an exterior uniform-norm bound.

## Outcome and remaining distinctions

All five exact signatures match the manifest statements. The quantifier order,
positive approximation degree, original-set roots, arbitrary compact source
and observation domains, probability assumption, finite representative
identities, and Bochner interpretation are faithful. No extra assumption,
omitted quantifier, hidden weakening, or unreported strengthening was found.

All five independently printed axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`, with universe annotations. The observed
full-project report passed for the frozen module. This review performs no
trusted-core promotion and does not replace a final project gate after other
changes.

This closes the finite-class and compact Bochner-kernel discretization bridge.
The pointwise potential representation for arbitrary source measures, the
equilibrium/density argument, and the exact targets `E1040-CAP1` and
`E1040-FULL` remain distinct obligations.
