# Independent correspondence review: ExteriorKernel

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/ExteriorKernel.lean`, SHA-256
`39421cd86c7dcc62b60e9e8c9c00a67ffb3dc4952911fed92056d222cacae109`.
The author, combinatorics_scout, froze the module after a full checker PASS.
This reviewer did not edit it. The review compares all six definition/proof
bodies, the six manifest statements, the existing area-kernel and finite
atomic-potential conventions, and separately printed exact signatures. The
independent print run exited 0; its log is
`formal/.audit/preflight-exterior-kernel.log`. The source hash was rechecked
after that run. Bindings are in `preflight-exterior-kernel-bindings.json`.

## Disjoint sets and the function-space topology

`exteriorLogKernel` uses the source subtype S and observation subtype E.
Its value at a source w is the real continuous function on E given by
`log(norm(z-w))`. The explicit disjointness hypothesis ensures z differs from w
for every such pair, so the logarithm's argument is positive. No compactness
is used or needed for this definition, and neither set is silently replaced
by a closure or hull. The totalized value of the logarithm at zero is never
needed for these disjoint source-observation pairs.

`continuous_exteriorLogKernel` uses joint continuity of this logarithmic
function on the product of the two subtypes to obtain continuity into C(E,R).
At this level C(E,R) has its compact-open topology. The declaration has no
compactness assumption and does not assert a global uniform norm on a
noncompact observation space. The manifest explicitly makes this distinction.

The following four declarations all contain the explicit typeclass binder
`[CompactSpace E]`, visible in their printed signatures. With the inherited
subtype topology this says precisely that the observation subtype is compact.
It equips C(E,R) with the uniform norm and its complete normed-space structure;
the topology agrees with the compact-open topology already used. Thus those
norm claims do not omit a compact-observation requirement. Source compactness
is separately supplied as `IsCompact S` and is not inferred from disjointness.

## The exterior integral

`integrable_exteriorLogKernel_on_compact` combines continuity on the compact
source subtype with the explicitly given probability measure to prove Bochner
integrability in the continuous-function Banach space. It does not assume
absolute continuity of the source probability or any boundary regularity.
The measure is on the original source subtype, so source membership is built
into its domain. Compact source and observation sets may be empty in the
abstract declarations, but an actual probability on an empty source subtype
cannot exist; no separate missing nonemptiness premise is required.

`exteriorLogKernel_integral_apply` commutes continuous-function evaluation at
an arbitrary z in E with that genuine Bochner integral. Its right side is the
actual scalar source integral of `log(norm(z-w))`. Evaluation is a bounded
linear map in the uniform-norm space, so integrability of the function-valued
kernel also gives integrability of each scalar evaluation. This is not an
identity obtained by treating nonintegrable scalar integrals as zero. It is
valid at every exterior observation, not just almost everywhere.

This exterior evaluation identity does not establish a pointwise source-integral
representative for the area-L2-valued integral when source and observation sets
overlap. That separate area representation remains distinct.

## One root list for both estimates

`exists_roots_approx_area_and_exterior_integrals` quantifies over compact source
S, compact area observation K, compact exterior observation E, disjointness of
S and E, a probability on S, and two strictly positive tolerances. It samples
the single continuous product kernel

`w -> (areaLogKernel(K,w), exteriorLogKernel(w))`

into the product of real area-L2 and the exterior continuous-function Banach
space. The equal-weight approximation theorem is applied once with tolerance
`min(epsilonA, epsilonE)`. Each component norm is bounded by the product norm,
and each component integral is the corresponding projection of the Bochner
integral. Therefore the two error bounds use exactly one degree and one list,
not two independently chosen existential root lists.

The returned list has type `Fin n -> S`, with `n > 0`. Every root consequently
lies in the original source set, repetitions are permitted, and the common
weight is exactly `1/n`. There is no prescribed-degree restriction or
quantitative convergence rate. The area observation K need not be disjoint
from the source or exterior observation; only the stated S-E disjointness is
used. Empty or zero-area observations do not create an invalid positive-degree
witness because source nonemptiness comes from the probability measure.

`exists_roots_approx_area_and_exterior_potentials` retains that same area
L2 estimate and that same root list. The uniform norm bound controls every
evaluation in E. The integral-evaluation identity and the exact finite sum
formula identify the evaluated average with the actual `atomicLogPotential`
of those complex roots. The result is a strict scalar absolute-error bound
with the same exterior tolerance for every z in E. No exceptional source
points occur in E because of disjointness, and no almost-everywhere weakening
is substituted for the pointwise exterior assertion.

The area side of these two declarations remains the L2 average of kernel
classes. The separately reviewed `DiscretePotential` theorem identifies that
finite average exactly with the class of the actual finite atomic potential.
Neither exterior declaration claims the still-separate arbitrary-source
pointwise area-potential representation.

## Outcome and limits

All six exact signatures match their manifest statements. The compact-open
versus uniform-norm distinction, explicit compactness binders, disjointness,
probability domain, same-list quantifier order, actual scalar integral, and
every-point exterior error bound are faithful. No extra assumption, omitted
quantifier, hidden weakening, or unreported strengthening was found.

All six independently printed axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`, with universe annotations. The author
reported a full checker PASS for the frozen source. This review does not
perform trusted-core promotion or replace the next full project gate.

The module establishes simultaneous norm approximation on the two specified
observation domains. It supplies no capacity or equilibrium premise and does
not establish the central density theorem, the positive perturbation, or final
targets `E1040-CAP1` and `E1040-FULL`.
