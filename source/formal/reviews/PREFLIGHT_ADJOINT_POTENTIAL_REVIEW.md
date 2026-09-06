# Independent correspondence review: AdjointPotential

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/AdjointPotential.lean`, SHA-256
`74fe89f6614e40d2bc6aa1449e2ab8d559e933f1ef813a579a4da74464602c2e`.
The author, the root agent, froze the file after successful compilation. This
reviewer did not edit it. The review compares its complete definitions and
proofs, the five manifest statements, the independently reviewed logarithmic
kernel class and continuity result, and separately printed exact signatures.
The independent print run exited 0 and its output is
`formal/.audit/preflight-adjoint-potential.log`. The frozen source hash was
checked again after that run. Per-declaration review bindings are in
`preflight-adjoint-potential-bindings.json`.

## Actual integral and class conventions

`adjointAreaPotential` is defined by the real integral over K of
`h(z) * Real.log (norm (w-z))`. The integral uses planar Lebesgue measure
restricted to K. The density h belongs to the real L2 space for this same
restricted measure and is accessed through its representative. There is no
second restriction or unrelated probability measure. Almost-everywhere
changes of the density do not change the integral: the kernel is real-valued
everywhere under the explicitly stated totalized logarithm convention.

The norm symmetry `norm(w-z) = norm(z-w)` faithfully connects this expression
to `areaLogKernel`. The definition's compactness proof parameter records the
stated compact domain; it does not alter the integrand or conceal an arbitrary
potential function. Its role is not to assume the desired continuity result.

`integrable_adjointAreaPotential` proves integrability of the actual product
for every compact K, every such L2 density, and every complex w. It uses
integrability of the product of two real L2 functions and the almost-everywhere
representative of `areaLogKernel`. Thus the defined integral is an actual
finite integral for each w. The argument does not obtain a spurious continuous
zero function by relying on the integral convention for a nonintegrable
function. It remains valid when w lies in K; the totalized value at z=w affects
only a singleton of area zero.

`adjointAreaPotential_eq_inner` proves equality of that integral with the real
L2 inner product of h and `areaLogKernel`. It rewrites the existing definition
of the L2 inner product and proves equality of the integrands almost everywhere.
In the real inner product, multiplication order is immaterial, and norm
symmetry accounts for the reversed subtraction order. It does not define the
potential to be an abstract inner product and omit the integral correspondence.
Both the source and printed signature preserve all compactness, density, and
source quantifiers.

## Continuity and support

`continuous_adjointAreaPotential` composes the already proved full L2 norm
continuity of `areaLogKernel` with the continuous real inner-product functional
against h, and then uses the actual integral identity. Its conclusion is
ordinary continuity on the entire complex plane, including points in K and
irregular positive-area boundaries. No exclusion of the singular diagonal,
boundary-nullness, smoothness, connectedness, boundedness of h, positivity,
or zero-mass condition is added. Empty and zero-area compact sets are also
included. This is continuity for an area-L2 density on a compact set; it is
not a continuity claim for arbitrary singular-measure logarithmic potentials.

`adjointAreaPotential_zero_on_support_of_ae` quantifies over an arbitrary
measure nu on the complex plane. Its explicit hypothesis is that this
continuous potential equals zero nu-almost everywhere. The zero set is closed,
so that hypothesis places the whole topological support of nu in the zero set.
Equivalently, a nonzero value at a support point would, by continuity, give a
neighborhood contained in the nonzero set, contradicting the almost-everywhere
vanishing and the support definition.

No probability, finite-measure, support-subset-K, or relation between nu and
the area measure is hidden in this theorem. Its signature retains the full
almost-everywhere vanishing premise. That premise is not proved here from an
annihilator, equilibrium measure, or orthogonality condition, and the theorem
must remain conditional until the relevant preceding argument is supplied.

## Outcome and scope

All five exact signatures match their manifest statements. The actual integral,
its integrability, its inner-product correspondence, global continuity, and
the conditional support extension pass independent mathematical review. No
extra assumption, omitted quantifier, changed area convention, hidden weakening,
or strengthening relative to those statements was found.

All five separately printed axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`, with universe annotations. The compiler
also produced proof-parameter congruence helpers under tracked definitions;
their exact `.congr_simp` suffix, absence of a source declaration range, safe
kernel status, and standard-only axiom dependencies were checked before the
verifier recognized that helper form. They introduce no new source assumption.

The review bindings authorize version-bound correspondence status only. No
trusted-core promotion was performed by this reviewer; the full project gate
remains separate. These theorems advance the continuous-adjoint portion of
the density argument but do not establish its almost-everywhere annihilation
premise, exterior harmonic uniqueness, moment comparison, or final capacity-one
and complete targets `E1040-CAP1` and `E1040-FULL`.
