# Independent correspondence review: AreaTransfer

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/AreaTransfer.lean`, SHA-256
`624c76235c9a5cff3f96ae265ab9c2f2c5c573dcbd912112d08c7deded36da11`.
The source was authored by the root agent, not this reviewer. This review
compares the complete source, the manifest statement, the candidate's
Chebyshev sign-transfer argument, and the separately printed exact signature.
The independent print command exited successfully; its output is
`formal/.audit/preflight-area-transfer.log`. Signature and statement hash
bindings appear in `preflight-area-transfer-bindings.json`.

The sole declaration is
`Erdos1040.measure_neg_le_margin_add_sq_eLpNorm`, claim
`E1040-AREA-TRANSFER`. It is a conditional supporting theorem.

## Exact statement

The signature quantifies over every measure on the complex plane and every
pair of real-valued functions. It explicitly requires almost-everywhere strong
measurability of their difference for that measure. It then quantifies over
every strictly positive nonnegative-real margin. Its conclusion is

`measure {f < 0} <= measure {g < delta} + delta^(-2) * eLpNorm(f-g,2)^2`.

The negative set and low-margin set both use strict inequalities. The tail
set used internally has a non-strict error threshold. The coefficient is the
square of the inverse of the ENNReal embedding of the positive margin. This
equals division by the square of the finite positive real margin.

No finite-measure, probability-measure, or separate measurability assumption
on `f` and `g` is introduced. This is legitimate: containment and measure
subadditivity bound arbitrary sets, and the Markov estimate requires only
the explicitly stated almost-everywhere measurability of the difference.
The result applies in particular to planar Lebesgue measure and its compact
restrictions, but does not silently specialize an arbitrary-measure claim.

The L2 quantity is `eLpNorm`, so its codomain is the extended nonnegative
reals and it may equal infinity. The initial natural-language wording was
clarified during review to say "extended nonnegative-real L2 seminorm
(possibly infinite)" before its final statement hash was bound. If that norm
is infinite, the theorem remains true but does not provide a useful finite
error estimate. The existence of approximants with a finite small norm remains
a distinct research dependency. The theorem makes no integrability claim.

## Mathematical check

If `f(z) < 0` while `g(z) >= delta`, then
`abs(f(z)-g(z)) >= delta`. Thus the negative set of `f` lies in the union of
the low-margin set of `g` and the error tail. The checked L2 Markov inequality
bounds that tail by `delta^(-2) * eLpNorm(f-g,2)^2`. Measure monotonicity and
subadditivity give the stated conclusion with the unchanged low-margin term.
This argument has no assumption containing the desired conclusion and no
existential approximation or positive-potential premise hidden in a definition.

The printed signature exactly matches the clarified manifest statement.
No omitted quantifier, changed domain, extra assumption, hidden weakening, or
change of strictness was found. Its general measure domain is an explicit
generalization of the particular planar-area application in the candidate.

The separate printed axiom list contains only `propext`, `Classical.choice`,
and `Quot.sound`, with universe annotations. This correspondence review does
not replace the full project build, dependency audit, source scan, or axiom
gate. No trusted-core promotion was performed by this reviewer.

The result transfers an already available margin and approximation error to
an area bound. It does not construct those inputs, define logarithmic capacity,
establish the central density theorem, or resolve `E1040-CAP1` or `E1040-FULL`.
