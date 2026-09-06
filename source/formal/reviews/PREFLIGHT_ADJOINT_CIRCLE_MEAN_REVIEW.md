# Independent correspondence review: AdjointCircleMean

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/AdjointCircleMean.lean`, SHA-256
`9bc8f86da6790f2767a3d5f762e0f437e96825ffe853cba720587c25d1d73730`.
Prerequisite `CircleMean.lean` is frozen at SHA-256
`b58428d24b28b567d9352896661e977185aee3fd8a83672bee5523fd9cd7c298`.
The author, number_theory_scout, confirmed a full checker PASS before freezing
both files. This reviewer did not edit the mathematical sources.

The review compares the complete theorem and proof, its manifest statement,
the actual adjoint-potential definition, the previously reviewed circle-mean
theorem, and the pinned Mathlib definitions of circle averaging and subtype
comap integration. A separate exact signature and axiom print run exited 0;
its log is `formal/.audit/preflight-adjoint-circle-mean.log`. The frozen source
hash was rechecked after that run. The binding is in
`preflight-adjoint-circle-mean-bindings.json`.

## Exact mathematical statement

The sole declaration, `Erdos1040.circleAverage_adjointAreaPotential`, quantifies
over every compact planar set K and every real L2 density h for planar Lebesgue
measure restricted to K. It quantifies over every real radius R with the two
explicit hypotheses `0 < R` and `norm(z) < R` for every z in K. The circle is
centered at zero. The conclusion is

`circleAverage(adjointAreaPotential h, 0, R) = (integral_K h darea) * log R`.

The enclosing condition is strictly less than R, not a closed-disk condition.
Together with compactness this supplies the positive separation needed by the
prerequisite's bounded logarithmic kernel and Fubini argument. Positivity of R
makes R the actual geometric radius and makes `log R` consistent with that
radius. There is no hidden assumption that R is one, exceeds one, or is a
particular enclosing radius.

The total mass is the signed real integral of h. It is not the integral of
its absolute value, its L2 norm, a source probability mass, or an integral
against arc length. No positivity or zero-mass premise on h is introduced.

## Finite mass and the subtype measure

The proof defines the measure on subtype K by comapping ordinary planar volume
along the subtype inclusion. Since compact K is measurable, this is exactly
the measure corresponding to restricted planar volume. It is not a comap
along an inverse map or a probability normalization.

The continuous measurable embedding of K into the plane transfers finiteness
on compact sets to the comap measure. Compactness of the subtype then supplies
the finite-measure instance required by the source circle-mean theorem.
Separately, compactness gives finite restricted planar volume on K. Thus the
existing real L2 membership of h implies L1 integrability there. The checked
`integrableOn_iff_comap_subtypeVal` equivalence transports this exact
integrability statement to the subtype measure.

Consequently h has a genuine finite signed mass under both presentations.
Accessing h through its Lp representative does not introduce a new pointwise
assumption: almost-everywhere equivalent representatives give the same
restricted-area and subtype integrals. Values outside K cannot affect them.

## Conversion of the actual potential and its mean

For each complex observation w, the pinned theorem `integral_subtype_comap`
identifies the subtype integral of
`h(z) * log(norm(w-z))` with the integral of that same function over K for
ordinary planar volume. The proof uses this identity for every w and obtains
equality of the entire potential functions. Hence the circle-average theorem
is applied to the actual `adjointAreaPotential` from its existing integral
definition, not an unrelated function or an assumed potential representation.
The same subtype-integral identity converts the source mass back to
`integral_K h darea` on the right side. There is no double restriction or
change of area normalization.

Mathlib's `Real.circleAverage` is exactly the normalized scalar angular mean
`(2*pi)^(-1) * integral_0^(2*pi) f(R*exp(i*theta)) dtheta` for center zero.
It is not the complex contour integral with respect to dz, and it introduces
no missing factor of R. The preceding `CircleMean` development proves absolute
integrability of the angle/source product, justifies interchange of integrals,
and proves circle integrability under these same enclosing hypotheses. Thus
this result does not exploit the default zero value assigned to a
non-circle-integrable function. The adjoint module also independently
establishes integrability of its actual potential integrand at all sources.

## Outcome and scope

The exact printed signature agrees with the manifest statement. Compactness,
the L2 density space, strict enclosure, positive radius, origin center,
ordinary normalized circle mean, and restricted-area signed mass are all
preserved. Empty or zero-area compact sets are allowed and cause no mismatch.
No extra assumption, omitted quantifier, changed measure, hidden weakening,
or unreported strengthening was found.

The independently printed axiom list contains only `propext`,
`Classical.choice`, and `Quot.sound`, with universe annotations. The author
reported the full checker PASS for the frozen source. This review provides
version-bound correspondence status only and performs no trusted-core
promotion. The final whole-project gate remains the parent's responsibility.

The theorem is a mass/circle-mean identity. It does not prove mass zero,
exterior harmonic uniqueness, the annihilator-density result, an equilibrium
or capacity statement, or either final target `E1040-CAP1` and `E1040-FULL`.
