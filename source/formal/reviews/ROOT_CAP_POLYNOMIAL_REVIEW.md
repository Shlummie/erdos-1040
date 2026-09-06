# Independent correspondence review: CapPolynomial

Reviewer root; author formalization_preflight; 2026-09-05 UTC.
Read all ten exact printed signatures and source independently. Reviewed
source f6c45f7ff19ce0a39946dfc05a24d5312fbf227482d58abd60e72171eb2d87d7.
Bindings: root-cap-polynomial-bindings.json. Machine source: immutable
2026-09-05-analytic-bridges-pre-admission.json.

The capSet definition is exactly norm(z)<=M and a<=abs(Im z). Compactness and
the explicit theorem-instance cover every real M,a, including empty cases.
cap_denominator_ne_zero requires only a>0, any real pole b, and cap membership.
capResolvent is the actual continuous reciprocal (b-z)^(-1) on those caps;
its source definition, not only its printed result type, was inspected.

The general closed-subalgebra lemma requires a compact domain, f in the
algebra with uniform norm<1, and the exact identity g*(1-f)=1. Its conclusion
g in A is proved from checked geometric summation and closedness. It does not
assume g in A or an approximation theorem. The inverse identities for the
actual resolvents are proved by nonzero-denominator algebra in both callers.

The far-pole lemma assumes 0<a, 0<M, M<B. The one-step lemma assumes 0<a,
real b,h, |h|<a, and existing uniform-closure membership for the pole b; it
proves membership for b-h. No positivity of h or M is silently needed in this
step. Imaginary separation gives uniform norm<1, justified by compactness.
Finitely many steps starting at B=N*a/2 with N>=4M/a prove the zero-pole
membership for 0<a,0<M. Negative intermediate poles would also be permitted.

The final theorem has exactly 0<a<M and produces an actual complex polynomial
Q, Q.eval 0=1, and norm(Q.eval z)<1/4 for every norm(z)<=M and a<=abs(Im z).
Uniform closure supplies a polynomial approximation at tolerance 1/(8M),
and Q=1+X*P supplies the exact origin value. The reciprocal cancellation uses
z!=0 established from a>0. The proof actually bounds the cap norm below 1/8.
The closed cap boundaries are included and both signs of Im z are covered.

This is the candidate's precise separator, with a different elementary proof
than the optional fixed-degree recurrence in the research note. The Lean
theorem does not assert that recurrence, a degree bound, real coefficients,
rotation selection, or mean-zero area control. These are not omitted parts
of the exact registered statement. No general Runge/Mergelyan assumption,
custom axiom, or conclusion-shaped premise is used. Only the three standard
logical axioms appear. No correspondence discrepancy found.
