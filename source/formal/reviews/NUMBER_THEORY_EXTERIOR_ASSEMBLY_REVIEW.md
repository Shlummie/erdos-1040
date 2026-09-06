# Independent correspondence review of exterior positivity and support assembly

Reviewer: number_theory_scout. Date: 2026-09-05 UTC.

The root agent authored the reviewed proofs; this reviewer did not edit them.
The reviewed sources are:

- `formal/Erdos1040/ExteriorPositivity.lean`, SHA-256
  `ba29345fda8479dc4db855c6eea6ec7c9378d991b43d0360d8ffca8b11c362d7`;
- `formal/Erdos1040/NonnegativePotentialLemniscate.lean`, SHA-256
  `57e8297f00944ac37b4f59294d36087b194f2ef9efeb60dc0254b10203ead70c`.

The two exterior signatures were first checked against immutable PASS207.
All three canonical statements, exact printed signatures, source hashes,
and axiom lists were then checked in the immutable passing report
`formal/admissions/2026-09-05-global-frostman-pre-admission-212.json`,
SHA-256 `91dd9a2f40b5a491af1ba6268ab7f4be0b75359523f69897dd1dfd7bc71e4191`.
Its recorded check time is `2026-09-04T23:08:05.657605-07:00`.
Per-declaration bindings are in
`formal/reviews/number-theory-exterior-assembly-bindings.json`.

## Exact statements and proof correspondence

1. `tendsto_log_source_potential_atTop` proves that the actual positive-log
   source integral for every compact complex source probability tends to
   positive infinity along the cocompact filter on the plane. The previously
   proved signed-source asymptotic is specialized to constant density one;
   the probability mass is exactly one. Adding the logarithm of the norm,
   which tends to infinity, supplies the stated conclusion. No minimization,
   finite-energy, non-atomicity, support regularity, or global potential-bound
   assumption has been inserted. Integrability is already proved in the
   far exterior used by the asymptotic, so totalization of the real integral
   does not manufacture the limiting value.

2. `log_source_potential_pos_on_hull_compl` assumes compact S and K, a
   probability on subtype S, its actual ambient support contained in K,
   preconnected complement of K, and everywhere nonnegativity of its actual
   positive-log source potential. It concludes strict positivity at every
   point outside K. In particular, it does not require the entire source S
   to lie in K; support containment is sufficient and is exactly what the
   printed signature says. SourceSupport proves harmonicity outside the
   actual support, which restricts to the complement of K. A hypothetical
   zero there is a maximum of the negative potential. The checked strong
   maximum principle forces zero throughout that complement, contradicting
   the first theorem at a point outside compact K. Connectedness, sign,
   growth, and the direction of the support inclusion are used correctly.
   There is no boundary-limit argument, polar exception, zero-on-K
   requirement, assumed exterior strictness, or hidden equilibrium theorem.

3. `hasArbitrarilySmallLemniscates_of_nonnegative_source_potential` has only
   compact S, a probability mu on S, and everywhere nonnegativity of the
   actual positive-log source integral as hypotheses. It constructs the
   compact nonempty ambient support T, the probability transported to T,
   and a compact containing set K with preconnected complement and frontier
   contained in T. Exact equality of the two pushed-forward measures gives
   equality of the actual source integrals and identifies the transported
   probability's ambient support with the original T. Thus the entire
   frontier of K lies in that support, not merely almost everywhere there.
   The second theorem supplies strict exterior positivity. These proved
   data meet every hypothesis of the reviewed ConditionalLemniscate theorem.

The resulting roots first lie in T. The proved inclusion T subset S and
the exact monotonicity lemma preserve the same roots and area while making
them permitted roots in S. Expanding HasArbitrarilySmallLemniscates retains
every positive real tolerance, an actual positive finite degree, a finite
root list with multiplicities allowed, and planar Lebesgue area of the
entire strict unit lemniscate below the tolerance. No roots are placed in
the filled hull outside the original source, no exterior area is discarded,
and no polynomial degree or runtime bound is asserted.

The third theorem therefore removes all caller-supplied hull, frontier,
connected-exterior and strict-positivity hypotheses. Its remaining global
nonnegativity hypothesis is explicit and is not itself proved by that
theorem. In the larger program it can be supplied by the separately checked
finite-minimizer global bound and the finite-energy estimate. That final
composition and correspondence with the original geometric or capacity
hypothesis remain separate declarations and reviews.

No additional assumption, missing quantifier, domain change, hidden weakening,
or strengthening was found relative to these three canonical statements.
The immutable PASS212 report records a passing source scan, pinned build,
dependency checks, and only `propext`, `Classical.choice`, and `Quot.sound`
for each theorem. This review supplies the independent version-bound
correspondence gate; the root owns canonical admission. The referenced
snapshot still marks E1040-CAP1 and E1040-FULL incomplete and does not certify
the original problem or any P versus NP implication.
