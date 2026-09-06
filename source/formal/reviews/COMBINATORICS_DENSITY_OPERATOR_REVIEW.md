# Independent correspondence review of DensityOperator

Reviewer: combinatorics_scout. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/DensityOperator.lean`, SHA-256
`cc57dadc3704ac382a61be0555299aab8ddb14459d10262fd3a4244bfab29482`.
The root agent authored this source; this reviewer did not edit its proofs.
The review compares the source, the three registered natural-language
statements, and the exact printed signatures in the passing immutable report
`formal/admissions/2026-09-05-conditional-core-pre-admission.json` (119
declarations, checked 2026-09-05 04:43 UTC). Per-declaration source, signature,
and statement hashes are recorded in `combinatorics-density-operator-bindings.json`.

1. `boundedMeasurableDensities` is the real submodule of actual real functions
   on the source subtype S whose carrier predicate is measurability together
   with a finite pointwise real norm bound. It is not a quotient modulo the
   source measure, an essential-bound-only space, a complex vector space, or
   a positive-density cone. The definition proves closure under zero, addition,
   and real scalar multiplication from that exact predicate. S is arbitrary
   here; no compactness or nonemptiness assumption has been inserted. Allowing
   any real bound C is equivalent to an ordinary finite norm bound and handles
   an empty source subtype without an artificial positivity requirement.

2. `sourceDensityOperator` has compact complex source and observation sets
   S and K and an arbitrary finite nonnegative measure on subtype S. Its value
   is exactly the Bochner integral of the real density times the existing
   logarithmic area-L2 kernel, for planar Lebesgue measure restricted to K.
   This is a real linear map. Addition uses the already proved integrability
   of each bounded measurable density times the L2-valued kernel; scalar
   multiplication uses the integral's linearity. The declaration does not
   assume or assert boundedness of this operator for an unprovided domain
   norm, positivity of its arguments, probability normalization, or pointwise
   continuity of the scalar potential. All are outside its stated scope.

3. `exists_density_approx_of_annihilator` quantifies over every real area-L2
   target u on K. Its explicit conditional hypothesis says that each h
   orthogonal to all actual bounded measurable source-density potentials is
   orthogonal to u. Its conclusion supplies such an actual bounded measurable
   real density with Bochner potential at L2 distance strictly below every
   positive real tolerance. The proof identifies u with an element of the
   double orthogonal complement of the operator's range, uses the Hilbert
   double-complement/closure identity, and chooses an element of that range
   in the required metric ball. Real inner-product symmetry and the norm's
   symmetry are used with the correct orientation. Completeness and the
   relevant measure structure are supplied by the existing area-L2 space.

The last result is a conditional Hilbert-space criterion. It does not prove
its annihilator hypothesis for an equilibrium measure or a harmonic
polynomial, and is not the complete E1040-DENSITY lemma. Its hypothesis is
displayed faithfully in both the statement and the printed Lean signature;
it is not an untracked assumption or a main-target theorem. Conversely, its
conclusion has not been weakened to abstract range membership: it retains
the actual source function, its measurability, its pointwise bound, and the
actual source integral.

No extra assumption, omitted quantifier, domain change, weakening, or
strengthening was found relative to the three registered statements. The
immutable full-check report passes all machine checks and records only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound` for these
declarations. Kernel checking and this independent correspondence review are
separate gates. The report correctly leaves E1040-CAP1 and E1040-FULL
incomplete; these supporting declarations have no established P versus NP
implication.
