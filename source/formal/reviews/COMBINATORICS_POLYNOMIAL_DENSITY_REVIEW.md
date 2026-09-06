# Independent correspondence review of PolynomialDensity

Reviewer: combinatorics_scout. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/PolynomialDensity.lean`, SHA-256
`7dbd5866453feb2c29bf8a12d1c4dbcc66e743fd584668905a0a85c824711fe3`.
The root agent authored this source; this reviewer did not edit its proofs.
This review compares the source, the three natural-language statements, and
the exact printed signatures in the passing immutable 122-declaration report
`formal/admissions/2026-09-05-polynomial-density-pre-admission.json`.
Per-declaration source, signature, and statement hashes are recorded in
`combinatorics-polynomial-density-bindings.json`.

1. `memLp_re_polynomial` proves real L2 membership of the actual real part of
   any complex polynomial on any compact complex observation set K, with
   planar Lebesgue measure restricted to K. Compactness supplies finite area
   and a uniform bound for this continuous real function. No source measure,
   nonempty interior, positive area, boundary smoothness, or polynomial degree
   restriction has been inserted.

2. `inner_re_polynomial_toLp` identifies the real Hilbert inner product of
   any area-L2 class h with the class of Re p with the actual integral over K
   of the representative h times Re p. Both sides use the same planar-area
   measure and the exponent 2. The proof uses the established almost-everywhere
   representative identity and the real L2 inner-product formula. This is
   neither pointwise evaluation continuity nor an asserted choice-independent
   pointwise value of h; the integral is invariant under changes on null sets.

3. `exists_density_approx_re_polynomial` assumes compact complex S and K,
   S contained in K, a probability measure on subtype S, preconnectedness of
   the complement of K, containment of the frontier of K in the support of
   the source measure pushed forward by inclusion, and global nonnegativity
   of the actual real logarithmic source potential. For every complex
   polynomial with zero real source mean and every positive tolerance, it
   produces an actual measurable real source density with a finite pointwise
   norm bound whose Bochner logarithmic potential approximates Re p in
   restricted area-L2 norm.

The third theorem discharges the abstract annihilator implication using the
previously proved exact area-polynomial pairing identity from
`AdjointUniqueness`; zero source mean makes that pairing vanish. It then
applies the reviewed Hilbert-space closure criterion from `DensityOperator`.
The annihilator conclusion is therefore proved rather than inserted as a
new hypothesis. The resulting approximation is by the actual density and
actual Bochner source integral. The existing `SourceDensity` correspondence
identifies that class with the scalar signed logarithmic potential almost
everywhere; the theorem does not assert pointwise or uniform approximation.

All geometric and potential assumptions listed above are present in the
printed signature and the natural-language statement. In particular,
`hpotential` is an everywhere assertion about the established totalized real
Bochner integral, not an unexpressed classical extended-real or
quasi-everywhere convention. This conditional result does not construct an
equilibrium probability or show that capacity one provides those assumptions.
It also does not assert the eventual positivity of a perturbed probability,
the exterior collar estimates, or existence of the final polynomial roots.

No extra assumption, omitted quantifier, domain change, weakening, or
strengthening was found relative to the three registered statements. The
immutable report passes all machine checks and records only `propext`,
`Classical.choice`, and `Quot.sound` for these declarations. Those checks and
this separate correspondence review establish their supporting scope only.
The report leaves E1040-CAP1 and E1040-FULL incomplete, and no P versus NP
implication is established.
