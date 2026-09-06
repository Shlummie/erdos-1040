# Independent correspondence review of SourcePotential

Reviewer: combinatorics_scout. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/SourcePotential.lean`, SHA-256
`4de9d0b75283f0707d6e52c2170f211bc0c2347bd482e6fb7e3fb1e7a9eca652`.
The root agent authored this source; this reviewer did not edit its proofs.
The review compared all five declarations with their exact printed signatures
and natural-language statements in `formal/.audit/report.json`, whose checked
timestamp was `2026-09-05T04:08:19.488774+00:00`. That report passed the complete
machine checks while correctly recording the main target as incomplete.
Per-declaration version bindings are in
`combinatorics-source-potential-bindings.json`.

## Exact statements and correspondence

1. `integral_sq_log_norm_sub_eq_norm_areaLogKernel_sq` quantifies over every
   compact complex observation set K and every complex source w. Its left
   side is the integral of the square of the real logarithm of the complex
   distance for planar Lebesgue measure restricted to K. Its right side is
   the squared norm of the corresponding real area-L2 class. This is the
   asserted identity, with no disjointness, boundary-regularity, or
   nonzero-area assumption. The proof uses the already established kernel
   L2 membership and its almost-everywhere representative identity.

2. `integrable_log_norm_sub_prod` uses arbitrary compact complex S and K,
   an arbitrary measure on the source subtype S, and an explicit
   `IsFiniteMeasure` instance. It proves Bochner integrability of the real
   logarithmic kernel for the product of this source measure and restricted
   planar area. Thus it proves actual joint absolute integrability, rather
   than assuming Fubini or only separately checking source slices. Probability
   normalization, absolute continuity of the source measure, disjointness,
   and boundary smoothness are not assumptions. Compactness of S and kernel
   norm continuity bound the integrated squared kernel; finite source mass
   and finite area then give joint L1 integrability. The latter finiteness is
   derived from compact K, not an omitted hypothesis.

3. `areaLogKernel_integral_ae_eq_source_potential` identifies the representative
   of the Bochner integral of the L2-valued source kernel with the real
   source-variable logarithmic integral, almost everywhere for
   `volume.restrict K`. The source measure is again arbitrary and finite on
   subtype S; this is not a statement about unrestricted source points or
   an unexpressed support predicate. The conclusion is area-almost-everywhere
   equality, not pointwise equality on K or continuity of the scalar
   potential. The proof obtains equality of integrals over every measurable
   test set of finite restricted area. It represents those test integrals
   by legitimate L2 inner products with indicator classes and invokes Fubini
   using the previously proved joint integrability. It does not treat
   point evaluation as a continuous linear functional on L2.

4. `memLp_source_potential` proves real L2 membership of that same actual
   totalized source integral for restricted planar area. It transfers
   membership across the established almost-everywhere equality. No new
   regularity hypothesis or pointwise finiteness assertion is introduced.

5. `source_potential_toLp_eq_integral_areaLogKernel` proves equality of the
   L2 class constructed from the scalar source integral with the Bochner
   integral of `areaLogKernel`. Both sides have exactly the same area measure
   and exponent 2. The membership proof and source-set compactness remain
   explicit in the dependent signature; they are not new mathematical
   assumptions. This equality is the requested interface for transporting
   Banach-valued approximation to the actual source-potential class.

## Measure and exceptional-set limits

All logarithms use the project's established positive-log convention,
`Real.log` applied to complex distance, with `Real.log 0 = 0`. All scalar
source integrals use Lean's real Bochner integral. Joint absolute
integrability ensures an absolutely integrable source slice at almost every
area observation. These declarations do not assert that the source slice is
integrable at every observation, that a classical extended-real potential
is finite everywhere, or that its value at source atoms is unchanged by
totalization. The almost-everywhere and L2 statements are exactly the
appropriate scope; an everywhere or classical-boundary interpretation would
require further work.

The results allow overlapping S and K, atoms, zero source mass, empty compact
sets, and arbitrary compact geometry. The source measure itself is a finite
nonnegative measure, as expressed by `Measure`; this module does not yet
introduce a signed-density parameter. Those boundaries agree with all five
manifest statements and do not weaken their asserted scope.

No extra assumption, omitted quantifier, domain change, weakening, or
strengthening was found between these exact signatures and their registered
natural-language statements. Their printed axiom lists contain only
`propext`, `Classical.choice`, and `Quot.sound`. Kernel validity and this
independent correspondence review are separate checks. These five supporting
results do not establish E1040-CAP1, E1040-FULL, equilibrium theory, or any
P versus NP implication.
