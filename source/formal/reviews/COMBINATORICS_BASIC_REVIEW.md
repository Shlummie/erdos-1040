# Independent correspondence review of Basic

Reviewer: combinatorics_scout. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/Basic.lean`, SHA-256
`8ad9a2349f6cc49d3042bcb01c67bc63c09286655df5d48bb2afa028cbbc3dc7`.
The source was authored by the root agent, not this reviewer. The review used
the current source, the natural-language manifest entries, and separately
printed Lean signatures and axiom lists. The print run completed with exit 0;
its output is `formal/.audit/combinatorics-basic-unbounded.log`. Per-declaration
signature and statement hashes are in `combinatorics-basic-bindings.json`.

## Findings

- `rootPolynomial` quantifies over every natural `n` and every `Fin n`-indexed
  list of complex numbers. Its body is exactly the finite product of `X - C r`.
  Indexing by a list allows repeated roots and does not silently impose
  distinctness. Allowing `n = 0` in this supporting definition is faithful;
  the final small-area predicate separately requires positive `n`.
- `unitLemniscate` is the subset of the full complex plane on which the norm
  of the actual product of `z - roots i` is strictly less than 1. There is no
  real-line restriction, non-strict boundary substitution, or probability
  measure replacing area.
- `HasArbitrarilySmallLemniscates` has the order of quantifiers required by
  the source: for every real epsilon greater than zero, there exists a
  natural `n > 0` and a list of `n` roots, every one in the original set,
  whose strict unit lemniscate has volume strictly below epsilon. The list
  and degree may depend on epsilon. The positive-degree conjunct excludes
  the constant polynomial 1.
- `rootPolynomial_monic` proves monicity for every list, with no omitted
  nonzero or distinctness hypothesis.
- `rootPolynomial_eval` proves equality with the root product at every
  complex evaluation point. This connects the set definition to the actual
  polynomial, including evaluations at roots.
- `rootPolynomial_natDegree` proves that the polynomial's natural degree is
  exactly the indexing natural number, including the empty-list case. Together
  with the predicate's `0 < n`, this is the intended positive polynomial degree.
- `rootPolynomial_isRoot_iff` proves both directions: a complex number is a
  root of the polynomial if and only if it equals some listed root. Thus the
  predicate's membership condition accounts for all polynomial roots and
  does not omit extra roots.

The volume instance is the standard complex-plane planar Lebesgue measure.
In the same pinned dependency environment, `Complex.volume_ball` evaluates
the volume of a radius-r complex ball as `ofReal r ^ 2 * NNReal.pi`, confirming
the intended area normalization. `ENNReal.ofReal epsilon` is faithful for the
explicitly positive tolerance; it does not truncate a negative tolerance.

No extra assumption, domain change, omitted quantifier, weakening, or
strengthening was found in these seven declaration-to-statement comparisons.
Their printed axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`, with universe annotations. That observation is distinct from
the correspondence review and does not replace the full project verifier.

This review does not establish `E1040-CAP1` or `E1040-FULL`. It also does not
independently review `Unbounded.lean`, which this reviewer authored. The same
print log includes those four declarations for transparent handoff to a
different reviewer, but their presence is not an independent admission review.
