# Countable-source correspondence review

Reviewed 2026-09-05 19:05:26 UTC by `cold_analytic`. The installed module was
authored by another agent. **No mathematical or correspondence defect found
in the eight reviewed declarations.** This is an agent review of source,
printed signatures, registered statements, and selected dependency interfaces.
It is separate from kernel checking and is not human peer review.

The reviewed source is [CountableSources.lean](../Erdos1040/CountableSources.lean),
SHA-256 `95663c2dd64194040b067955857e6724fcaadef8316d3ca315978595e81a9596`.
The companion [bindings](cold-countable-sources-bindings-20260905.json) bind
each raw source-file hash, exact printed-signature UTF-8 hash, and exact
registered-source-statement UTF-8 hash. No proof, manifest, or canonical
research record was edited for this review.

## Machine evidence and admission boundary

The inspected full checker record is `formal/.audit/report.json`, checked at
2026-09-05T19:03:17.475803+00:00, SHA-256
`e0d517065c7f077bba2633e9eb12d46cb23ece2e62acef4f1dca3c41da3bda1b`.
It records build and audit exit code zero, `source_scan_pass: true`,
`machine_checks_pass: true`, 271 tracked declarations, and no machine errors.
The build log records 8,759 jobs. All eight reviewed declarations have passing
axiom audits and only `propext`, `Classical.choice`, and `Quot.sound`.

That report still has `main_target_complete: false` and 31 pending new
correspondence reviews, including these eight. This review supplies eight
version-bound correspondence decisions; it does not itself update admission
or assert completion of the expanded target chain. The root agent must attach
the reviews and rerun the documented gate.

## Declaration correspondence

All names below have the prefix `Erdos1040.` and the stable registered claim
ID `E1040-CAPACITY-ONLY`.

| Declaration | Exact mathematical assessment |
| --- | --- |
| `nonnegativeLogEnergy_eq_top_of_countable` | Quantifies over every countable complex source, every positive real scale, and every actual probability on the source subtype. The conclusion is equality to positive infinity in the extended nonnegative reals, with no compactness, distance-bound, or minimizer assumption. |
| `logarithmicCapacity_eq_zero_of_countable` | Establishes zero for the existing literal Robin-infimum definition on every countable source. Its registered statement explicitly limits classical-capacity interpretation to bounded or compact sources; it does not introduce an unbounded-capacity convention. |
| `smallCountableSource` | The body is exactly zero inserted into the range of the complex reciprocal of the natural number `n + 4`, for every natural `n`. The first reciprocal is `1/4`, and zero is included as the limiting point. |
| `smallCountableSource_countable` | Uses countability of a natural-indexed range and preservation under inserting zero. The signature is about the exact defined set, without an additional hypothesis. |
| `smallCountableSource_isCompact` | The complex reciprocals tend to zero, and the range with that actual limit inserted is compact. The topology is the ordinary complex topology. Compactness is proved, not assumed. |
| `smallCountableSource_infinite` | Reciprocal equality implies denominator equality by the involution of complex inversion; injectivity of natural casting and cancellation of four give equality of indices. The infinite range remains infinite after inserting zero. |
| `smallCountableSource_subset_closedBall` | Every reciprocal has norm `1/(n+4)`, at most `1/4`, and zero also satisfies the bound. The radius is real, the center complex zero, and the ball is closed. The included endpoint `1/4` is handled by a non-strict inequality. |
| `zero_mem_smallCountableSource` | Zero is literally the inserted element. No nonemptiness or membership premise is supplied by the caller. |

## Energy and capacity checks

The energy proof correctly retains the singular diagonal. It argues by
contradiction from finite extended energy, using the admitted
`nullSingletonClass_of_finite_nonnegativeLogEnergy` to make every source
singleton null. The entire countable source subtype would then have measure
zero, contradicting the probability mass one. This proves every such energy
is positive infinity; it never applies real `log 0` or `toReal` to discard
infinity. Empty sources cause no counterexample: no probability exists on an
empty subtype, so the probability-quantified statement is vacuous there.

For capacity, the canonical scale is at least one and hence positive. Every
energy in the Robin infimum is infinity; subtracting the finite real logarithm
of that scale leaves positive infinity. The infimum, including an empty
probability index, is therefore positive infinity, and its negative
exponential is zero. No infinity-minus-infinity operation or equilibrium
existence assertion enters this argument. Classical interpretation is used
for the explicit source only after its compactness has been established.

The relevant existing definitions and finite-energy premise were inspected in
[LogarithmicCapacity.lean](../Erdos1040/LogarithmicCapacity.lean),
[LogEnergy.lean](../Erdos1040/LogEnergy.lean), and
[LogEnergyIntegrability.lean](../Erdos1040/LogEnergyIntegrability.lean).
Selected pinned Mathlib interfaces checked were
`Set.Countable.measure_zero`, `tendsto_one_div_atTop_nhds_zero_nat`, and
`Tendsto.isCompact_insert_range`.

No extra assumption, omitted quantifier, hidden domain restriction, or
weakened conclusion was found relative to the eight registered statements.
These declarations alone establish neither the area-infimum separation nor
the zero geometric transfinite diameter; those are separate modules and
reviews. No novelty, publication, or P versus NP conclusion follows here.
