# Independent correspondence review: GeometricDiameter

Reviewer: `formalization_preflight` (not the source author). Machine evidence: `formal/admissions/2026-09-05-energy-diameter-pre-admission-203.json`, checked 2026-09-05T05:48:38.649762+00:00, all 203 declarations machine PASS, main targets incomplete. I read the entire source and its current natural-language statements, checked each definition body where present, and independently printed every exact signature and axiom list. The combined 42 fresh messages for these three modules match the immutable snapshot exactly. Log: `formal/.audit/preflight-geometric-empirical-energy.log`, Lean exit 0. All declarations depend only on the standard allowed logical axioms.

Frozen source SHA-256: `bd0f8f27726fb5ef979c5e47f08a789d201144218b0045e91d1d908ab5a542a7`.

| Declaration | Exact correspondence review |
|---|---|
| `unorderedPairProduct` | Product of ordinary Euclidean distances over exactly the index pairs i<j. Repeated roots give a zero factor when the repeated indices form a pair; empty products are one. |
| `geometricMeanSeparation` | The exponent is the real number 2/(N*(N-1)), with subtraction in the reals. At orders zero and one the denominator is zero and totalization makes the exponent zero; those orders are excluded from the transfinite sequence. |
| `finiteDiameter` | Extended nonnegative supremum over all tuples in the actual source subtype, retaining unbounded values. No energy predicate, distinctness assumption, or ambient enlargement replaces the geometric definition. |
| `transfiniteDiameter` | Extended infimum of orders n+2. This is a geometric infimum definition; separate antitonicity and convergence results remain necessary to identify it with the classical decreasing-limit presentation. The registered statement explicitly retains that obligation. |
| `continuous_unorderedPairProduct` | Every natural order, including empty and singleton tuples; finite products of continuous distances. |
| `continuous_geometricMeanSeparation` | Explicit N>=2 makes the exponent positive, so continuity includes colliding tuples where the product is zero. |
| `finiteDiameter_eq_max_of_compact` | Nonempty compact source and N>=2; the finite source-tuple product space is compact, and an actual tuple attains the real continuous maximum and hence the ENNReal supremum. |
| `finiteDiameter_empty` | Every positive order has no tuple into the empty source, so its extended supremum is zero. Order zero is correctly not included. |
| `transfiniteDiameter_empty` | Every order used in the infimum is positive; the result is zero. |
| `finiteDiameter_lt_top_of_compact` | Compact sources may be empty. The proof splits empty and nonempty cases and proves finiteness for N>=2. |
| `exists_distinct_configuration_of_one_le_transfiniteDiameter` | The infimum bound forces every required finite maximum to be at least one. Positive exponent yields pair product>=1; no pair distance can be zero, so the original-source tuple is injective. Nonemptiness and distinctness are derived. |
| `sum_offDiag_log_dist_eq_twice_log_unorderedPairProduct` | The ordered off-diagonal pairs split into i<j and j<i, paired by symmetry. Injectivity makes every logarithm argument nonzero. The equality also covers orders zero and one. Logarithm values themselves may be zero at distance one. |
| `exists_distinct_configuration_log_sum_nonneg` | Exact original-source injective tuple; the preceding ordered-sum identity and product>=1 yield the nonnegative logarithmic sum. |

One prose error was corrected during review: "logarithm factors are nonzero" was replaced by "logarithm arguments are nonzero." The parent applied that correction to the manifest and canonical rows. Its current statement hash is `6451dea3d43b7356943f7ba78068bd3726ee82948677f5059fc5bfa7c073c3c4`; source and exact Lean signature are unchanged. The bindings use this corrected statement hash and the saved source/signature hashes. The next full checker must validate that current binding.

No other extra hypothesis, omitted quantifier, altered source domain, exponent change, or hidden weakening was found relative to the thirteen registered statements. These declarations establish the geometric infimum API and its configuration consequence. This review does not certify the separate decreasing-limit correspondence, an equality with logarithmic capacity, or the final Erdős theorem. Bindings: `preflight-geometric-diameter-bindings.json`.
