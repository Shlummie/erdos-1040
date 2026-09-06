# Independent correspondence review of TruncatedEnergy

Reviewer: combinatorics_scout. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/TruncatedEnergy.lean`, SHA-256
`a4a946a5c03daf7c48c107db684319ecc0eca74ffacd7833fad8e8de5e75a5a1`.
The root agent authored this source; this reviewer did not edit its proofs.
The source, five natural-language statements, and five exact printed
signatures were compared against the passing immutable report
`formal/admissions/2026-09-05-geometric-support-initial-195.json`, checked
2026-09-05 05:22 UTC. Per-declaration source, signature, and statement hashes
are recorded in `combinatorics-truncated-energy-bindings.json`.

1. `truncatedLogEnergy` is the actual extended nonnegative integral of the
   pointwise minimum of the established logarithmic kernel and the natural
   truncation level, against the product of a source probability with itself.
   The source set and real scale are unrestricted in this definition. In
   particular, its diagonal is truncated to the finite level when the scale
   is positive; the untruncated kernel's infinite diagonal is not redefined.

2. `lowerSemicontinuous_truncatedLogEnergy` assumes compactness of the
   complex source and proves lower semicontinuity of this exact truncated
   energy on the source probability space with its existing weak topology.
   The proof uses continuity of the extended kernel, continuity of finite
   truncation, the established lower semicontinuity theorem for actual
   integrals, and continuity of the probability-product map. It introduces
   no probability convergence, source smoothness, or finite full-energy
   assumption.

3. `nonnegativeLogEnergy_eq_iSup_truncated` uses the same probability on both
   sides and identifies the full actual extended energy with the supremum
   of all natural truncations. The source need not be compact. The proof
   establishes the measurable increasing integrands, applies monotone
   convergence, and proves their pointwise supremum equals the original
   kernel, including its value at infinity. Thus no diagonal term is lost
   and infinite full energy is preserved.

4. `exists_probability_energy_le_of_truncated_bounds` has a compact source,
   arbitrary real scale, and an arbitrary extended nonnegative bound B.
   The hypothesis allows a different source probability for each truncation;
   the conclusion produces one probability whose full actual energy is at
   most B. The proof forms closed nested sublevel sets in the compact source
   probability space. Their nonemptiness is exactly the stated hypothesis.
   A point in their intersection bounds every truncation for a single
   probability, and the preceding supremum identity bounds its full energy.
   Nonemptiness of the source is thereby supplied by the hypothesis, not
   silently assumed. B is allowed to be infinity; a finite-energy conclusion
   requires a finite B in an application.

5. `exists_probability_energy_le_of_approx_truncated_bounds` permits the
   approximating probability to depend on both the natural truncation and
   every positive finite nonnegative-real error. The proof attains the
   minimum of each truncated energy using lower semicontinuity and
   compactness. A witness at error one supplies the required nonempty
   probability space. Comparison with the witnesses at every positive error
   puts that minimum below B, after which the nested-sublevel theorem supplies
   one probability with full energy at most B. The error quantifier has not
   been weakened to a selected tolerance or a finite collection of tests.

No extra assumption, omitted quantifier, domain change, weakening, or
strengthening was found relative to the five registered statements. The
proofs distinguish actual bounded truncations from the full singular energy
throughout. They do not assert finite full energy for empirical atomic
probabilities or assume an empirical sequence converges. No geometric
configuration, transfinite-diameter bound, equilibrium measure property,
or main lemniscate conclusion is supplied by this module itself.

The immutable full report passes the machine checks; the five declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`. This separate
correspondence review establishes their stated supporting scope only. It
does not establish E1040-CAP1, E1040-FULL, or a P versus NP implication.
