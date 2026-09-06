# Independent correspondence review: Unbounded and AtomicPotential

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

The reviewer authored neither reviewed mathematical module. This review compares
the complete source bodies, the separately printed exact Lean signatures, and
the corresponding natural-language statements in `formal/claims.json`. The
mathematical context is the candidate proof, sections 7 and 8.2, together with
the finite-root definitions in `Basic.lean`.

The frozen sources are:

- `formal/Erdos1040/Unbounded.lean`: SHA-256
  `805c0dd336dee7456891b029688d5e332f2138a799c62a34d0956e93321c9156`.
- `formal/Erdos1040/AtomicPotential.lean`: SHA-256
  `11dc8d3c71fdc66458f9d7701c466ad2216c409b8261234a3ab33fa970b43094`.
- Supporting `formal/Erdos1040/Basic.lean`: SHA-256
  `8ad9a2349f6cc49d3042bcb01c67bc63c09286655df5d48bb2afa028cbbc3dc7`.

The independent `lake env lean --stdin --json` signature and axiom command
completed with Lean exit code 0. Its unchanged output is
`formal/.audit/preflight-unbounded-atomic.log`. The subsequent shell display
initially encountered a Windows console encoding error; the Lean run and the
UTF-8 log had already completed successfully. The log was then read directly.
The signature printer settings match the project checker. The paired JSON
bindings record hashes of these exact printed signatures and reviewed source
statements. The full project checker remains a separate required gate.

## Unbounded: four declarations

`quadratic_sublevel_subset_balls` quantifies over any two distinct complex
numbers. Its left side is the strict unit sublevel set of the actual quadratic
product. Its right side is the union of the two open balls of radius
`2 / norm (a - b)`. Complex norm equals Euclidean distance. Distinctness makes
the denominator strictly positive. The triangle inequality forces one factor
distance to be at least half the root separation, so the other is strictly
less than twice its reciprocal. No hypothesis about capacity, closedness,
root-set membership, or degree is silently used by this geometric lemma.

`volume_quadratic_sublevel_le` uses planar Lebesgue volume on the entire
complex plane, not a probability measure or one-dimensional length. Ball
volume and measure subadditivity give exactly `8 * pi / norm (a - b)^2`.
The source uses `ENNReal.ofReal` to embed this positive, finite real bound.
The non-strict area upper bound and the strict sublevel inequality are both
preserved. No disjointness assumption is introduced for the two balls.

`unbounded_exists_quadratic_small_area` has the required quantifier order:
every unbounded complex set, then every positive real tolerance, then two
distinct roots in that original set. Unboundedness supplies nonemptiness and
arbitrarily large root separation. The proof chooses the stronger sufficient
separation `D > max(1, 8*pi/epsilon)`, which implies `D^2 > 8*pi/epsilon`.
This changes only an internal witness bound, not the theorem statement.
The area conclusion is strictly less than the given positive tolerance.

`unbounded_hasArbitrarilySmallLemniscates` expands to the already reviewed
predicate with a positive natural degree, a `Fin n`-indexed root list in the
original set, and strict area below every positive real tolerance. Its witness
is exactly degree two with roots `a` and `b`; the polynomial connection and
exact degree are supplied by `Basic.lean`. The Lean statement matches its
manifest statement. Relative to the candidate section headed "Unbounded
closed infinite sets", this is an explicit strengthening: closedness is not
needed, and unboundedness already rules out finite sets. It does not address
the bounded compact capacity-one case.

## AtomicPotential: six declarations

`atomicLogPotential` is exactly the finite sum of totalized real logarithms of
distances divided by the list length. Repeated roots are allowed and retain
multiplicity. Unlike the classical extended-real logarithmic potential, it
is a real-valued representative whose logarithm at zero is totalized. There
is also a harmless empty-list extension: `n = 0` is allowed by the definition,
and Lean's totalized division gives value zero. This edge case was identified
during review and explicitly added to the natural-language definition and
log-product identity before binding them. It is not treated as a degree-zero
solution: the sign and area theorems require `0 < n`.

`atomicLogPotential_eq_log_product` has the explicit hypothesis that the
evaluation point differs from every listed root. That hypothesis ensures
every distance and the product modulus are nonzero, so the logarithm of the
product equals the sum of logarithms. Both sides are divided by the same
natural-number cast. The identity includes the now-documented totalized
empty-list case. No pointwise logarithmic identity at a root is asserted.

`atomicLogPotential_neg_iff` separately requires positive list length and
avoidance of every root. Positive length permits sign-preserving division;
positive product modulus permits `log x < 0` exactly when `x < 1`. Its result
uses the strict unit lemniscate. Neither the positivity nor the root-avoidance
hypothesis is omitted from the informal statement.

`ae_ne_roots` asserts that planar Lebesgue almost every complex point differs
from every element of an arbitrary finite root list. Finiteness is encoded
by `Fin n`; repeated roots cause no problem. Although the abbreviated printed
signature elides the default measure notation, the complete source explicitly
fixes `volume` on `Complex`. No arbitrary measure or nonatomicity assumption
is hidden in the declaration's signature.

`unitLemniscate_ae_eq_atomicLogPotential_neg` requires positive length and
asserts equality almost everywhere for planar Lebesgue measure, not literal
set equality. The finite root set is the necessary null exception because
the real logarithm is totalized there. This is faithful to candidate section 7,
which explicitly works away from the zeros and then passes to area.

`volume_unitLemniscate_eq_atomicLogPotential_neg` converts that almost-everywhere
set equality into equality of planar areas. It has the same positive-degree
requirement and no additional measurability, capacity, distinctness, or
finite-area hypothesis. The measure equality is valid for the full ENNReal
volume values. It does not assert any sign or pointwise identity at a root.

## Review outcome and limits

After the explicit empty-list clarification, all ten declaration-to-statement
comparisons pass correspondence review. The only differences from the wider
informal context are documented above: the unbounded theorem drops an
unneeded closedness assumption, and the atomic potential is a totalized
real-valued representative whose area correspondence removes the finite root
set. No hidden weakening, extra assumption, omitted quantifier, changed
admissible root set, or change of planar area was found.

Each of the ten printed axiom lists contains only `propext`,
`Classical.choice`, and `Quot.sound`, with their printed universe annotations.
These observations do not replace dependency, source, build, and whole-project
checks. The paired JSON authorizes version-bound correspondence status only;
this reviewer has not promoted any theorem to the trusted core.

This review establishes no equilibrium measure theorem, capacity-one result,
area-L2 density result, quantitative complexity bound, or complete solution of
Erdos #1040. `E1040-CAP1` and `E1040-FULL` remain separate unresolved targets.
