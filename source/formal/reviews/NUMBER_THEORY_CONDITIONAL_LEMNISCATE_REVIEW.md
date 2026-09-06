# Independent correspondence review of ConditionalLemniscate

Reviewer: number_theory_scout. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/ConditionalLemniscate.lean`, SHA-256
`5bc2595a6a22e78f4dbf3f4d85b241c19dc366163cdedeec1d1d3db23782e241`.
The root agent authored the source; this reviewer did not edit its proofs.
The four registered statements and exact printed signatures were read from
the immutable passing 158-declaration report
`formal/admissions/2026-09-05-conditional-and-frostman-pre-admission.json`,
SHA-256 `b79da8378751cca90066c71829b7739f834775520aaaeb4007ef95186ae972b1`.
Its recorded check time is `2026-09-04T22:05:49.95245-07:00`.
Per-declaration source, signature, and statement hashes are recorded in
`number-theory-conditional-lemniscate-bindings.json`.

The accompanying mathematical supplement
`erdos-research/experiments/1040/MONOTONE_AREA_ASSEMBLY.md` was also reviewed
at SHA-256 `821f9bb2de6c29a05fa0bc22538c0abcbd3542ad5575f4321874653961789dc4`.
The original candidate's bytes remain separate fixed evidence.

1. `exists_L2_tolerance_for_small_sublevel_set` quantifies over any finite
   measure on the complex plane, a real L2 function, any real threshold, a
   positive real margin represented as `NNReal`, and every positive real
   tolerance. Its conclusion is uniform over all sufficiently close real
   L2 functions and uses the strict sublevel set at the original threshold.
   Subtracting the constant threshold is legitimate because the measure is
   finite. The proof preserves the L2 distance exactly and applies the
   established negative-set margin estimate. Neither the comparison nor
   conclusion silently changes strict inequalities to non-strict ones.

2. `exists_large_shift_small_exterior_set` has exactly the registered finite
   measure, measurable set, real-valued almost-everywhere measurable
   functions, and everywhere exterior strict-positivity assumptions. The
   actual sets for the sequence `A_n = max C 0 + 1 + n` are null measurable,
   decrease, and have empty intersection because each exterior value of U
   is strictly positive and V is a finite real number. Continuity of measure
   from above applies because the ambient measure is finite. The resulting
   A is both positive and strictly greater than C. No boundary regularity,
   neighborhood thickness, uniform lower bound, continuity of U or V, or
   exterior uniform convergence has been inserted.

3. `shifted_source_potential_ae_eq` uses compact planar source S and compact
   observation D, a probability on subtype S, a measurable real density f
   with a pointwise finite bound C, and A greater than C. Its left side is
   the actual change-of-density measure with the exact normalized density
   `(f+A)/(integral(f)+A)`. The checked PositiveDensity results separately
   prove its positive normalizing mass and probability property. Product
   integrability provides source-kernel integrability for almost every
   observation point, where the actual scalar integral formula applies.
   The conclusion is equality almost everywhere for planar area restricted
   to D, not equality at every source point or an implicit extended-real
   convention. The scalar potential functions use Lean's totalized real
   integral exactly as the registered statement says.

4. `hasArbitrarilySmallLemniscates_of_potential_properties` retains all
   conditional inputs: compact S contained in compact K, a probability on
   S, preconnectedness of the complement of K, inclusion of the whole
   frontier of K in the support of the source pushed forward by inclusion,
   global nonnegativity of the actual positive-log source potential, and
   strict positivity at every point outside K. The conclusion expands to
   every positive area tolerance, a positive natural degree, an actual
   finite list of roots all in S, and planar Lebesgue area of the entire
   strict unit lemniscate below that tolerance. The established root-product
   polynomial is monic and has that degree. Multiplicities remain allowed.

For the fourth theorem, the polynomial-density step is used only on K. Its
mean-zero polynomial is above the fixed margin except on a sufficiently
small area set, and L2 closeness gives the required signed-potential margin
on K. Adding the positive multiple A U cannot decrease that signed potential
on K. Outside K, the second theorem makes the bad area small in the fixed
observation disk. The exact normalized-potential identity covers its small
sublevel set almost everywhere by these two bad sets, whose strict bounds
sum to less than the requested tolerance. AtomicAreaAssembly preserves this
strict area bound and confines the entire resulting unit lemniscate to the
disk of source-radius plus one. Thus no exterior area is omitted and no
source point is moved outside S.

The supplement describes this same valid implication. It allocates a spare
epsilon/4 bound to the initial polynomial's exceptional set, while the
checked assembly directly uses epsilon/2 with the margin-transfer theorem;
both choices yield the stated epsilon/2 bound on the first bad set and the
same final epsilon bound. This numerical slack is not a theorem-signature
change. The supplement correctly identifies that U=0 almost everywhere on K
is unnecessary: global nonnegativity alone proves the needed inequality.
It also correctly removes the boundary-collar and uniform-convergence steps
from this conditional assembly.

No extra assumption, missing quantifier, domain change, hidden weakening, or
strengthening was found relative to the four canonical registered statements.
The immutable report passes the source scan, pinned build, dependency checks,
and all four axiom audits, recording only `propext`, `Classical.choice`, and
`Quot.sound`. This review supplies the separate correspondence check for the
specified source and signature version. Final admission remains the root's
canonical-record operation.

This establishes the conditional supporting implication only. Deriving its
probability, topology, support, and global potential hypotheses from the
original transfinite-diameter condition remains mathematical work. The
report explicitly leaves E1040-CAP1 and E1040-FULL incomplete. No solution of
Erdos #1040, priority claim, or P versus NP implication is certified here.
