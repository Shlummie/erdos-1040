# Independent correspondence review: LogContinuity

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/LogContinuity.lean`, SHA-256
`57a6f8fb5a2fe0686c34af4f26ea3826030f9324e70e3de479b38d0aa4db7d29`.
The author, number_theory_scout, explicitly froze the source after a successful
full project check. This reviewer did not edit it. The review compares the
complete definitions and proof bodies, the five current manifest statements,
the underlying `LogKernel.lean` objects, and separately printed exact
signatures. The independent print run exited 0; its output is
`formal/.audit/preflight-log-continuity.log`. The source hash was checked again
after that run. Per-declaration version bindings are in
`preflight-log-continuity-bindings.json`.

## Restriction and representatives

`restrictAreaL2` takes an arbitrary planar set and a real global area-L2 class.
Its result is an L2 class for planar Lebesgue measure restricted to that set.
It uses the input class's representative together with its checked `MemLp`
property and the restriction theorem. No particular representative is claimed
pointwise. Global almost-everywhere equality remains equality almost everywhere
after restriction because the restricted measure is dominated by the original
measure. Thus the definition is faithful at the quotient-class level.

The set need not be measurable. `Measure.restrict_le_self` is sufficient for
the L2 membership and distance inequalities on this complete-domain
definition; no claim about an arbitrary set's indicator or area regularity is
introduced. This matches the manifest's explicit arbitrary-set domain.

`lipschitzWith_restrictAreaL2` proves the full two-input distance inequality
with constant exactly one. The extended-distance formulas for the two L2
classes reduce it to monotonicity of the L2 seminorm in its measure. In these
Lp spaces the finite norm and metric are the standard L2 norm and distance,
so the theorem is precisely the claimed 1-Lipschitz restriction map, not merely
continuity or a bound for one chosen representative.

## Source translations

`continuous_translateAreaL2` quantifies over every real global area-L2 class
and every complex shift. The argument translation is exactly `z - w`; no sign
change is hidden. The source constructs the continuous family of continuous
maps `(w,z) -> z-w` and supplies the standard translation-invariance proof
for planar Lebesgue measure. The imported Lp-composition continuity theorem
applies at the finite exponent 2. The printed signature elides this supplied
measure-preservation proof term, not an additional theorem hypothesis.

Its codomain is the normed global L2 space. Therefore the conclusion is strong
L2 norm continuity in the shift, not pointwise continuity of a representative,
weak convergence, or continuity merely away from a singular source. It does
not claim that the untruncated logarithmic kernel is globally in L2.

## The compact-domain logarithmic kernel

`areaLogKernel` represents `z -> Real.log (norm (z-w))` in the real L2 space
for planar Lebesgue measure restricted to the arbitrary compact set. The
source uses the proved shifted-kernel membership result, not a new assumption
asserting membership. The logarithm is explicitly totalized at its source;
the class agrees with the classical kernel away from an area-null singleton.
Repeated source positions, empty sets, and compact sets of zero area are all
within the stated domain. No equilibrium measure or capacity is involved.

`continuous_areaLogKernel` proves continuity for all complex source positions,
including positions in the compact set. At an arbitrary source `w0`, compactness
supplies a finite positive bound `norm z < R` for every `z` in the set. The
proof fixes `L = R + norm w0 + 2` and truncates the unshifted logarithmic
kernel by the indicator of the closed ball of radius L. The preceding compact
integrability theorem makes this truncated function globally L2. The cutoff
need not be continuous; strong continuity of translations holds for arbitrary
global L2 functions.

For shifts with `norm(w-w0) < 1`, the triangle inequality gives
`norm(z-w) <= norm z + norm w < R + norm w0 + 1 < L` for every point of the
compact set. Consequently the translated cutoff and the desired shifted
logarithmic kernel agree there. The proof first uses the actual
almost-everywhere representative of the translated L2 class, restricts that
equality to the compact set, and invokes membership in the compact set almost
everywhere for its restricted measure. It then uses `MemLp.toLp_congr` to
obtain equality of L2 classes. There is no unjustified pointwise identity of
quotient representatives.

The restricted translated-cutoff family is norm-continuous by the preceding
two theorems. Its eventual equality with the target family yields continuity
at the arbitrary source `w0`. No step excludes `w0` from the compact set or
discards the compact boundary. Compactness is used only for a norm bound,
measurability, and the established compact L2 membership. No smooth boundary,
zero-area boundary, nonempty interior, connectedness, or positive area is
assumed. This covers arbitrary compacts, including positive-area sets with
empty interior, at the level of this kernel-continuity theorem.

## Outcome and scope

All five exact signatures match their manifest statements. No extra
assumption, omitted quantifier, altered measure, hidden weakening, or
strengthening relative to those statements was found. The source translation,
quotient representatives, cutoff domain, and genuine norm-continuity
requirements pass independent mathematical correspondence review.

All five independently printed axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`, with universe annotations. The latest
whole-project machine report observed during review passed and contained the
same source hash. Review bindings themselves do not promote declarations and
do not replace the final whole-project gate after other edits.

This establishes a necessary logarithmic-kernel continuity input. It does
not establish empirical-measure convergence, density of equilibrium-supported
potentials, logarithmic capacity, or either final target `E1040-CAP1` and
`E1040-FULL`. Those remain separate research dependencies.
