# Independent correspondence review: SimultaneousApproximation

Reviewer: formalization_preflight. Date: 2026-09-05 UTC.

Reviewed source: `formal/Erdos1040/SimultaneousApproximation.lean`, SHA-256
`ec8a506a77cd7ac2a0b000f26390995e879e6d7e6453491ae36c5510148eeff4`.
The root agent authored and froze this compiled module. The reviewer did not
edit it. The review compares the complete theorem and proof, its manifest
statement, and the two independently reviewed modules it combines. The
separate exact signature and axiom print run exited 0 and is recorded in
`formal/.audit/preflight-simultaneous-approximation.log`. The source hash was
rechecked after that run. The version binding is in
`preflight-simultaneous-approximation-bindings.json`.

The only declaration is
`Erdos1040.exists_roots_simultaneous_potential_approximation`.

Its signature retains compact source S, compact area observation K, the
explicit `CompactSpace E` exterior-observation binder, disjointness of S and
E, and a probability measure on the source subtype S. Both tolerances are
arbitrary positive real numbers. There is no capacity assumption, source
density restriction, boundary-regularity condition, or separation requirement
between K and S.

For these inputs the theorem returns one natural degree `n > 0`, then a list
`roots : Fin n -> Complex`, then explicit membership of every root in the
original S. Both error conclusions are inside this same existential scope.
Thus it supplies one root list meeting both estimates. Repeated roots remain
allowed, and the empty-list totalization of the supporting definitions cannot
satisfy the positive-degree conjunct.

The first error is the real area-L2 norm on K of the difference between the
class of the actual `atomicLogPotential roots` and the Bochner integral of
the source-to-`areaLogKernel` map. Its `toLp` membership proof comes from the
previously proved finite-atomic integrability theorem. The proof rewrites the
exact finite L2 class identity from `DiscretePotential` into the area estimate
obtained from `ExteriorKernel`; it does not merely rename an arbitrary kernel
average as an actual atomic potential.

The second conclusion uses those identical complex roots and bounds the
absolute difference between their actual atomic-potential value and the
actual scalar source log-distance integral for every point of E. It retains
the strict exterior tolerance. The earlier exterior theorem provides this
pointwise integral correspondence and the common list; subtype coercion to
the complex plane preserves both values and source membership exactly.

The area reference is still a Bochner integral of L2 classes. This theorem
does not equate it with an arbitrary-source pointwise potential on overlapping
area observations. The distinct actual scalar-integral statement is confined
to the explicitly disjoint exterior observation set. It provides no prescribed
degree, quantitative rate, or simultaneous convergence for every test function.

The exact printed signature matches the manifest statement. No extra
assumption, omitted quantifier, changed domain, hidden weakening, or unreported
strengthening was found. The independently printed axiom list contains only
`propext`, `Classical.choice`, and `Quot.sound`, with universe annotations.

This is a correspondence review of the frozen compiled declaration. The full
project checker remains required after the other modules under construction
settle. No trusted-core promotion was performed by this reviewer, and neither
`E1040-CAP1` nor `E1040-FULL` is established by this combined approximation
theorem.
