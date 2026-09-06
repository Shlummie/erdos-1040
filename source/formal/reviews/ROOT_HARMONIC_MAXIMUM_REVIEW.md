# Independent correspondence review: HarmonicMaximum

Reviewer: root, 2026-09-05 UTC. Author: number_theory_scout.
All four exact signatures and source proofs were independently read after a
full successful machine audit. Per-declaration source/signature/statement
bindings are in root-harmonic-maximum-bindings.json.

1. harmonic_eventually_eq_of_isLocalMax: real f on the complex plane, harmonic
at c and a local maximum there, gives f=f(c) on a neighborhood of c. The proof
uses a conjugate only on a local disk. Exponentiation turns its real part into
a complex modulus; injectivity of the real exponential gives the claimed equality.
2. harmonic_eqOn_of_isPreconnected_of_isMaxOn: open preconnected U, harmonicity
at every point of U, an explicit point c in U, and an attained global maximum
on U. Conclusion is constancy on U. No global conjugate or simply-connected
assumption occurs. Preconnectedness plus the witness is the intended connected
nonempty-domain condition; the clopen separation proof matches the scope.
3. harmonic_nonpos_of_continuous_majorant: open preconnected unbounded U,
harmonic real f on U, continuous real g on the whole plane, g=0 at every
frontier point, f<=g on U, and the global cocompact limit f->0. Conclusion f<=0
on U. The global limit is stated explicitly (stronger than a limit only
within U) and is supplied by the actual compact-source asymptotics interface.
No continuity of f on the frontier is asserted. The positive superlevel is
closed using g and compact using the limit, before its maximum is invoked.
4. harmonic_eq_zero_of_nonpos_of_circleAverage_zero: same open preconnected
harmonic domain, f<=0 on U, positive radius R, full circle sphere(c,R) in U,
and exact Real.circleAverage f c R=0. Conclusion is f=0 on all U. The enclosed
disk is not required to lie in U. Circle continuity/integrability follows from
harmonicity near its points. Circle compactness and the strong maximum theorem
supply equality without any irregular-boundary extension assumption.

All are clearly conditional supporting lemmas. None supplies equilibrium
measure existence, global Frostman nonnegativity, harmonicity of actual source
integrals, or the final capacity-one result. The recorded four theorem axiom
audits use only propext, Classical.choice, Quot.sound. No correspondence issue
found; admission still requires a final full gate on the registered source.
