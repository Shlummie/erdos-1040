# Small-area polynomial lemniscates with prescribed roots

## A Lean-verified proof of the threshold assertion in Erdős problem #1040

shlummi

6 September 2026 - public review manuscript, version 1

### Abstract

For a closed infinite set \(F\subseteq\mathbb C\) of geometric transfinite diameter at least one, we prove that monic polynomials of positive degree with all roots in \(F\) have strict unit lemniscates of arbitrarily small planar Lebesgue area. We also prove the conclusion for every compact set of logarithmic capacity at least one, including arbitrary compact capacity-one sets. The proof constructs a finite-energy minimizing probability, establishes a global potential bound, approximates mean-zero harmonic polynomials by density potentials in planar-area \(L^2\), and discretizes a positive probability after establishing a positive margin on almost all the observation area. No boundary regularity is imposed. An appendix formalizes a known negative answer to the separate question of whether the minimum-area functional depends only on capacity or transfinite diameter. The accompanying Lean project records 241 theorems and 33 definitions. No degree or runtime bound is claimed.

### Relation to the problem and earlier work

Erdős, Herzog and Piranian [1, Problem 4, p.135] ask whether the infimum of these areas is determined by transfinite diameter and whether it vanishes at transfinite diameter at least one. The main argument below addresses the threshold assertion. The appendix treats the already-known negative answer to the dependence question; that negative answer is not claimed as new.

Ghosh and Ramachandran [2, version 3] prove the compact capacity-greater-than-one case and explicitly leave the general compact capacity-one case open. Krishnapur, Lundberg and Ramachandran [3, Theorem 6 and section 5] treat capacity-one sets with boundary regularity hypotheses. Their potential-approximation strategy provides background for this work; here the approximation and error control use planar area throughout. These comparisons concern the cited versions and are not an exhaustive priority determination. Saff [4] provides background on classical logarithmic potential theory; the formal proof establishes the required ingredients through its pinned Lean dependencies and project lemmas.

### Proof organization

Sections 2-5 obtain a minimizing probability whose raw logarithmic potential is nonnegative everywhere and strictly positive outside a compact filled hull. Sections 6-8 construct harmonic polynomials positive outside a set of small area and approximate them by density potentials. Section 9 shifts a density to obtain a positive probability and fixes a positive potential margin before sampling. Sections 10-11 produce actual roots in the original set and handle unbounded sources. The geometric and energy-capacity hypotheses supply the initial energy bound separately; no general capacity-diameter equality is assumed.

### AI assistance and verification status

The proof development, Lean formalization, manuscript preparation, and recorded correspondence reviews used AI assistance, including OpenAI Codex. Additional AI reports supplied by the project operator were attributed to DeepSeek and Claude/Opus; no comprehensive independent human review is claimed. The checking records concern the exact Lean statements and their dependencies. Mathematical correspondence with the informal problem is a separate assessment; a successful compiler run alone does not settle that assessment. This manuscript is being prepared for public scrutiny and does not claim journal acceptance or acceptance by the Erdős Problems site.

The proof body and counterexample argument below are drawn from the existing verified project manuscripts. Mathematical formulas, quantifiers, and theorem names are retained. Typesetting, introductory material and references were prepared for this release. All short formal pointers use the namespace prefix `Erdos1040.` and refer to module files under `formal/Erdos1040/` in the companion source archive.

## 1. Statements, area, and the two size definitions

Write \(m\) for two-dimensional Lebesgue measure on \(\mathbb C\). For a
positive integer \(N\) and points \(w_1,\ldots,w_N\), with repetitions allowed,
put

\[
 p(z)=\prod_{j=1}^{N}(z-w_j),\qquad
 L(p)=\{z\in\mathbb C:|p(z)|<1\}.
\]

The polynomial is monic and has degree \(N>0\). Both the sublevel inequality
and the desired area bound are strict.

**Full theorem.** Let \(F\subseteq\mathbb C\) be closed and infinite. If its
geometric transfinite diameter \(\rho(F)\) is at least one, then for every
real \(\varepsilon>0\) there is a monic polynomial \(p\in\mathbb C[z]\) of
positive degree, with every complex root in \(F\), such that

\[
 m(L(p))<\varepsilon. \tag{1}
\]

**Compact capacity corollary.** If \(S\subseteq\mathbb C\) is compact and its
logarithmic capacity is one, the same conclusion holds with all roots in
\(S\). The argument also proves this conclusion when that capacity is greater
than or equal to one.

These are the explicit positive-tolerance versions of the vanishing-infimum
question in Erdős, Herzog and Piranian, *Metric properties of polynomials*
(1958), Problem 4, p.135. Equation (1) of that paper, on p.125, specifies the
monic products and their strict unit sublevels. The separate dependence question is addressed in Appendix A.

For \(N\geq2\), define

\[
 d_N(w_1,\ldots,w_N)
   =\left(\prod_{i<j}|w_i-w_j|\right)^{2/(N(N-1))},
 \qquad
 \delta_N(S)=\sup_{(w_1,\ldots,w_N)\in S^N}d_N(w_1,\ldots,w_N).
 \tag{2}
\]

The supremum is in \([0,\infty]\), with value zero for an empty family. On a
nonempty compact \(S\), it is a finite attained maximum. Section 2 proves
that \(\delta_N(S)\) decreases for \(N\geq2\); thus

\[
 \rho(S)=\lim_{N\to\infty}\delta_N(S)
        =\inf_{N\geq2}\delta_N(S). \tag{3}
\]

For the capacity definition, let \(S\) be compact and choose any real \(D>0\)
bounding all distances between its points. On \(S\times S\), use the
extended nonnegative kernel

\[
 k_D(z,w)=
 \begin{cases}
  \log(D/|z-w|),&z\ne w,\\
  +\infty,&z=w.
 \end{cases}
\]

For a Borel probability \(\mu\) on \(S\), set

\[
 J_D(\mu)=\iint k_D(z,w)\,d\mu(z)\,d\mu(w),\qquad
 I(\mu)=J_D(\mu)-\log D. \tag{4}
\]

The integral \(J_D\) retains positive infinity on the diagonal. The
normalized energy \(I\) is independent of the chosen positive distance
bound: changing \(D\) adds exactly the corresponding logarithmic constant
to \(J_D\), including the case of infinite energy. When finite, \(I\) is the
usual integral of \(\log(1/|z-w|)\). Define the Robin constant and capacity by

\[
 V_S=\inf_{\mu\in\mathcal P(S)}I(\mu),\qquad
 \operatorname{cap}(S)=\exp(-V_S). \tag{5}
\]

Here \(\inf\varnothing=+\infty\) and \(\exp(-\infty)=0\). The implementation
chooses \(D=\max(1,\operatorname{diam}S)\) for these definitions and proves
independence of every other permissible \(D\). Capacity of the empty set is
zero. Only compact sources use this energy definition in the capacity
theorem. The geometric and capacity hypotheses will supply the needed
energy bound separately; their classical equality need not be assumed.

There are three distinct logarithm conventions in the proof. The singular
energy kernel above always retains its infinite diagonal. Finite algebraic
double sums in section 2 use the totalized real value \(\log0=0\) only for
diagonal terms excluded by the corresponding off-diagonal sum. Area-\(L^2\)
representatives may likewise use this finite value at their single
singularity, since that point has planar measure zero. Neither convention
replaces the singular energy kernel.

**Formal pointers.** `Basic`: `rootPolynomial`, `unitLemniscate`,
`HasArbitrarilySmallLemniscates`, and the monicity, degree, evaluation and
root identities. `GeometricDiameter`: `unorderedPairProduct`,
`geometricMeanSeparation`, `finiteDiameter`, `transfiniteDiameter`.
`LogEnergy`, `LogEnergyScale`, and `LogarithmicCapacity`: the actual extended
energy, `nonnegativeLogEnergy_normalized_scale_independent`, `robinConstant`,
and `logarithmicCapacity`.

## 2. The geometric limit supplies distinct configurations

First prove the monotonicity asserted in (3). Consider \(N+1\) points, where
\(N\geq2\). If the full pair product is zero, its geometric mean is zero,
and deleting any point gives a nonnegative mean at least as large.

Otherwise all points are distinct. Set

\[
 T_0=\sum_{i\ne j}\log|w_i-w_j|.
\]

Its normalized mean satisfies \(\log d_{N+1}=T_0/(N(N+1))\). Each ordered
pair occurs in exactly \(N-1\) of the \(N+1\) configurations obtained by
deleting one point. Consequently

\[
 \sum_{k=1}^{N+1}\log d_N(w_1,\ldots,\widehat w_k,\ldots,w_{N+1})
  =\frac{(N-1)T_0}{N(N-1)}
  =(N+1)\log d_{N+1}. \tag{6}
\]

At least one deleted configuration has geometric mean at least \(d_{N+1}\).
Taking suprema gives \(\delta_{N+1}(S)\leq\delta_N(S)\) for every \(S\).
A decreasing sequence in \([0,\infty]\) converges to its infimum, proving
(3). In the Lean matrix calculation the displayed off-diagonal sum equals
the full double sum with totalized zero diagonal entries; all non-diagonal
distances in this branch are strictly positive.

Now suppose \(S\) is compact and \(\rho(S)\geq1\). For every \(N\geq2\), the
maximum in (2) is at least one. A maximizing tuple therefore has pair
product at least one and is distinct. In particular,

\[
 \sum_{i\ne j}\log|w_i-w_j|\geq0. \tag{7}
\]

Nonemptiness of \(S\) follows from the same hypothesis.

**Formal pointers.** `GeometricDiameterLimit`:
`sum_log_geometricMeanSeparation_succAbove`,
`exists_geometricMeanSeparation_le_succAbove`, `finiteDiameter_succ_le`,
`antitone_finiteDiameter`, `tendsto_finiteDiameter_transfiniteDiameter`.
`GeometricDiameter`: `finiteDiameter_eq_max_of_compact` and
`exists_distinct_configuration_log_sum_nonneg`.

## 3. A finite global energy minimizer

The space \(\mathcal P(S)\) of Borel probabilities on a nonempty compact
metric space is compact in its weak topology. Extend \(k_D\) to the plane
by replacing negative off-diagonal values with zero. This kernel is
continuous into \([0,\infty]\); on \(S\times S\) it is unchanged. Its bounded
truncations are continuous, and the full energy is their increasing
supremum. Continuity of the probability-product map and monotone convergence
give lower semicontinuity of \(J_D\). Hence \(J_D\) attains its minimum,
though this alone does not show that the minimum is finite.

Assume first \(\rho(S)\geq1\), and choose \(D\geq1\) bounding all source-pair
distances. For a natural truncation level \(t\), write

\[
 J_{D,t}(\mu)=\iint\min(k_D(z,w),t)\,d\mu(z)\,d\mu(w).
\]

Take the \(N\) points from (7) and their empirical probability
\(\mu_N=N^{-1}\sum_j\delta_{w_j}\). Its diagonal contribution to the
truncated energy is \(t/N\). Off the diagonal, \(\min(k_D,t)\leq k_D\), so

\[
 \begin{aligned}
 J_{D,t}(\mu_N)
 &\leq \frac{t}{N}
   +\frac{N(N-1)\log D-\sum_{i\ne j}\log|w_i-w_j|}{N^2}\\
 &\leq \log D+\frac{t}{N}. \tag{8}
 \end{aligned}
\]

For each fixed \(t\), lower semicontinuity and compactness attain the minimum
of \(J_{D,t}\). Equation (8), for arbitrarily large \(N\), makes this minimum
at most \(\log D\). Thus the closed sets

\[
 C_t=\{\mu\in\mathcal P(S):J_{D,t}(\mu)\leq\log D\}
\]

are nonempty and nested. Compactness gives a probability in their
intersection. Monotone convergence puts its full energy at most \(\log D\).
Comparison with a global minimizer gives a minimizing probability \(\mu\)
with

\[
 e:=J_D(\mu)\leq\log D<\infty. \tag{9}
\]

The empirical probabilities were used only for their truncated energies;
their full singular energies were never asserted finite.

For the capacity corollary, suppose instead that
\(\operatorname{cap}(S)\geq1\). Equation (5) gives \(V_S\leq0\) and ensures
\(S\ne\varnothing\). A global minimizer of \(J_D\) also minimizes
\(I=J_D-\log D\). Since its value is \(V_S\leq0\), it has finite energy and
again satisfies (9). Both hypotheses therefore supply the same starting
condition through their respective definitions.

**Formal pointers.** `LogEnergy`:
`lowerSemicontinuous_nonnegativeLogEnergy`,
`exists_minimizer_nonnegativeLogEnergy`. `TruncatedEnergy`:
`exists_probability_energy_le_of_approx_truncated_bounds`.
`EmpiricalEnergy`: `truncatedLogEnergy_empirical_le_of_log_sum_nonneg`.
`EnergyDiameter`: `exists_finite_minimizer_of_one_le_transfiniteDiameter`.
`LogarithmicCapacity`: `robinConstant_eq_energy_sub_log_of_minimizer` and
`exists_finite_minimizer_of_one_le_logarithmicCapacity`.

## 4. From minimization to a nonnegative potential everywhere

Use the positive-logarithm convention

\[
 U(z)=\int\log|z-w|\,d\mu(w). \tag{10}
\]

We first prove its integrability and the needed global inequality. Finite
energy implies that \(\mu\) has no atoms: an atom of positive mass would
give the infinite diagonal positive product measure. Let

\[
 V_D(z)=\int k_D(z,w)\,d\mu(w).
\]

For a finite-energy probability \(\nu\), expansion of the energy of
\((1-s)\mu+s\nu\), followed by minimality at \(s=0\), gives

\[
 \int V_D\,d\nu\geq e. \tag{11}
\]

If the cross energy is infinite this is immediate; otherwise divide the
exact quadratic energy expansion by \(s>0\) and let \(s\downarrow0\).

The measurable source set \(A=\{V_D<e\}\) is \(\mu\)-null. Otherwise,
normalizing \(\mu|_A\) would give a finite-energy probability \(\nu\), since
\(J_D(\nu)\leq J_D(\mu)/\mu(A)^2\). It would satisfy
\(\int V_D\,d\nu<e\), contradicting (11). Tonelli gives
\(\int V_D\,d\mu=e\), so \(V_D=e\) \(\mu\)-almost everywhere.

Let \(T=\operatorname{supp}\mu\), viewing the source probability as a measure
on the plane. Lower semicontinuity makes \(\{V_D\leq e\}\) closed. This set
has full \(\mu\)-measure and therefore contains \(T\). For \(z\in T\), the
finite value \(V_D(z)\) implies absolute integrability of the raw logarithm:
off the null singleton \(w=z\),

\[
 \log|z-w|=\log D-k_D(z,w).
\]

Consequently

\[
 U(z)=\log D-V_D(z)\geq\log D-e\quad(z\in T). \tag{12}
\]

The support \(T\) is nonempty, compact, and contained in \(S\). Transporting
\(\mu\) to a probability on \(T\) preserves its ambient measure and every
integral. Outside \(T\), the compact source is a positive distance from each
fixed observation point. The raw logarithm is integrable there, and \(U\)
is harmonic. Local differentiation under the integral, using the local
analytic logarithm away from sources, proves this harmonicity.

To extend (12), put \(M_0=e-\log D\), so \(-U\leq M_0\) on \(T\). For each
\(z\), choose a nearest point \(a(z)\in T\). For \(w\in T\),

\[
 |a(z)-w|\leq |a(z)-z|+|z-w|\leq2|z-w|. \tag{13}
\]

For \(\xi\in T\), also \(|a(z)-\xi|\leq2|z-\xi|\), so \(a(z)\to\xi\) as
\(z\to\xi\). Define

\[
 b_z(w)=\max\bigl(0,\log|a(z)-w|-\log|z-w|\bigr).
\]

For each \(z\), null atoms and (13) give \(0\leq b_z\leq\log2\) almost
everywhere. For almost every \(w\), namely \(w\ne\xi\), one has
\(b_z(w)\to0\). Dominated convergence gives \(\int b_z\,d\mu\to0\).
All raw potentials here are integrable, and hence

\[
 -U(z)\leq-U(a(z))+\int b_z\,d\mu
          \leq M_0+\int b_z\,d\mu.
\]

This proves

\[
 \limsup_{z\to\xi}(-U(z)-M_0)\leq0\qquad(\xi\in T). \tag{14}
\]

Compact support also gives \(U(z)=\log|z|+o(1)\) at infinity. For example,
if all sources have modulus at most \(R\), then for \(|z|>2R\),

\[
 \bigl|\log|z-w|-\log|z|\bigr|\leq 2R/|z|,
\]

uniformly in \(w\). Thus \(-U-M_0\) is negative sufficiently far away. The
ordinary maximum principle on \(\mathbb C\setminus T\), with (14), yields
\(-U\leq M_0\) everywhere. This form covers all components: a positive
level would give a compact superlevel set away from the boundary, attaining
a maximum; its maximal-level set would then be nonempty, bounded, closed in
the plane, and open by the strong maximum principle, a contradiction.

Together with (9), this proves

\[
 U(z)\geq\log D-e\geq0\qquad\text{for every }z\in\mathbb C. \tag{15}
\]

No continuity of \(U\) on its support, boundary regularity, or theorem about
exceptional polar boundary sets was required.

**Formal pointers.** `LogEnergyIntegrability`:
`nullSingletonClass_of_finite_nonnegativeLogEnergy`. `EnergyVariation`:
`nonnegativeLogEnergy_le_crossEnergy_of_minimizer`. `EnergyFrostman`:
`finite_nonnegativeLogEnergy_probabilityRestriction`,
`nonnegativeLogPotential_ae_eq_energy_of_minimizer`. `GlobalFrostman`:
`nonnegativeLogPotential_le_energy_on_support_of_minimizer`,
`integrable_log_norm_sub_of_finite_minimizer`,
`eventually_neg_log_potential_lt_of_le_on_source`,
`harmonic_nonpos_of_boundary_and_infinity`, and
`log_source_potential_ge_of_finite_minimizer`.

## 5. A compact hull and strictly positive exterior potential

Continue with the actual probability on \(T\), denoting it by \(\nu\). Its
potential is the same \(U\). Choose a disk containing \(T\). The connected
exterior of that disk lies in a unique component \(\Omega\) of
\(\mathbb C\setminus T\). Every unbounded component meets that exterior,
so \(\Omega\) is the unique unbounded component. Put

\[
 H=\mathbb C\setminus\Omega.
\]

Then \(H\) is compact, contains \(T\), and has connected complement. Also
\(\partial H\subseteq T\): a point outside \(T\) has a neighborhood in one
component of \(\mathbb C\setminus T\) and is therefore an interior point of
either \(\Omega\) or \(H\).

On \(\Omega\), \(U\) is harmonic and nonnegative. If it vanished at one point,
the strong minimum principle would make it identically zero on connected
\(\Omega\). This contradicts logarithmic growth along the unbounded exterior.
Therefore

\[
 U>0\text{ on }\mathbb C\setminus H,\qquad
 U\geq0\text{ on all of }\mathbb C. \tag{16}
\]

Only \(T\) will supply roots. The hull \(H\) is an observation region for
area estimates; no root is introduced in \(H\setminus T\).

**Formal pointers.** `SourceSupport`: `sourceSupport`,
`sourceProbabilityOnSupport`, `integral_sourceProbabilityOnSupport`.
`FilledHull`: `exists_compact_hull_with_connected_complement`.
`ExteriorPositivity`: `log_source_potential_pos_on_hull_compl`.

## 6. Logarithmic kernels in planar-area \(L^2\)

For any compact observation set \(B\subseteq\mathbb C\), let

\[
 \kappa_B(w)=[z\mapsto\log|z-w|]\in L^2(B,m;\mathbb R).
\]

The value at \(z=w\) does not affect this area class. Local square
integrability follows from \(\int_0^r s|\log s|^2\,ds<\infty\); away from
the singularity the function is continuous. The map \(w\mapsto\kappa_B(w)\)
is continuous in \(L^2\). Near a fixed \(w_0\), cut off \(\log|z|\) on a
sufficiently large disk. All relevant restrictions then come from
translations of one global \(L^2\) function. Translations are continuous in
\(L^2\), and restriction does not increase the norm.

Thus \(\kappa_B\) is bounded on compact source sets and Bochner integrable
against every finite source measure. For bounded measurable real \(f\) on
\(T\), define the actual density potential

\[
 V_f(z)=\int_T f(w)\log|z-w|\,d\nu(w).
\]

Its area-\(L^2(B)\) class is

\[
 [V_f]=\int_T f(w)\kappa_B(w)\,d\nu(w). \tag{17}
\]

The representative identity is area-almost everywhere. Joint absolute
integrability follows from the uniform bound of \(\|\kappa_B(w)\|_2\),
finite area, and Cauchy-Schwarz. Fubini then identifies the Bochner integral
with the actual source integral. Pointwise evaluation on \(L^2\) is not
assumed to be a continuous functional.

**Formal pointers.** `LogKernel`: `memLp_log_norm_sub_of_isCompact`.
`LogContinuity`: `areaLogKernel`, `continuous_areaLogKernel`.
`SourcePotential`: `integrable_log_norm_sub_prod`,
`source_potential_toLp_eq_integral_areaLogKernel`.
`SourceDensity`: `source_density_potential_toLp_eq_integral_areaLogKernel`.

## 7. Density of mean-zero harmonic polynomials

Let \(\mathcal V\subseteq L^2(H,m;\mathbb R)\) be the linear subspace of
potentials in (17), for bounded measurable real \(f\) on \(T\). We claim that
whenever a complex polynomial \(P\) satisfies

\[
 \int_T\operatorname{Re}P\,d\nu=0,
\]

its real part lies in the \(L^2(H)\) closure of \(\mathcal V\).

Take \(h\in\mathcal V^\perp\), and define

\[
 W_0(w)=\int_H h(z)\log|w-z|\,dm(z),\qquad
 c=\int_H h(z)\,dm(z).
\]

The potential \(W_0\) is continuous everywhere, by Cauchy-Schwarz and
continuity of \(\kappa_H\). Orthogonality and Fubini give

\[
 0=\langle h,[V_f]\rangle=\int_T f(w)W_0(w)\,d\nu(w)
\]

for every bounded measurable real \(f\). The restriction \(W_0|_T\) is itself
bounded and continuous; choosing it as \(f\) gives \(W_0=0\)
\(\nu\)-almost everywhere. Continuity and the full ambient support yield

\[
 W_0=0\text{ on }T,\quad\text{in particular on }\partial H. \tag{18}
\]

On connected \(\Omega\), put \(W=W_0-cU\). It is harmonic and tends to zero
at infinity, because both terms have logarithmic mass \(c\). If \(c\geq0\),
(16) gives \(W\leq W_0\), and (18) makes its boundary upper limit at most
zero. The ordinary maximum principle gives \(W\leq0\) on \(\Omega\).

For a sufficiently large circle \(|z|=R\), the angular mean of
\(\log|z-w|\) is \(\log R\) for every \(w\in H\). One can take real parts
in the uniformly convergent logarithm series for \(1-w/z\) to see this.
Fubini gives means \(c\log R\) for \(W_0\) and \(\log R\) for \(U\), so
the circle mean of \(W\) is zero. A continuous nonpositive function on a
circle with zero average is zero there. The strong maximum principle makes
\(W\) zero on all of \(\Omega\). If \(c<0\), apply the same argument to
\(-h\). Consequently, in every case,

\[
 W_0(z)=cU(z)\qquad(z\notin H). \tag{19}
\]

For the polynomial consequence, form the compactly supported finite real
signed measure \(\lambda=h\,m|_H-c\nu\). Its mass is zero, and (19) says its
logarithmic potential is zero outside a disk. For \(|z|\) larger than twice
that disk's radius, uniform absolute convergence gives

\[
 0=\int\log|z-w|\,d\lambda(w)
   =-\operatorname{Re}\sum_{n\geq1}
       \frac{z^{-n}}{n}\int w^n\,d\lambda(w). \tag{20}
\]

The power series in \(\zeta=1/z\) is analytic near zero, has zero real part,
and vanishes at zero. It is identically zero, so every complex moment in
(20) vanishes. The zero-th moment is the zero mass already established.
Therefore

\[
 \int_H h(z)\operatorname{Re}P(z)\,dm(z)
   =c\int_T\operatorname{Re}P(w)\,d\nu(w)=0. \tag{21}
\]

Every vector in \(\mathcal V^\perp\) thus annihilates
\(\operatorname{Re}P\). The Hilbert-space identity
\((\mathcal V^\perp)^\perp=\overline{\mathcal V}\) proves the claim.

**Formal pointers.** `AdjointPotential` and `SourceDensity` provide
continuity, the adjoint identity, and vanishing on support.
`AdjointUniqueness`:
`adjointAreaPotential_eq_mass_mul_source_potential_of_annihilator` and
`integral_area_mul_re_polynomial_eq_mass_mul_source_integral_of_annihilator`.
`PotentialMoments`: `polynomial_integrals_eq_of_log_density_potential_eq`.
`DensityOperator` supplies the orthogonal-complement closure criterion;
`PolynomialDensity`: `exists_density_approx_re_polynomial`.

## 8. A mean-zero polynomial positive off a small strip

Fix \(M\geq1\) with \(H\subseteq\overline B(0,M)\). Given \(0<a<M\), put

\[
 K_a=\{z:|z|\leq M,\ |\operatorname{Im}z|\geq a\}.
\]

We construct a polynomial \(Q\) with \(Q(0)=1\) and \(|Q|<1/4\) on \(K_a\).
Let \(\mathcal A\) be the uniform closure there of complex polynomials.
It is a closed unital subalgebra of \(C(K_a;\mathbb C)\). If \(f\in\mathcal A\)
and \(\|f\|_\infty<1\), the geometric series puts \((1-f)^{-1}\) in
\(\mathcal A\). For real \(b\), put \(r_b(z)=(b-z)^{-1}\). There is no pole
on \(K_a\), and \(\|r_b\|_\infty\leq1/a\). If \(b>M\), expansion in \(z/b\)
gives \(r_b\in\mathcal A\). Whenever \(|t|<a\), the identity

\[
 r_{b-t}=r_b(1-tr_b)^{-1}
\]

keeps the resolvent in \(\mathcal A\). Choose \(b=N(a/2)>M\) and move the
pole in \(N\) steps of size \(a/2\). Thus \(r_0(z)=-1/z\) belongs to
\(\mathcal A\). Choose a polynomial \(q\) with
\(\|q+1/z\|_{K_a}<1/(8M)\) and put \(Q(z)=1+zq(z)\). Then \(Q(0)=1\), and
\(|Q(z)|<1/8<1/4\) on \(K_a\).

For a unit complex number \(u\), set

\[
 A(u)=\int_T\operatorname{Re}Q(uw)\,d\nu(w).
\]

Its mean over the unit circle is \(\operatorname{Re}Q(0)=1\), since every
nonconstant polynomial term has zero angular mean. Continuity supplies a
rotation \(u\) with \(A(u)\geq1\). The real part

\[
 H_0(z)=\operatorname{Re}(A(u)-Q(uz))
\]

is a harmonic polynomial with source mean zero. Inside \(|z|\leq M\), it
is greater than \(3/4\) whenever \(|\operatorname{Im}(uz)|\geq a\). The
rotated strip within that disk has area at most \(4Ma\), by containment
in a rotated rectangle of side lengths \(2M\) and \(2a\). Choosing \(a\)
sufficiently small therefore makes

\[
 m\{z:|z|\leq M,\ H_0(z)\leq3/4\}
\]

as small as prescribed.

**Formal pointers.** `CapPolynomial`: `closed_subalgebra_geometric_inverse_mem`,
`capResolvent_far_mem`, `capResolvent_step_mem`, `capResolvent_zero_mem`,
`exists_cap_polynomial`. `CapRotation`:
`exists_unit_rotation_mean_ge_constant`, `volume_rotated_strip_le`,
`exists_mean_zero_polynomial_large_off_small_area`.

## 9. A probability with a positive margin on almost all the area

Fix the desired \(\varepsilon>0\), and let \(B=\overline B(0,M+1)\). Choose
section 8's polynomial so that its bad set in \(|z|\leq M\) has area less
than \(\varepsilon/8\). By section 7, choose bounded measurable real \(f\)
on \(T\) whose potential \(V=V_f\) satisfies

\[
 \|V-H_0\|_{L^2(H)}^2<\varepsilon/128.
\]

If \(H_0>3/4\) and \(V<1/2\), then \(|V-H_0|>1/4\). Chebyshev gives

\[
 \begin{aligned}
 m\{z\in H:V(z)<1/2\}
 &\leq m\{z\in H:H_0(z)\leq3/4\}
       +16\|V-H_0\|_{L^2(H)}^2\\
 &<\varepsilon/4. \tag{22}
 \end{aligned}
\]

Choose \(C\geq0\) with \(|f|\leq C\), and put \(A_0=C+1\). The measurable
sets

\[
 E_n=\{z\in B\setminus H:V(z)+(A_0+n)U(z)<1/2\}
\]

decrease with \(n\) and have empty intersection. Indeed \(U>0\) outside
\(H\), where the compact-source density potential \(V\) is finite.
Since \(m(B)<\infty\), continuity from above gives \(m(E_n)\to0\).
Choose \(n\) with \(m(E_n)<\varepsilon/4\), and write \(A=A_0+n\).

The measure

\[
 d\sigma(w)=\frac{f(w)+A}{m_A}\,d\nu(w),\qquad
 m_A=A+\int_T f\,d\nu>0 \tag{23}
\]

is an actual probability on \(T\), since \(A>C\). Its potential satisfies
the area-almost-everywhere identity on \(B\)

\[
 U_\sigma(z)=\frac{V(z)+AU(z)}{m_A}. \tag{24}
\]

On \(H\), (16) and \(A\geq0\) give \(V+AU\geq V\); outside \(H\), the
exceptional set is the selected \(E_n\). Hence, with
\(\delta=1/(2m_A)>0\), equations (22)-(24) give

\[
 m\{z\in B:U_\sigma(z)<\delta\}<\varepsilon/2. \tag{25}
\]

This argument includes all of \(H\), even a boundary of positive area.
It uses no boundary collar, no conversion of polar exceptions into an area
claim, and no assertion that \(U=0\) on \(H\). The positive margin
\(\delta\) is established before discrete sampling.

**Formal pointers.** `PositiveDensity`: `shifted_density_mass_pos`,
`isProbabilityMeasure_shifted_density`, `integral_shifted_density`.
`ConditionalLemniscate`: `exists_L2_tolerance_for_small_sublevel_set`,
`exists_large_shift_small_exterior_set`, `shifted_source_potential_ae_eq`,
`hasArbitrarilySmallLemniscates_of_potential_properties`.

## 10. Equal-weight sampling and actual permitted roots

The continuous Banach-valued kernel \(\kappa_B:T\to L^2(B,m;\mathbb R)\)
is integrable against \(\sigma\). The Banach-valued strong law for independent
samples from \(\sigma\) provides a sequence of actual points in \(T\) whose
equal-weight kernel averages converge in norm to
\(\int_T\kappa_B\,d\sigma=[U_\sigma]\). Thus, for every \(r>0\), there are
a positive \(N\) and \(w_1,\ldots,w_N\in T\) such that

\[
 \left\|\frac1N\sum_{j=1}^{N}\kappa_B(w_j)-[U_\sigma]\right\|_2<r.
 \tag{26}
\]

Repetitions are permitted. The strong law is applied to this single
specified \(L^2\)-valued kernel.

Put \(v_N(z)=N^{-1}\sum_j\log|z-w_j|\), using totalized finite logarithms
at the finitely many roots for its area representative. Equation (17)
identifies the norm in (26) with \(\|v_N-U_\sigma\|_{L^2(B)}\). The
elementary sign-transfer estimate is

\[
 m\{z\in B:v_N(z)<0\}
 \leq m\{z\in B:U_\sigma(z)<\delta\}
       +\delta^{-2}\|v_N-U_\sigma\|_{L^2(B)}^2. \tag{27}
\]

A point with \(v_N<0\) and \(U_\sigma\geq\delta\) has error at least
\(\delta\), and Chebyshev bounds that error set. Choose the tolerance in
(26) so that \(r^2<\delta^2\varepsilon/2\). Equations (25) and (27) then
give area strictly less than \(\varepsilon\).

Set \(p(z)=\prod_j(z-w_j)\). Outside the finite root set,

\[
 \log|p(z)|=Nv_N(z),
\]

so \(L(p)\) and \(\{v_N<0\}\) differ only on an area-null set. All roots
have modulus at most \(M\). If \(|z|>M+1\), every \(|z-w_j|>1\), so
\(|p(z)|\geq1\). Thus \(L(p)\subseteq B\). Its global area is exactly the
area bounded in (27), and is less than \(\varepsilon\).

The degree is the positive integer \(N\), the product is monic, and every
complex root is one of the selected \(w_j\in T\subseteq S\). This proves
the compact conclusion whenever (9) holds, and hence both the compact
geometric theorem and the compact capacity corollary.

**Formal pointers.** `AtomicApproximation`:
`exists_sample_sequence_tendsto_integral`, `exists_equal_weight_average_on_compact`.
`DiscretePotential` and `SourcePotential` identify atomic and source
area classes. `AtomicPotential`:
`unitLemniscate_ae_eq_atomicLogPotential_neg`.
`AreaTransfer`: `measure_neg_le_margin_add_sq_eLpNorm`.
`AtomicAreaAssembly`: `unitLemniscate_subset_closedBall_of_roots_norm_le`,
`exists_roots_small_area_of_source_margin`.
`NonnegativePotentialLemniscate`:
`hasArbitrarilySmallLemniscates_of_nonnegative_source_potential`.
`CompactLemniscate`: `hasArbitrarilySmallLemniscates_of_finite_minimizer`
and `hasArbitrarilySmallLemniscates_of_one_le_transfiniteDiameter`.
`CapacityTheorem`: `hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity`
and `erdos1040_capacity_one`.

## 11. Unbounded sources and the full closed-set theorem

If \(F\) is unbounded, choose \(a,b\in F\) with separation \(L=|a-b|>0\)
as large as needed. For every \(z\), the triangle inequality puts at least
one of \(|z-a|\), \(|z-b|\) at or above \(L/2\). If
\(|(z-a)(z-b)|<1\), the other distance is less than \(2/L\). Consequently

\[
 L((z-a)(z-b))\subseteq B(a,2/L)\cup B(b,2/L),\qquad
 m(L((z-a)(z-b)))\leq\frac{8\pi}{L^2}. \tag{28}
\]

A sufficiently large separation makes this less than \(\varepsilon\).
The polynomial has degree two, is monic, and both roots are in \(F\).
This argument applies to every unbounded \(F\).

Finally let \(F\) satisfy the full theorem's hypotheses. If it is bounded,
closedness makes it compact, and the compact geometric theorem applies.
If it is unbounded, use (28). In either case an actual monic polynomial
of positive degree, with all complex roots in \(F\), satisfies (1).
The stated infinitude hypothesis is retained in the full theorem; the
proof does not need to invoke it separately.

**Formal pointers.** `Unbounded`: `volume_quadratic_sublevel_le`,
`unbounded_hasArbitrarilySmallLemniscates`. `PolynomialConclusion`:
`HasArbitrarilySmallLemniscates.mono`, `exists_monic_polynomial_small_area`.
`FullTheorem`: **`erdos1040`**.


## 12. Formal verification and exact scope

The accompanying project uses Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The recorded final audit of 5 September 2026 passed for 274 tracked declarations: 241 theorems and 33 definitions in 52 declaration-bearing modules. There are 54 owned Lean source files, including the import root and trusted-core index. The checker builds every owned module, prints each tracked signature and axiom list, inventories generated kernel declarations, checks dependency revisions and tracked cleanliness, and checks version-bound correspondence-review records. Only `propext`, `Classical.choice` and `Quot.sound` appear as allowed foundational axioms.

The primary endpoints are `Erdos1040.erdos1040` and `Erdos1040.erdos1040_capacity_one`. The exact zero-infimum formulations are `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter` and `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity`.

All roots belong to the original source, repeated roots are permitted, polynomial degree is positive, the sublevel condition is strict, and area means planar Lebesgue measure. No boundary regularity, connectedness, finite-energy probability or desired potential inequality is an extra hypothesis of the final theorems. The proof supplies no degree bound or computational running-time bound. It proves neither a general capacity-diameter equality nor any consequence concerning P versus NP.

The source archive includes the pinned lockfile, exact proof sources, declaration manifest, portable setup script, full checker, selected review documents, and a clearly labeled sanitized copy of the recorded audit. Source hashes bind the shipped proof to that audit. The README explains how to reproduce checks; the separate release verification note distinguishes new package testing from historical evidence. Existing correspondence reviewers were AI agents. Public posting and external mathematical acceptance remain separate from the local admission process.

## Appendix A. The capacity-only dependence question

The negative answer below was already known. In particular, Ghosh and Ramachandran [2, p.2] describe earlier countably infinite capacity-zero examples with different area infima and give positive-capacity examples. This appendix supplies an explicit Lean-checked pair of witnesses and relates the threshold theorem to the same area functional.

### Exact functional and answer

Let \(m\) be planar Lebesgue measure and define

\[
 M(F)=\inf\left\{m\{z\in\mathbb C:|p(z)|<1\}:
 p\in\mathbb C[z]\text{ is monic},\ \deg p>0,
 \text{every root of }p\text{ belongs to }F\right\}.
\]

The infimum is in \([0,\infty]\); no minimizing polynomial or attainment is
asserted. Repeated roots are allowed. Monic positive-degree polynomials over
\(\mathbb C\) are exactly the positive finite products used in Equation (1)
of the original paper. The Lean definition is
`Erdos1040.minimalLemniscateArea`; its proof-indexed infima exclude
inadmissible polynomials by assigning an empty conditional family infimum
\(+\infty\).

Set

\[
 S=\{0\}\cup\left\{\frac1{n+4}:n\in\mathbb N\right\},
 \qquad T=S\cup\{-4,4\}.
\]

Both sets are compact and infinite, hence satisfy the original closed
infinite domain. The construction proves

\[
 \rho(S)=\rho(T)=0,\qquad
 \operatorname{cap}(S)=\operatorname{cap}(T)=0,
 \qquad M(T)\le\frac\pi8<\frac{9\pi}{16}\le M(S).
\]

Here \(\rho\) is the actual geometric transfinite diameter and capacity is
the separate Robin-energy definition. Thus even on compact infinite sets,
the area infimum is not determined by either quantity alone.

### Compactness, countability and zero capacity

The sequence \(1/(n+4)\) is injective and tends to zero. Its range with its
limit adjoined is compact, countable and infinite, and lies in the closed
disk of radius \(1/4\). Adding the two points \(\pm4\) preserves the first
three properties.

For a countable source \(A\) and a positive scale \(D\), every probability
measure on \(A\) has infinite singular logarithmic energy. Indeed, finite
energy would imply that every singleton has measure zero, by the already
proved finite-energy non-atomicity theorem. Countable additivity would then
give total mass zero, contrary to probability mass one. Consequently the
Robin infimum is \(+\infty\) and the logarithmic capacity is zero. The
singular diagonal remains \(+\infty\) throughout this argument.

These statements and the properties of \(S\) are implemented in
`formal/Erdos1040/CountableSources.lean`.
The capacity identity is valid for the existing raw definition on countable
sets; its classical interpretation here concerns only the compact witnesses.

### Zero geometric transfinite diameter

We do not assume the general capacity–diameter equality. Instead, positive
dilation directly scales every geometric finite diameter and its infimum:

\[
 \delta_N(cA)=c\,\delta_N(A)\quad(N\ge2,\ c>0),\qquad
 \rho(cA)=c\,\rho(A).
\]

For a finite tuple, there are \(\binom N2\) pair distances, so multiplying
every point by \(c\) multiplies their product by \(c^{\binom N2}\). The
exponent \(2/[N(N-1)]\) converts this to a factor \(c\). The tuple-image
arguments preserve repeated entries, and multiplication by a positive
finite extended real commutes with the required supremum and infimum.

If a compact countable set \(A\) had \(\rho(A)>0\), compactness would make
this value finite. Dilating by \(1/\rho(A)\) would give a compact countable
set of geometric transfinite diameter one. The admitted geometric-to-energy
theorem supplies a finite-energy probability on that set, contradicting the
countability argument above. Thus \(\rho(A)=0\).

This proof is in
`formal/Erdos1040/GeometricScaling.lean`.
Its energy-existence premise was admitted before the present counterexample;
the argument does not depend on the counterexample itself.

### Different area bounds

If a monic polynomial \(p\) of degree \(N>0\) has all its roots in \(S\),
write \(p(z)=\prod_{j=1}^N(z-w_j)\), counting multiplicities. For
\(|z|<3/4\), each factor satisfies

\[
 |z-w_j|\le |z|+|w_j|\le |z|+1/4<1.
\]

Hence the strict unit sublevel of every admissible \(p\) contains the open
disk of radius \(3/4\), whose area is \(9\pi/16\). This proves the uniform
lower bound for \(M(S)\). The formal polynomial proof uses actual splitting
over \(\mathbb C\), preserves multiplicities, and requires positive degree.

For \(T\), take the actual monic quadratic \(q(z)=(z-4)(z+4)=z^2-16\).
Both its roots belong to \(T\), and the previously admitted quadratic area
bound gives

\[
 m\{|q|<1\}\le\frac{8\pi}{|4-(-4)|^2}=\frac\pi8.
\]

The area bounds are implemented in
`formal/Erdos1040/AreaObstruction.lean`.

### Formal endpoints and scope

`formal/Erdos1040/CapacityDependence.lean`
defines the area infimum and both source bounds, and proves:

- `Erdos1040.capacity_only_dependence_counterexample`: compact infinite
  witnesses with both size quantities zero and strictly different area infima.
- `Erdos1040.minimalLemniscateArea_not_determined_by_transfiniteDiameter`:
  no function of geometric transfinite diameter can give the area infimum
  for every closed infinite complex source.
- `Erdos1040.minimalLemniscateArea_not_determined_by_logarithmicCapacity`:
  the corresponding negation for every compact infinite complex source.

Together with the existing `Erdos1040.erdos1040` threshold theorem, these
give answers to both questions in original Problem 4. The new
`formal/Erdos1040/AreaInfimumEndpoints.lean`
also expresses the threshold answer using this same functional:
`Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter`
proves \(M(F)=0\) for every closed infinite \(F\) with \(\rho(F)\ge1\), and
`Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity`
proves \(M(F)=0\) for every compact \(F\) with capacity at least one.
Both are direct consequences of the previously admitted arbitrary-tolerance
polynomial results. They do not determine
the exact numerical values of \(M(S)\) or \(M(T)\), give degree or runtime
bounds, establish a general capacity–diameter equality, or imply a result
about P versus NP.

## References

1. P. Erdős, F. Herzog and G. Piranian, *Metric properties of polynomials* (1958), especially Equation (1), p.125, and Problem 4, p.135. [Original paper](https://users.renyi.hu/~p_erdos/1958-05.pdf).
2. S. Ghosh and K. Ramachandran, *A note on the Erdős minimal area problem*, arXiv:2604.03036, version 3, 27 August 2026. [Cited version](https://arxiv.org/abs/2604.03036v3).
3. M. Krishnapur, E. Lundberg and K. Ramachandran, *On the area of polynomial lemniscates*, arXiv:2503.18270, version 1, 24 March 2025, Theorem 6 and section 5. [Cited version](https://arxiv.org/abs/2503.18270v1).
4. E. B. Saff, *Logarithmic Potential Theory with Applications to Approximation Theory*, arXiv:1010.3760 (2010). [Paper](https://arxiv.org/abs/1010.3760).
5. T. F. Bloom, *Erdős Problem #1040*. [Problem page](https://www.erdosproblems.com/1040). Catalogue status and external acceptance may change independently of this version.
