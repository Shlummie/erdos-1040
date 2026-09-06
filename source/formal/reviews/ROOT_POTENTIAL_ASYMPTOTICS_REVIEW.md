# Independent correspondence review: PotentialAsymptotics

Reviewer: root, 2026-09-05 UTC. Author: combinatorics_scout.
Source and exact signatures were read independently after the full machine PASS.
Bindings are in root-potential-asymptotics-bindings.json.

- abs_log_norm_sub_sub_log_norm_le: every complex z,w; positive observation norm and 2*norm(w)<=norm(z); exact absolute logarithm difference bound 2*norm(w)/norm(z). Equality in the radius comparison is allowed and the proof establishes nonzero z-w. The checked local complex-log estimate is used only inside norm<=1/2.
- integrable_log_density_potential_of_norm_lt: any source subtype S, nonnegative radius M bounding every source, arbitrary measure mu, real integrable density f, and strict norm(z)>2M. Conclusion is actual absolute integrability, not the totalized integral alone. No compactness or finite-measure assumption is needed in this bounded-source lemma.
- abs_log_density_potential_sub_mass_log_le: same hypotheses, exact actual integral minus real total mass times log norm(z), bounded by (2M/norm(z))*integral abs(f). Multiplication order agrees with real scalar arithmetic; f can have either sign.
- tendsto_log_density_potential_sub_mass_log: arbitrary compact S supplies the radius bound; arbitrary mu and integrable real f; actual mass-corrected potential tends to zero at the cocompact filter on C. In the finite-dimensional proper complex plane this is the usual norm-to-infinity limit. Source-set emptiness causes no unsupported existence assumption.
- tendsto_log_density_potential_of_integral_zero: exact additional hypothesis integral f=0; concludes convergence of the actual uncorrected potential to zero. Zero mass is explicit here and absent from the general theorem.

The arbitrary-measure statements strengthen the originally planned finite-measure interfaces: Integrable f guarantees finite total absolute density, so no infinite-measure loophole supplies the conclusion. All five use raw positive-log convention and no harmonicity/equilibrium/capacity premises. Compact-support singularities do not affect the exterior estimates and are not asserted integrable at all interior observations. These are supporting statements, not E1040-CAP1 or E1040-FULL. Every audited dependency uses only propext, Classical.choice, Quot.sound. No correspondence discrepancy found.
