# Independent correspondence review: EmpiricalEnergy

Reviewer: `formalization_preflight` (not the source author). Machine evidence: `formal/admissions/2026-09-05-energy-diameter-pre-admission-203.json`, checked 2026-09-05T05:48:38.649762+00:00, all 203 declarations machine PASS, main targets incomplete. I read the entire source and its current natural-language statements, checked each definition body where present, and independently printed every exact signature and axiom list. The combined 42 fresh messages for these three modules match the immutable snapshot exactly. Log: `formal/.audit/preflight-geometric-empirical-energy.log`, Lean exit 0. All declarations depend only on the standard allowed logical axioms.

Frozen source SHA-256: `a9a0a6ca326dc2a7aa39946516b4f93f7356dc4f7aeb7e7caf46dcc26b789bba`.

| Declaration | Exact correspondence review |
|---|---|
| `empiricalSourceProbability` | The actual measure is N inverse times the finite sum of the Dirac measures at the listed original-source points. N>0 is explicit and mass one is proved. Repeated points retain multiplicity. |
| `lintegral_empiricalSourceProbability` | Any ENNReal-valued source function, including infinite values, is integrated against that actual measure and equals its normalized finite sum. No integrability or distinctness is inserted. |
| `truncatedLogEnergy_empirical` | Tonelli on the actual product probability and two applications of the preceding integral identity give N inverse squared times the full ordered double sum. Both indices range over all roots, including equal indices. The natural truncation controls diagonal infinities. |
| `toReal_truncatedLogEnergy_empirical` | Every min(kernel,n) is explicitly finite before applying toReal to the two finite sums. This is an identity for bounded truncated energy, not a replacement of the full atomic energy. |
| `sum_truncated_kernel_le_of_log_sum_nonneg` | Distinct roots, pair distances<=D, D>=1, and nonnegative ordered off-diagonal log sum are explicit. The diagonal contributes exactly N*n. Off diagonal, the finite kernel is logD-logdist, and its truncation is no larger. The N(N-1) off-diagonal count is bounded by N squared using logD>=0. N=0 is allowed for this finite-sum inequality and correctly yields zero. |
| `truncatedLogEnergy_empirical_le_of_log_sum_nonneg` | Adds N>0 to form the probability and divide by N. The actual truncated energy is finite; the bound is exactly ofReal(logD+n/N), with nonnegativity justified before real conversion. |

No removed diagonal, changed measure, hidden finite-energy premise, added source point, omitted order restriction, or invalid real conversion was found. The full energy of a positive atomic probability remains infinite at positive scale; the proof never claims otherwise. The six registered statements pass correspondence review. Bindings: `preflight-empirical-energy-bindings.json`.
