# Independent equal-weight approximation correspondence review

Reviewed by the root agent independently of the proof author on 2026-09-05
UTC. Source SHA-256:
`3ae91e428d2374be76c419a75cb58c664b2df36124435e0bc9e3f761ea29c4ba`.
All three complete proofs and exact printed signatures were compared with
the manifest. The printed signatures and standard-only axiom lists are
preserved in `root-atomic-approximation-signatures.json`.

The first two theorems quantify over any measurable source space and any
complete real normed vector space equipped with its Borel measurable
structure. The measure is a probability. Measurability and Bochner
integrability of the supplied kernel are explicit hypotheses. No separability
or finite-dimensionality hypothesis is present. The product probability
space supplies independent samples with exactly the original law; the
Banach-valued strong law gives norm convergence of their prefix means.
An almost-sure witness exists because the product measure is a probability.

`exists_sample_sequence_tendsto_integral` uses the exact coefficients
`(n : real)^(-1)` and the prefix of length n. Its zero-length expression is
totalized to zero; the assertion is convergence as n tends to infinity.

`exists_equal_weight_average` chooses n at least one and at least the
convergence threshold. Its list is indexed by `Fin n`, so exactly n terms
receive coefficient 1/n. Repetitions are allowed. The norm error is strictly
less than the arbitrary positive tolerance. Neither arbitrary weights nor
external source points replace the asserted equal-weight average.

`exists_equal_weight_average_on_compact` uses the original compact complex
set as a subtype. Every source witness therefore lies in that set. Its
probability hypothesis excludes an impossible probability on the empty
subtype, without an extra nonemptiness assumption. Compactness and continuity
prove the required integrability and measurability; the codomain's canonical
Borel structure is introduced within the proof. The exposed signature has
only real Banach completeness, compactness, probability, continuity, and a
positive tolerance. It does not impose a boundary or separability condition.

No correspondence defect was found. These results establish norm
approximation for a supplied Banach-valued kernel. They provide neither a
quantitative rate nor literal weak convergence of probability measures for
all continuous tests simultaneously. A product Banach target may encode
several norms using the same sample list, but that application remains a
separate construction. The full Erdős target is not a consequence of these
three theorems alone.

Per-declaration bindings are in `root-atomic-approximation-bindings.json`.
The whole-project gate and trusted admission remain separate checks.
