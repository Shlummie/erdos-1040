# Independent logarithmic-kernel integrability correspondence review

Reviewed by the root agent, independently of the LogKernel author, on
2026-09-05 UTC. Source SHA-256:
`0a4125e7f8974c6e4f7b2db8c17174fe598092f330a1316c5837fbabbaa7c8f7`.
The five printed signatures and standard-only axiom lists were read from
the completed signature audit. This review is separate from the final
whole-project machine gate; concurrent changes elsewhere require a fresh run.

| Declaration | Exact correspondence |
| --- | --- |
| `Erdos1040.exists_pos_integrableOn_log_norm_sq_ball` | There exists a strictly positive real radius; the square of the real logarithm of the complex norm is integrable on the open planar ball at zero. No unmentioned regularity or capacity assumption. |
| `Erdos1040.locallyIntegrable_log_norm_sq` | The same real-valued squared function is locally integrable at every point of the complex plane for Lebesgue volume. |
| `Erdos1040.memLp_log_norm_of_isCompact` | Every compact complex set, including empty or positive-area sets, supports the stated restricted-area L2 class. The exponent is exactly 2. |
| `Erdos1040.memLp_log_norm_sub_of_isCompact` | The source is any complex number; the compact observation set is arbitrary. Translation is by minus the source and preserves planar volume. |
| `Erdos1040.memLp_log_norm_sub_closedBall` | The center, source, and real radius are universally quantified. Nonpositive-radius degeneracies are included; there is no positivity assumption on radius. |

The proof bounds the logarithm squared by an integrable inverse-radius
singularity near zero, uses ordinary continuity away from zero, then uses
compactness and measure-preserving translation. The domain has real
dimension two. This agrees with candidate Lemma 1's local integrability
requirement.

`Real.log 0 = 0` is a totalized representative. These are area L2 claims,
not pointwise claims that this value equals the extended logarithmic
singularity. They do not define equilibrium measures or logarithmic capacity,
and they do not establish source continuity or weak-measure approximation.
No weakening or extra assumption was found relative to these five recorded
supporting statements. The entire E1040-L2KERNEL claim is still larger.

Version-bound per-declaration records are in `root-logkernel-bindings.json`.
This review alone admits no theorem to the trusted core.
