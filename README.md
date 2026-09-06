# Erdős #1040: small-area polynomial lemniscates

Publishing name: **shlummi** (pen name).

[Read the paper](Erdos1040-Paper.pdf) · [Browse the Lean source](source/) · [Download the Lean source project (v1.0.1)](Erdos1040-Lean-Source-v1.0.1.zip) · [Verification and review status](VERIFICATION.md)

This package presents an AI-assisted, Lean-verified proof of the threshold assertion in Erdős problem #1040. For every closed infinite complex set of geometric transfinite diameter at least one, it constructs monic polynomials of positive degree with all roots in that set and strict unit lemniscates of arbitrarily small planar Lebesgue area. It also proves this conclusion for every compact set of logarithmic capacity at least one, including arbitrary compact capacity-one sets.

The paper includes an explicit formalized counterexample to the separate capacity-only dependence question. That negative answer was already known and is not claimed as new. No polynomial degree or runtime bound follows from the proof.

## Read or reproduce

- The PDF contains the mathematical argument, formal theorem pointers, references, and AI disclosure.
- [Erdos1040-Lean-Source-v1.0.1.zip](Erdos1040-Lean-Source-v1.0.1.zip) expands to one complete project folder, with 54 owned Lean source files, a pinned dependency manifest, the original checker, and reproduction instructions. Dependencies are downloaded separately; this is not an offline binary bundle.
- Read the [source README](source/README.md) and [reproduction instructions](source/REPRODUCING.md) online, or open the same files after extracting the ZIP. Readers can verify the shipped hashes before running the build.
- [SHA256SUMS.txt](SHA256SUMS.txt) records the current public release files. The [source manifest](source/MANIFEST.json) records the individual source-package files.

The project pins Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Recorded checks cover 274 tracked declarations: 241 theorems and 33 definitions across 52 declaration-bearing modules. Kernel checks and mathematical correspondence review are documented separately.

## Start with the exact theorem statements

The source links below open the declarations directly. The [declaration manifest](source/formal/claims.json) records their intended statements and version-bound AI correspondence-review notes.

| Result | Lean declaration |
| --- | --- |
| Closed infinite geometric threshold | [`Erdos1040.erdos1040`](source/formal/Erdos1040/FullTheorem.lean#L18) |
| Arbitrary compact capacity-one case | [`Erdos1040.erdos1040_capacity_one`](source/formal/Erdos1040/CapacityTheorem.lean#L27) |
| Exact zero-infimum geometric threshold | [`Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter`](source/formal/Erdos1040/AreaInfimumEndpoints.lean#L29) |
| Exact zero-infimum compact capacity-at-least-one case | [`Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity`](source/formal/Erdos1040/AreaInfimumEndpoints.lean#L35) |
| Explicit counterexample to dependence | [`Erdos1040.capacity_only_dependence_counterexample`](source/formal/Erdos1040/CapacityDependence.lean#L66) |
| Negation of dependence only on transfinite diameter | [`Erdos1040.minimalLemniscateArea_not_determined_by_transfiniteDiameter`](source/formal/Erdos1040/CapacityDependence.lean#L84) |
| Negation of dependence only on logarithmic capacity, for compact infinite sources | [`Erdos1040.minimalLemniscateArea_not_determined_by_logarithmicCapacity`](source/formal/Erdos1040/CapacityDependence.lean#L93) |

## Packaging update v1.0.1

Version 1.0.1 adds the [countable-source review's companion binding records](source/formal/reviews/cold-countable-sources-bindings-20260905.json), which were omitted from the original ZIP, and makes the source browsable on GitHub. The archive manifest and public documentation have been updated accordingly.

This is a packaging correction. All 54 Lean files, the checker, claims manifest, toolchain and dependency pins, and recorded audit files retain their original bytes. The mathematical paper and 274 audited declarations are unchanged. No new proof test or Lean execution is claimed by this update.

The [original frozen submission archive](Erdos1040-Lean-Source.zip) remains available. Its [original checksums and release context](https://github.com/Shlummie/erdos-1040/blob/cc27bcde8bbe857d83c6c3b4ae537447739bf409/SHA256SUMS.txt) are preserved at the original publication commit.

## Review status and AI assistance

Proof development, formalization, documentation and correspondence reviews used AI assistance, including OpenAI Codex. Additional reports supplied by the project operator were attributed to DeepSeek and Claude/Opus. The records do not claim independent human peer review, journal acceptance, or acceptance by the Erdős Problems site. Please report a precise mathematical or formalization issue, with its theorem name or paper location, through this repository's Issues if enabled.

The public literature comparison is limited to the cited versions. No exhaustive novelty or priority determination is claimed. See [Erdős #1040](https://www.erdosproblems.com/1040), [Ghosh and Ramachandran, arXiv:2604.03036v3](https://arxiv.org/abs/2604.03036v3), and the paper's references.

No new reuse license has been assigned in this prepared package. Third-party dependencies retain their own licenses. Public availability alone is not a grant of an open-source license.
