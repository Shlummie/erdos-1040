# Erdős #1040: small-area polynomial lemniscates

Publishing name: **shlummi** (pen name).

[Read the paper](Erdos1040-Paper.pdf) · [Download the Lean source project](Erdos1040-Lean-Source.zip) · [Verification and review status](VERIFICATION.md)

This package presents an AI-assisted, Lean-verified proof of the threshold assertion in Erdős problem #1040. For every closed infinite complex set of geometric transfinite diameter at least one, it constructs monic polynomials of positive degree with all roots in that set and strict unit lemniscates of arbitrarily small planar Lebesgue area. It also proves this conclusion for every compact set of logarithmic capacity at least one, including arbitrary compact capacity-one sets.

The paper includes an explicit formalized counterexample to the separate capacity-only dependence question. That negative answer was already known and is not claimed as new. No polynomial degree or runtime bound follows from the proof.

## Read or reproduce

- The PDF contains the mathematical argument, formal theorem pointers, references, and AI disclosure.
- `Erdos1040-Lean-Source.zip` expands to one complete project folder, with 54 owned Lean source files, a pinned dependency manifest, the original checker, and reproduction instructions. Dependencies are downloaded separately; this is not an offline binary bundle.
- Start with the `README.md` and `REPRODUCING.md` inside that ZIP. Readers can verify the shipped hashes before running the build.
- `SHA256SUMS.txt` records the exact PDF, source ZIP and descriptive files in this release.

The project pins Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Recorded checks cover 274 tracked declarations: 241 theorems and 33 definitions across 52 declaration-bearing modules. Kernel checks and mathematical correspondence review are documented separately.

## Review status and AI assistance

Proof development, formalization, documentation and correspondence reviews used AI assistance, including OpenAI Codex. Additional reports supplied by the project operator were attributed to DeepSeek and Claude/Opus. The records do not claim independent human peer review, journal acceptance, or acceptance by the Erdős Problems site. Please report a precise mathematical or formalization issue, with its theorem name or paper location, through this repository's Issues if enabled.

The public literature comparison is limited to the cited versions. No exhaustive novelty or priority determination is claimed. See [Erdős #1040](https://www.erdosproblems.com/1040), [Ghosh and Ramachandran, arXiv:2604.03036v3](https://arxiv.org/abs/2604.03036v3), and the paper's references.

No new reuse license has been assigned in this prepared package. Third-party dependencies retain their own licenses. Public availability alone is not a grant of an open-source license.
