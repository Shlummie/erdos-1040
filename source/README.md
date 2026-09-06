# Reproducing the Erdős #1040 proof

Publishing name: **shlummi** (pen name).

This is the standalone source project accompanying *Small-area polynomial lemniscates with prescribed roots*. Extract this ZIP before running commands. On Windows, use a short writable path, such as `C:\e1040`, to avoid long dependency filenames exceeding a tool's path limit. Run commands from the extracted directory that contains `formal/`, `scripts/`, and `erdos-research/`.

## Quick verification

Install Python 3.9+, Git, and [Lean using elan](https://lean-lang.org/install/). Install the pinned version with:

```text
elan toolchain install leanprover/lean4:v4.33.1
```

Then run:

```text
python scripts/verify-files.py
python scripts/prepare-dependencies.py --cache
python scripts/check-formalization.py
```

Use `python3` instead of `python` where appropriate. Setup requires internet access. The preparation helper expects elan's default toolchain directory under your home directory; nonstandard installations need equivalent setup. Do not run `lake update`, which could replace the pinned dependency choices. Keep source-file line endings unchanged: review records bind raw source bytes, and `.gitattributes` disables normalization if you put this tree in Git.

Expected checker output:

```text
Machine checks: PASS
Main target: COMPLETE
```

Inspect `formal/.audit/report.json` and confirm that `machine_checks_pass` and `main_target_complete` are both `true`, `errors` is empty, and the 274 declarations pass their axiom and correspondence-binding checks. The report is generated on your machine; its absolute paths and execution time will differ from the published example. Details and the alternative dependency-source-build procedure are in [REPRODUCING.md](REPRODUCING.md).

## What to inspect

- `formal/Erdos1040/FullTheorem.lean`: `Erdos1040.erdos1040`, the closed infinite geometric threshold theorem.
- `formal/Erdos1040/CapacityTheorem.lean`: `Erdos1040.erdos1040_capacity_one` and the compact capacity-at-least-one conclusion.
- `formal/Erdos1040/AreaInfimumEndpoints.lean`: the two exact zero-area-infimum formulations.
- `formal/Erdos1040/CapacityDependence.lean`: the explicit known-dependence counterexample and functional-dependence negations.
- `formal/claims.json`: all intended statements and version-bound AI correspondence-review notes.
- `paper/Erdos1040-Paper.md`: editable release manuscript with all mathematical arguments and references.
- `evidence/`: the sanitized historical audit, provenance, and the separately labelled package reproduction check.
- `formal/reviews/`: selected supporting AI review documents referenced by the manifest. These can mention historical workspace artifacts not included here; their notes are supporting evidence, not extra Lean assumptions.

The isolated `erdos-research/CLAIMS_LEDGER.md` and `STATEMENT_MAP.md` are generated from all 274 unchanged manifest entries. They omit unrelated research history. Proof sources, the declaration manifest, checker, toolchain and lockfile retain their original bytes. The preserved source hashes and printed signatures identify exactly what was checked.

## Interpretation

Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` occur as allowed foundational axioms. A successful build proves the exact formal statements under the pinned dependencies. Agreement with the informal problem is a separate mathematical question. The recorded correspondence reviews were performed by AI agents; independent human peer review and public acceptance are not claimed.

The capacity-only negative answer is known in the literature. No degree or runtime bound, general capacity-diameter equality, or result about P versus NP is claimed. See the accompanying paper and [VERIFICATION.md](VERIFICATION.md) for the complete scope.

See [RIGHTS.md](RIGHTS.md) for release and third-party rights information.
