# Verification and review status

Release prepared 2026-09-06T02:20:23.402812+00:00. No upload, submission, journal acceptance, or Erdős-site acceptance is claimed by this file.

Publishing name: **shlummi** (pen name).

## Exact formal artifact

- Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- 54 owned Lean source files, containing 274 tracked declarations: 241 theorems and 33 definitions in 52 declaration-bearing modules.
- Historical final audit: `2026-09-05T19:16:33.633815+00:00`. Both `machine_checks_pass` and `main_target_complete` are true; errors are empty.
- Every shipped Lean file matches that audit's source hash. The claims manifest, toolchain, dependency lockfile and original checker retain their canonical bytes.
- Allowed foundational axioms: `propext`, `Classical.choice`, `Quot.sound`. No project-specific axioms or admitted proof placeholders are used.

## Package reproduction performed for this release

The exact source inputs were copied to an isolated directory on the original Windows host. The package preparation helper accepted all nine pinned dependency checkouts. Their already existing source checkouts and compiled caches were ordinary file copies; they were not fresh downloads or a fresh dependency rebuild.

The original full checker then rebuilt the project and completed its declaration inventory, signature, axiom, source-preservation and correspondence-binding checks. The new report is dated `2026-09-06T02:00:45.134369+00:00` and reports **Machine checks: PASS; Main target: COMPLETE**, with 274 tracked declarations and zero errors. All 54 source hashes, all 274 printed signatures and source statements, and all reported axiom lists agree with the historical final audit. The helper's fresh-network-fetch and cache-download branches were not exercised by this same-host test.

An initial run from a deeply nested Windows directory failed when a cached dependency filename reached 260 characters. The file existed and matched its source; using a shorter directory resolved this packaging issue. Windows readers should extract to a short writable path, such as `C:\e1040`. The failure and recovery remain in the local preparation records.

## Mathematical and review scope

The geometric theorem is `Erdos1040.erdos1040`; the compact capacity-one endpoint is `Erdos1040.erdos1040_capacity_one`. The source includes exact area-infimum corollaries and a formalized counterexample to the separate dependence assertion. The negative answer to that dependence assertion was already known.

Kernel validity of an exact Lean statement and its correspondence with an informal mathematical claim are separate assessments. The correspondence records were produced by AI agents and are bound to source/signature/statement hashes. Checking those bindings does not independently redo the human mathematical assessment. Independent human peer review is not claimed.

Additional reports supplied by the project operator were attributed to DeepSeek and Claude/Opus. Their raw transcripts are omitted; their existence is not used as a replacement for the machine-checkable artifact. Earlier Nanoda and kernel-replay evidence concerned the original threshold target closure and did not cover the later 34 supporting additions. This release does not enlarge that earlier scope.

The PDF retains the complete main proof and counterexample argument, with one document-cross-reference correction and typesetting changes. AI-assisted publication review found no mathematical omission. No exhaustive priority determination, general capacity-diameter equality, degree/runtime bound, or P-versus-NP conclusion is claimed.

## Public evidence and integrity

The source ZIP includes `evidence/recorded-audit.json` and `evidence/package-check.json`. Both are explicitly labeled sanitized derivatives: personal absolute paths were replaced, while mathematical fields and source hashes were preserved. Each records its original report's SHA-256. `formal/claims.json` holds the unchanged version-bound review notes; supplemental review documents may refer to historical artifacts not shipped here.

`MANIFEST.json` inside the source ZIP hashes all its other files. Run `python scripts/verify-files.py` after extraction to check them. `SHA256SUMS.txt` beside the PDF hashes the four public release files other than that checksum list. Hashes establish file identity, not mathematical acceptance.


## Packaging update 1.0.1, 2026-09-06T03:13:43.392601+00:00

The `source/` directory now makes the same formal project browsable on GitHub.
`Erdos1040-Lean-Source-v1.0.1.zip` also includes the previously omitted companion
`formal/reviews/cold-countable-sources-bindings-20260905.json`, which is linked
from the countable-source review. Its eight source/signature/statement bindings
match the already shipped claims manifest. The revised source manifest records
the added attachment. Every original source-archive file except that manifest
retains its original bytes, including all 54 Lean files, the checker, claims,
dependency pins and both audit records. File hashes, archive contents and
relative Markdown links were checked. No mathematical change or new kernel
execution is claimed for this packaging update.

The original PDF and source ZIP remain unchanged and available. The initial
five-file release, including its checksum list, is preserved at Git commit
`cc27bcde8bbe857d83c6c3b4ae537447739bf409`. The current `SHA256SUMS.txt` covers
the current root release files and `source/MANIFEST.json`; the latter hashes
the other 122 files in the browsable project and corrected source archive.

Erdős claim 269 was submitted under shlummi and was awaiting moderator approval
when inspected for this update. This is a publication record, not site acceptance
or independent human peer review.
