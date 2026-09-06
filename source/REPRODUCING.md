# Reproducing the Erdős #1040 formal artifact

Use a fresh extraction of the accompanying source archive. The archive should
contain `scripts/prepare-dependencies.py`, the original
`scripts/check-formalization.py`, `formal/`, and the research records referenced by
the checker. Run the commands below from the extracted repository root.

On Windows, use a short extraction path, for example `C:\e1040`. A deeply nested
test extraction made Lean/Lake unable to read an existing dependency cache file
whose absolute path was 260 characters; keep the extraction path short even
when Python and the archive tool can access longer paths.

Prerequisites are Python 3.9 or newer, Git on `PATH`, network access to the locked
repositories and mathlib cache, and the exact Lean toolchain
`leanprover/lean4:v4.33.1`, installed separately with elan. The cache helper expects
elan's default toolchain location under the current user's home directory, as
used by the original checker. It does not install or update Lean. On systems
where Python is named `python3`, substitute `python3` for `python` below.

```text
python scripts/prepare-dependencies.py --cache
python scripts/check-formalization.py
```

The first command fetches the exact nine Git revisions recorded in
`formal/lake-manifest.json` before requesting precompiled dependency artifacts.
This ordering matters: the original checker audits the dependency checkouts
before invoking Lake. The helper preserves the lock file bytes and refuses to
reset, repair, or delete an existing dependency with a different revision or
tracked changes. Ignored and untracked generated files are permitted, matching
the original checker's tracked-change test. A failed fresh fetch leaves its
partial directory for inspection; use a fresh extraction for another attempt.
Do not run `lake update` as part of reproduction.

The checker writes its report and logs to `formal/.audit/`. Inspect
`formal/.audit/report.json`, the build and axiom logs it references, and the
version-bound correspondence records. A successful process exit and
`machine_checks_pass: true` establish that the implemented declarations pass
the recorded machine gates. The separate `main_target_complete` field must also
be checked before describing the required target chain as complete. These
fields are conclusions about the exact artifact and its recorded claim scope.

This procedure is a cache-assisted reproduction of the project build and
audits. It does not establish that every dependency was rebuilt from source, or
that an independent clean-machine reproduction has already occurred. To attempt
a dependency source rebuild, start from another fresh extraction, omit
`--cache`, then run the original checker; sufficient build time, platform tools,
and resources may be needed. Report that stronger reproduction only after it
actually succeeds and its evidence has been reviewed.
