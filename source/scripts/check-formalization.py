#!/usr/bin/env python3
"""Build and audit the owned Lean project without admitting mathematical claims.

Run from any directory. Reports are local to formal/.audit. A zero exit status
means the implemented declarations pass the machine gates; main_target_complete
is a separate field and also requires version-bound correspondence reviews.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"
AUDIT = FORMAL / ".audit"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.1"
EXPECTED_MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXCLUDED_DIRS = {".git", ".lake", "node_modules", "__pycache__"}
NAME = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|constant|structure|inductive|class|instance)"
    r"\s+(?P<name>" + NAME + r")", re.MULTILINE)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def axiom_base_name(name: str) -> str:
    """Remove only the pretty-printer's trailing universe annotation."""
    return re.sub(r"\.\{[^{}]*\}$", "", name)


def mask_comments_strings(text: str) -> str:
    """Mask Lean strings, line comments, and nested block comments; retain lines."""
    chars = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                chars[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                chars[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if chars[i] not in "\r\n":
                    chars[i] = " "
                i += 1
        elif text.startswith("--", i):
            while i < len(text) and text[i] not in "\r\n":
                chars[i] = " "
                i += 1
        elif text.startswith("/-", i):
            chars[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text[i] == '"':
            chars[i] = " "
            i += 1
            while i < len(text):
                c = text[i]
                if chars[i] not in "\r\n":
                    chars[i] = " "
                i += 1
                if c == "\\" and i < len(text):
                    if chars[i] not in "\r\n":
                        chars[i] = " "
                    i += 1
                elif c == '"':
                    break
        else:
            i += 1
    return "".join(chars)


def owned_sources() -> list[Path]:
    result = []
    for base, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in EXCLUDED_DIRS and Path(base) / d != AUDIT]
        for name in files:
            if name.endswith(".lean"):
                result.append(Path(base) / name)
    return sorted(result)


def run(command: list[str], log: Path, timeout: int, env: dict[str, str]) -> dict:
    try:
        with log.open("w", encoding="utf-8", newline="\n") as stream:
            result = subprocess.run(command, cwd=FORMAL, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=timeout, check=False)
        return {"command": command, "exit_code": result.returncode,
                "log": str(log.relative_to(ROOT))}
    except (OSError, subprocess.TimeoutExpired) as exc:
        with log.open("a", encoding="utf-8") as stream:
            stream.write("\nCHECKER ERROR: " + str(exc) + "\n")
        return {"command": command, "exit_code": None, "error": str(exc),
                "log": str(log.relative_to(ROOT))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    args = parser.parse_args()
    if args.timeout_seconds < 1:
        parser.error("--timeout-seconds must be positive")
    AUDIT.mkdir(parents=True, exist_ok=True)
    errors: list[str] = []
    report = {"schema_version": 1, "checked_at_utc": datetime.now(timezone.utc).isoformat(),
              "machine_checks_pass": False, "main_target_complete": False,
              "errors": errors, "declarations": [], "source_inventory": []}

    def finish() -> int:
        (AUDIT / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n",
                                          encoding="utf-8")
        for error in errors:
            print("FAIL:", error)
        print("Machine checks:", "PASS" if report["machine_checks_pass"] else "FAIL")
        print("Main target:", "COMPLETE" if report["main_target_complete"] else "INCOMPLETE")
        print("Report:", AUDIT / "report.json")
        return 0 if report["machine_checks_pass"] else 1

    try:
        manifest_bytes = (FORMAL / "claims.json").read_bytes()
        lock_bytes = (FORMAL / "lake-manifest.json").read_bytes()
        toolchain_bytes = (FORMAL / "lean-toolchain").read_bytes()
        lakefile_bytes = (FORMAL / "lakefile.toml").read_bytes()
        manifest = json.loads(manifest_bytes.decode("utf-8-sig"))
        lock = json.loads(lock_bytes.decode("utf-8-sig"))
        report["claims_manifest_sha256"] = digest(manifest_bytes)
        report["lean_toolchain_sha256"] = digest(toolchain_bytes)
        report["lakefile_sha256"] = digest(lakefile_bytes)
        toolchain = toolchain_bytes.decode("utf-8-sig").strip()
        if manifest.get("schema_version") != 1:
            errors.append("claims.json schema_version must be 1")
        if toolchain != EXPECTED_TOOLCHAIN:
            errors.append("Unexpected Lean toolchain: " + toolchain)
        packages = lock.get("packages", [])
        mathlib = [p for p in packages if p.get("name") == "mathlib"]
        if len(mathlib) != 1 or mathlib[0].get("rev") != EXPECTED_MATHLIB:
            errors.append("Mathlib lock revision does not match the authorized pin")
        if any(p.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", p.get("rev", ""))
               for p in packages):
            errors.append("Every dependency must have a pinned 40-character git revision")
        entries = manifest["declarations"]
        if not isinstance(entries, list) or not entries:
            errors.append("claims.json must track at least one declaration")
            return finish()
        prefix = manifest["namespace_prefix"]
        required = manifest["required_targets"]
        if required != ["E1040-CAP1", "E1040-FULL"]:
            errors.append("Required target IDs must remain E1040-CAP1 and E1040-FULL")
        if prefix != "Erdos1040":
            errors.append("Namespace prefix must remain Erdos1040")
        ledger = (ROOT / "erdos-research/CLAIMS_LEDGER.md").read_text(encoding="utf-8")
        statement_map = (ROOT / "erdos-research/STATEMENT_MAP.md").read_text(encoding="utf-8")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        errors.append("Project metadata cannot be read: " + str(exc))
        return finish()

    names: set[str] = set()
    for entry in entries:
        try:
            name, module = entry["name"], entry["module"]
            if not re.fullmatch(NAME, name) or not name.startswith(prefix + "."):
                errors.append("Invalid tracked declaration name: " + str(name))
            if not re.fullmatch(NAME, module):
                errors.append("Invalid module: " + str(module))
            if name in names:
                errors.append("Duplicate tracked declaration: " + name)
            names.add(name)
            if entry["kind"] == "def":
                entry["kind"] = "definition"
            if entry["kind"] not in {"definition", "theorem"}:
                errors.append("Invalid kind for " + name)
            if entry["role"] not in {"supporting", "target"}:
                errors.append("Invalid role for " + name)
            if entry["correspondence_status"] not in {"pending", "reviewed"}:
                errors.append("Invalid correspondence status for " + name)
            if not isinstance(entry["source_statement"], str) or not entry["source_statement"].strip():
                errors.append("Missing mathematical source statement for " + name)
            for label, record in (("claims ledger", ledger), ("statement map", statement_map)):
                if entry["claim_id"] not in record or name not in record:
                    errors.append(f"{name} or its claim ID is absent from the {label}")
            if not (FORMAL / (module.replace(".", "/") + ".lean")).is_file():
                errors.append("Missing source module for " + name)
        except (KeyError, TypeError, AttributeError) as exc:
            errors.append("Malformed declaration entry: " + str(exc))
    if errors:
        return finish()

    modules: set[str] = set()
    forbidden = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|constant|native_decide|implemented_by)\b"
                           r"|\bdebug\.skipKernelTC\b|\bopaque\b")
    found_names: set[str] = set()
    for path in owned_sources():
        relative = path.relative_to(ROOT).as_posix()
        source = path.read_text(encoding="utf-8-sig")
        masked = mask_comments_strings(source)
        for match in forbidden.finditer(masked):
            line = masked.count("\n", 0, match.start()) + 1
            errors.append(f"Forbidden proof construct {match.group()!r}: {relative}:{line}")
        report["source_inventory"].append({"path": relative, "sha256": digest(path.read_bytes())})
        if path.is_relative_to(AUDIT) or path.name == "lakefile.lean":
            continue
        if not path.is_relative_to(FORMAL):
            errors.append("Owned Lean source is outside the audited formal project: " + relative)
            continue
        module = ".".join(path.relative_to(FORMAL).with_suffix("").parts)
        if not re.fullmatch(NAME, module):
            errors.append("Owned Lean source has an invalid module name: " + relative)
            continue
        modules.add(module)
        # Source commands locate explicit owned declarations. Generated kernel
        # auxiliaries are checked transitively by the owning theorem's axiom audit.
        for match in DECLARATION.finditer(masked):
            short_name = match.group("name")
            candidates = [e for e in entries if e["module"] == module and
                          (e["name"] == short_name or e["name"].endswith("." + short_name))]
            line = masked.count("\n", 0, match.start()) + 1
            if len(candidates) != 1:
                errors.append(f"Untracked or ambiguous owned declaration {short_name}: {relative}:{line}")
            else:
                declared_kind = "theorem" if match.group("kind") in {"theorem", "lemma"} else "definition"
                if candidates[0]["kind"] != declared_kind:
                    errors.append("Manifest kind disagrees with source for " + candidates[0]["name"])
                found_names.add(candidates[0]["name"])
    for name in sorted(names - found_names):
        errors.append("Tracked declaration lacks an explicit source declaration: " + name)
    report["source_scan_pass"] = not errors
    if errors:
        return finish()

    env = os.environ.copy()
    direct_bin = Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1/bin"
    lake = direct_bin / ("lake.exe" if os.name == "nt" else "lake")
    if lake.is_file():
        env["PATH"] = str(direct_bin) + os.pathsep + env.get("PATH", "")
        lake_command = str(lake)
    else:
        lake_command = shutil.which("lake") or "lake"
    report["dependency_inventory"] = []
    for package in packages:
        package_path = FORMAL / lock.get("packagesDir", ".lake/packages") / package["name"]
        item = {"name": package["name"], "expected_revision": package["rev"]}
        try:
            revision = subprocess.run(["git", "-C", str(package_path), "rev-parse", "HEAD"],
                                      capture_output=True, text=True, timeout=60, check=False)
            status = subprocess.run(["git", "-C", str(package_path), "status", "--porcelain",
                                     "--untracked-files=no"], capture_output=True, text=True,
                                    timeout=60, check=False)
            item["actual_revision"] = revision.stdout.strip()
            item["tracked_changes"] = status.stdout.splitlines()
            item["pass"] = revision.returncode == 0 and status.returncode == 0 and not status.stdout and (
                revision.stdout.strip() == package["rev"])
        except (OSError, subprocess.TimeoutExpired) as exc:
            item.update({"pass": False, "error": str(exc)})
        if not item["pass"]:
            errors.append("Dependency is missing, modified, or at an unexpected revision: " + package["name"])
        report["dependency_inventory"].append(item)
    if errors:
        return finish()
    report["toolchain"] = toolchain
    report["mathlib_revision"] = EXPECTED_MATHLIB
    report["lake_manifest_sha256"] = digest((FORMAL / "lake-manifest.json").read_bytes())
    report["build"] = run([lake_command, "build", *sorted(modules)],
                          AUDIT / "build.log", args.timeout_seconds, env)
    if report["build"]["exit_code"] != 0:
        errors.append("Lean project build failed; see formal/.audit/build.log")
        return finish()

    lines = ["import Lean"] + ["import " + module for module in sorted(modules)]
    lines += ["set_option pp.universes true", "set_option pp.fullNames true",
              "set_option pp.proofs false", "set_option format.width 120"]
    command_lines: dict[int, tuple[str, str]] = {}
    for entry in entries:
        for command, label in (("#print sig ", "signature"), ("#print axioms ", "axioms")):
            lines.append(command + entry["name"])
            command_lines[len(lines)] = (entry["name"], label)
    # Inventory the actual imported kernel environment, including declarations
    # created by commands or macros that a source-token inventory cannot see.
    own_module_names = ", ".join("`" + module for module in sorted(modules))
    lines += ["open Lean Elab Command in", "run_cmd do", "  let env ← getEnv",
              "  let ownedModules : List Name := [" + own_module_names + "]",
              "  for idx in [:env.header.moduleData.size] do",
              "    let owner := env.allImportedModuleNames[idx]!",
              "    if ownedModules.contains owner then",
              "      for info in env.header.moduleData[idx]!.constants do",
              "        let name := info.name",
              "        let ranges ← findDeclarationRanges? name",
              '        let kind := if info.isTheorem then "theorem" else if info.isAxiom then "axiom" else "definition"',
              "        let axs ← collectAxioms name",
              '        logInfo m!"OWNED|{name}|{owner}|{kind}|{ranges.isSome}|{info.isUnsafe}|{axs.toList}"']
    audit_file = AUDIT / "Audit.lean"
    audit_file.write_text("\n".join(lines) + "\n", encoding="utf-8")
    report["audit"] = run([lake_command, "env", "lean", "--json", str(audit_file)],
                          AUDIT / "audit.log", args.timeout_seconds, env)
    if report["audit"]["exit_code"] != 0:
        errors.append("Lean signature/axiom audit failed; see formal/.audit/audit.log")
        return finish()
    results: dict[str, dict[str, str]] = {name: {} for name in names}
    report["kernel_inventory"] = []
    for line in (AUDIT / "audit.log").read_text(encoding="utf-8").splitlines():
        try:
            message = json.loads(line)
        except ValueError:
            continue
        if message.get("severity") == "error":
            errors.append("Lean audit emitted an error: " + str(message.get("data", "")))
        data = message.get("data", "")
        if data.startswith("OWNED|"):
            parts = data.split("|", 6)
            if len(parts) != 7:
                errors.append("Malformed kernel inventory output")
                continue
            _, owned_name, owner, kind, has_range, is_unsafe, owned_axioms = parts
            raw_axiom_names = [s.strip() for s in owned_axioms.strip("[]").split(",") if s.strip()]
            axiom_names = [axiom_base_name(name) for name in raw_axiom_names]
            # Lean generates equation and simplifier proof constants below the
            # owning explicit declaration. They have no source declaration
            # range; retain and audit them, while rejecting arbitrary untracked
            # constants even if a macro omitted their range information.
            generated_ancestor = next((name for name in names if re.fullmatch(
                re.escape(name) + r"\.(?:eq_[0-9]+|_simp_[0-9_]+|_proof_[0-9]+(?:_[0-9]+)*|congr_simp)",
                owned_name)), None)
            item = {"name": owned_name, "module": owner, "kind": kind,
                    "has_source_range": has_range == "true", "unsafe": is_unsafe == "true",
                    "axiom_names": axiom_names, "raw_axiom_names": raw_axiom_names,
                    "tracked": owned_name in names,
                    "compiler_generated_helper": has_range == "false" and generated_ancestor is not None,
                    "generated_ancestor": generated_ancestor}
            report["kernel_inventory"].append(item)
            if kind == "axiom" or item["unsafe"] or not set(axiom_names) <= ALLOWED_AXIOMS:
                errors.append("Unsafe or nonstandard owned kernel declaration: " + owned_name)
            if not item["tracked"] and not item["compiler_generated_helper"]:
                errors.append("Untracked owned kernel declaration: " + owned_name)
            if item["tracked"]:
                expected = next(e for e in entries if e["name"] == owned_name)
                if expected["module"] != owner or expected["kind"] != kind:
                    errors.append("Kernel declaration ownership or kind differs from manifest: " + owned_name)
        key = command_lines.get(message.get("pos", {}).get("line"))
        if key:
            name, label = key
            if label in results[name]:
                errors.append("Ambiguous audit output for " + name + " " + label)
            results[name][label] = message.get("data", "")

    kernel_names = {item["name"] for item in report["kernel_inventory"]}
    for name in sorted(names - kernel_names):
        errors.append("Tracked declaration absent from owned kernel inventory: " + name)

    for entry in entries:
        result = {**entry, **results[entry["name"]]}
        name = entry["name"]
        signature = result.get("signature", "")
        axiom_output = result.get("axioms", "")
        result["source_sha256"] = digest((FORMAL / (entry["module"].replace(".", "/") + ".lean")).read_bytes())
        result["signature_sha256"] = digest(signature.encode("utf-8"))
        result["statement_sha256"] = digest(entry["source_statement"].encode("utf-8"))
        if not signature:
            errors.append("No exact signature was printed for " + name)
        axiom_match = re.fullmatch(r"'" + re.escape(name) + r"' depends on axioms: \[(.*)\]", axiom_output, re.S)
        if axiom_output == f"'{name}' does not depend on any axioms":
            axiom_names = []
        elif axiom_match:
            axiom_names = [s.strip() for s in axiom_match.group(1).split(",") if s.strip()]
        else:
            axiom_names = ["<missing-or-unrecognized-audit>"]
        result["raw_axiom_names"] = axiom_names
        axiom_names = [axiom_base_name(name) for name in axiom_names]
        result["axiom_names"] = axiom_names
        result["axiom_audit_pass"] = set(axiom_names) <= ALLOWED_AXIOMS
        if not result["axiom_audit_pass"]:
            errors.append("Nonstandard or unaudited axioms for " + name + ": " + ", ".join(axiom_names))
        review = entry.get("review", {})
        result["correspondence_review_pass"] = entry["correspondence_status"] == "reviewed" and all(
            review.get(field) == result[field]
            for field in ("source_sha256", "signature_sha256", "statement_sha256")) and bool(
                review.get("reviewed_by")) and bool(review.get("notes"))
        if entry["correspondence_status"] == "reviewed" and not result["correspondence_review_pass"]:
            errors.append("Missing or stale version-bound correspondence review for " + name)
        report["declarations"].append(result)

    initial_sources = {item["path"]: item["sha256"] for item in report["source_inventory"]}
    final_sources = {path.relative_to(ROOT).as_posix(): digest(path.read_bytes()) for path in owned_sources()}
    if initial_sources != final_sources:
        errors.append("Owned Lean sources changed during verification; rerun after edits settle")
    if manifest_bytes != (FORMAL / "claims.json").read_bytes():
        errors.append("Claims manifest changed during verification; rerun after edits settle")
    if lock_bytes != (FORMAL / "lake-manifest.json").read_bytes():
        errors.append("Dependency lock changed during verification; rerun after edits settle")
    if toolchain_bytes != (FORMAL / "lean-toolchain").read_bytes():
        errors.append("Lean toolchain file changed during verification; rerun after edits settle")
    if lakefile_bytes != (FORMAL / "lakefile.toml").read_bytes():
        errors.append("Lake project configuration changed during verification; rerun after edits settle")
    report["machine_checks_pass"] = not errors
    admitted_targets = {entry["claim_id"] for entry in report["declarations"]
                        if entry["role"] == "target" and entry["kind"] == "theorem"
                        and entry["axiom_audit_pass"] and entry["correspondence_review_pass"]}
    report["missing_required_targets"] = [claim for claim in required if claim not in admitted_targets]
    report["unreviewed_declarations"] = [entry["name"] for entry in report["declarations"]
                                        if not entry["correspondence_review_pass"]]
    report["main_target_complete"] = (report["machine_checks_pass"] and
                                       not report["missing_required_targets"] and
                                       not report["unreviewed_declarations"])
    return finish()


if __name__ == "__main__":
    AUDIT.mkdir(parents=True, exist_ok=True)
    with (AUDIT / "checker.lock").open("a+b") as checker_lock:
        checker_lock.seek(0, os.SEEK_END)
        if checker_lock.tell() == 0:
            checker_lock.write(b"\0")
            checker_lock.flush()
        checker_lock.seek(0)
        try:
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(checker_lock.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(checker_lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            print("Another formalization check is running. Retry after it finishes; this invocation wrote no report.")
            raise SystemExit(2)
        try:
            raise SystemExit(main())
        finally:
            checker_lock.seek(0)
            if os.name == "nt":
                msvcrt.locking(checker_lock.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(checker_lock.fileno(), fcntl.LOCK_UN)
