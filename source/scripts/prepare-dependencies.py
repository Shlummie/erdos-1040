#!/usr/bin/env python3
"""Materialize the publication's locked dependencies before its original audit.

Python 3.9+, Git, and an already installed pinned Lean toolchain are required.
Place this file at scripts/prepare-dependencies.py in the extracted artifact.
No dependency version resolution or toolchain installation is performed.
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
from urllib.parse import urlparse


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.1"
EXPECTED_PACKAGES = {
    "mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
    "aesop", "Qq", "batteries", "Cli",
}


class PreparationError(RuntimeError):
    pass


def run(command: list[str], cwd: Path, *, capture: bool = False,
        env: dict[str, str] | None = None) -> str:
    result = subprocess.run(
        command, cwd=cwd, env=env, check=False, text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
        encoding="utf-8", errors="replace",
    )
    if result.returncode:
        detail = (result.stderr or result.stdout or "").strip() if capture else ""
        raise PreparationError(
            f"Command failed ({result.returncode}): {' '.join(command)}"
            + (f"\n{detail}" if detail else "")
        )
    return result.stdout.strip() if capture else ""


def git(arguments: list[str], cwd: Path, *, capture: bool = False) -> str:
    # Keep checkout bytes independent of the reader's global newline setting.
    return run(["git", "-c", "core.autocrlf=false", *arguments], cwd,
               capture=capture)


def reject_redirected_path(path: Path) -> None:
    # Refuse symlinks and Windows directory junctions, including absent children
    # whose existing parent redirects outside the extracted artifact.
    if path.resolve() != path.absolute():
        raise PreparationError(f"Dependency path redirects through a link: {path}")


def verify_existing(path: Path, rev: str) -> None:
    reject_redirected_path(path)
    if not path.is_dir() or not (path / ".git").is_dir():
        raise PreparationError(f"Existing dependency is not a standalone Git checkout: {path}")
    top = Path(git(["rev-parse", "--show-toplevel"], path, capture=True)).resolve()
    if top != path.resolve():
        raise PreparationError(f"Dependency Git root does not match its directory: {path}")
    head = git(["rev-parse", "HEAD"], path, capture=True)
    if head != rev:
        raise PreparationError(f"Existing dependency has HEAD {head}; expected {rev}: {path}")
    status = git(["status", "--porcelain", "--untracked-files=no"], path, capture=True)
    if status:
        raise PreparationError(f"Existing dependency has tracked changes; left untouched: {path}")


def installed_toolchain() -> tuple[Path, dict[str, str]]:
    toolchain = (FORMAL / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        raise PreparationError(f"Unexpected Lean toolchain: {toolchain}")
    # Match the original checker's direct-toolchain preference. Never invoke an
    # elan shim here: that could install a toolchain as an implicit side effect.
    toolchain_dir = EXPECTED_TOOLCHAIN.replace("/", "--").replace(":", "---")
    direct_bin = Path.home() / ".elan" / "toolchains" / toolchain_dir / "bin"
    suffix = ".exe" if os.name == "nt" else ""
    lake = direct_bin / ("lake" + suffix)
    lean = direct_bin / ("lean" + suffix)
    if not lake.is_file() or not lean.is_file():
        raise PreparationError(
            f"Pinned Lean must already be installed under {direct_bin}. "
            f"Install {EXPECTED_TOOLCHAIN} separately before using --cache."
        )
    env = os.environ.copy()
    env["PATH"] = str(direct_bin) + os.pathsep + env.get("PATH", "")
    version = run([str(lean), "--version"], FORMAL, capture=True, env=env)
    if not re.search(r"\bversion 4\.33\.1(?:\s|,|\))", version):
        raise PreparationError(f"Installed Lean reports an unexpected version: {version}")
    return lake, env


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", action="store_true",
                        help="also run the pinned mathlib cache command (network access)")
    args = parser.parse_args()
    if shutil.which("git") is None:
        raise PreparationError("Git must be installed and available on PATH.")

    lock_path = FORMAL / "lake-manifest.json"
    lock_bytes = lock_path.read_bytes()
    lock_sha = hashlib.sha256(lock_bytes).hexdigest()
    lock = json.loads(lock_bytes.decode("utf-8-sig"))
    packages = lock.get("packages")
    if lock.get("packagesDir") != ".lake/packages":
        raise PreparationError("The manifest must use packagesDir .lake/packages.")
    if not isinstance(packages, list) or len(packages) != 9:
        raise PreparationError("The manifest must contain exactly nine dependencies.")
    if any(not isinstance(package, dict) for package in packages):
        raise PreparationError("Invalid dependency entry in manifest.")
    names = [package.get("name") for package in packages]
    if any(not isinstance(name, str) for name in names) or set(names) != EXPECTED_PACKAGES:
        raise PreparationError("The manifest dependency names differ from this publication.")

    package_root = FORMAL / ".lake" / "packages"
    reject_redirected_path(package_root)
    missing = []
    for package in packages:
        name, rev, url = package["name"], package.get("rev"), package.get("url")
        if package.get("type") != "git" or package.get("subDir") is not None:
            raise PreparationError(f"{name} must be a whole Git checkout.")
        if not isinstance(rev, str) or not re.fullmatch(r"[0-9a-f]{40}", rev):
            raise PreparationError(f"{name} must have an exact 40-character revision.")
        parsed = urlparse(url) if isinstance(url, str) else None
        if (parsed is None or parsed.scheme != "https" or not parsed.netloc
                or parsed.username is not None or parsed.password is not None):
            raise PreparationError(f"{name} must have an HTTPS repository URL without credentials.")
        path = package_root / name
        reject_redirected_path(path)
        if path.exists():
            verify_existing(path, rev)
        else:
            missing.append((path, rev, url))

    # Complete read-only preflight before creating any dependency directories.
    cache_toolchain = installed_toolchain() if args.cache else None

    def verify_lock() -> None:
        if lock_path.read_bytes() != lock_bytes:
            raise PreparationError("lake-manifest.json changed during preparation; audit stopped.")

    try:
        verify_lock()
        for path, rev, url in missing:
            path.mkdir(parents=True, exist_ok=False)
            print(f"Fetching {path.name} at {rev}", flush=True)
            # Failed new checkouts remain in place for inspection. A subsequent
            # run refuses partial/wrong state instead of resetting or deleting it.
            git(["init", "."], path)
            git(["remote", "add", "origin", url], path)
            git(["fetch", "--depth", "1", "origin", rev], path)
            git(["checkout", "--detach", "FETCH_HEAD"], path)
            verify_existing(path, rev)
            verify_lock()
        if cache_toolchain is not None:
            lake, env = cache_toolchain
            print("Retrieving precompiled dependency cache with the pinned toolchain.", flush=True)
            run([str(lake), "exe", "cache", "get"], FORMAL, env=env)
        for package in packages:
            verify_existing(package_root / package["name"], package["rev"])
    finally:
        verify_lock()

    print(f"Ready: all nine dependency checkouts match the manifest; lock SHA-256 {lock_sha}.")
    print("Next: python scripts/check-formalization.py")
    if args.cache:
        print("This preparation uses cached dependency artifacts; it is not a fresh dependency rebuild.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (PreparationError, OSError, ValueError, TypeError, KeyError) as exc:
        print(f"Preparation failed: {exc}", file=sys.stderr)
        sys.exit(1)
