"""Cleanly rebuild the project's Lean source and audit reported axioms.

Dependencies are pinned by lake-manifest.json. Existing dependency build
artifacts may be retained; only this package's .lake/build is removed.
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", help="Path to the pinned Lean 4.19.0 lake executable")
    parser.add_argument("--git", help="Path to Git for read-only revision verification")
    parser.add_argument("--log-dir", help="Output directory for logs; defaults to this project's logs/")
    parser.add_argument("--no-clean", action="store_true")
    args = parser.parse_args()
    project = Path(__file__).resolve().parent
    portable = project.parent / ".tools/lean/lean-4.19.0-windows/bin/lake.exe"
    lake = args.lake or (str(portable) if portable.is_file() else shutil.which("lake"))
    if not lake:
        raise RuntimeError("Install Lean 4.19.0, or pass --lake /path/to/lake.")
    lake = str(Path(lake).resolve())
    env = dict(os.environ)
    env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
    logs = Path(args.log_dir).resolve() if args.log_dir else project / "logs"
    logs.mkdir(parents=True, exist_ok=True)

    def run(*arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [lake, *arguments], cwd=project, env=env, text=True,
            encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False,
        )

    version = run("env", "lean", "--version")
    if version.returncode or "version 4.19.0," not in version.stdout:
        raise RuntimeError("Wrong compiler or unavailable dependencies: " + version.stdout)
    lake_version = run("--version")
    manifest = project / "lake-manifest.json"
    source = project / "OQ14.lean"
    source_text = source.read_text(encoding="utf-8")
    if re.search(r"(?m)^\s*(axiom|constant)\s|\b(sorry|admit)\b", source_text):
        raise RuntimeError("Forbidden unproved declaration found in formal source.")
    lock = json.loads(manifest.read_text(encoding="utf-8"))
    mathlib = next(p for p in lock["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != "c44e0c8ee63ca166450922a373c7409c5d26b00b":
        raise RuntimeError("Unexpected mathlib revision in lockfile.")

    git = args.git or shutil.which("git")
    if not git:
        raise RuntimeError("Git is required to verify installed dependency revisions; use --git.")

    def git_read(directory: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [git, "-C", str(directory), *arguments], env=env, text=True,
            encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False,
        )

    installed_dependencies = []
    for package in lock["packages"]:
        if package["type"] != "git":
            raise RuntimeError(f"Unverified dependency type: {package['name']}")
        directory = project / lock["packagesDir"] / package["name"]
        head = git_read(directory, "rev-parse", "HEAD")
        if head.returncode or head.stdout.strip() != package["rev"]:
            raise RuntimeError(f"Installed dependency revision mismatch: {package['name']}: {head.stdout}")
        clean = git_read(directory, "diff", "--quiet", "HEAD", "--")
        if clean.returncode:
            raise RuntimeError(f"Tracked dependency files differ from the pin: {package['name']}")
        installed_dependencies.append({"name": package["name"], "revision": head.stdout.strip(),
                                       "tracked_files_clean": True})

    source_commit = git_read(project, "rev-parse", "HEAD")
    source_status = git_read(project, "status", "--porcelain", "--untracked-files=normal")
    repository_state = {
        "commit": source_commit.stdout.strip() if source_commit.returncode == 0 else None,
        "dirty": bool(source_status.stdout.strip()) if source_status.returncode == 0 else None,
        "captured": "before compilation",
    }
    initial_source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    initial_manifest_hash = hashlib.sha256(manifest.read_bytes()).hexdigest()

    if not args.no_clean:
        build = (project / ".lake/build").resolve()
        if not build.is_relative_to(project) or build == project:
            raise RuntimeError("Refusing cleanup outside the Lean project.")
        if build.exists():
            shutil.rmtree(build)

    result = run("build", "OQ14")
    text = result.stdout + f"\nCompiler exit code: {result.returncode}\n"
    (logs / "clean-build.txt").write_text(text, encoding="utf-8")
    print(result.stdout, end="")
    if result.returncode:
        return result.returncode
    if hashlib.sha256(source.read_bytes()).hexdigest() != initial_source_hash or \
            hashlib.sha256(manifest.read_bytes()).hexdigest() != initial_manifest_hash:
        raise RuntimeError("Formal source or dependency manifest changed during compilation.")

    expected = set(re.findall(r"#print axioms (OQ14\.\w+)", source_text))
    reports = dict(re.findall(r"'(OQ14\.\w+)' depends on axioms: \[([^\]]*)\]", text))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if set(reports) != expected:
        raise RuntimeError("Missing or unexpected theorem axiom reports.")
    for theorem, report in reports.items():
        actual = {s.strip() for s in report.split(",") if s.strip()}
        if not actual <= allowed:
            raise RuntimeError(f"Unapproved axioms for {theorem}: {sorted(actual - allowed)}")

    provenance = {
        "compiler": version.stdout.strip(),
        "lake": lake_version.stdout.strip(),
        "mathlib_revision": mathlib["rev"],
        "source_sha256": initial_source_hash,
        "manifest_sha256": initial_manifest_hash,
        "source_repository": repository_state,
        "installed_dependencies": installed_dependencies,
        "root_build_cleaned": not args.no_clean,
        "pinned_dependency_cache_retained": True,
        "compiler_exit_code": result.returncode,
        "checked_theorems": sorted(expected),
        "allowed_foundational_axioms": sorted(allowed),
    }
    (logs / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")
    with (logs / "clean-build.txt").open("a", encoding="utf-8") as handle:
        handle.write(f"Axiom audit passed for {len(expected)} theorems.\n")
    print(f"Lean build and axiom audit passed for {len(expected)} theorems.")
    return 0


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    raise SystemExit(main())
