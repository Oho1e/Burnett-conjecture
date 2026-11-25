#!/usr/bin/env python3
"""Check source identity and project setup; audit real paper targets when present.

Python 3.10+, standard library only. Does not install dependencies or publish.
An empty target list can only yield project-setup-passed, never paper verification.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from check_paper import path_alias


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"Expected a JSON object: {path}")
    return data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=".")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument(
        "--build-timeout", type=int,
        help="time limit in seconds for lake build Burnett (defaults to --timeout)",
    )
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.build_timeout is not None and args.build_timeout <= 0:
        parser.error("--build-timeout must be positive")
    build_timeout = args.timeout if args.build_timeout is None else args.build_timeout
    repo = Path(args.repo).resolve()
    output = repo / ".project-verification"
    if path_alias(output):
        print("ERROR: Refusing a symlinked or reparse project evidence directory", file=sys.stderr)
        return 1
    output.mkdir(parents=True, exist_ok=True)
    result = {
        "schema_version": 1,
        "status": "failed",
        "started_at": datetime.now(timezone.utc).isoformat(),
        "paper_formalization_verified": False,
        "semantic_correspondence_verified": False,
        "paper_hash_verified": False,
        "build_timeout_seconds": build_timeout,
        "error": "Run has not completed",
    }
    receipt = output / "result.json"
    receipt.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    logs = []

    def command(argv: list[str], filename: str, *, timeout: int = args.timeout) -> subprocess.CompletedProcess:
        print("Running " + json.dumps(argv, ensure_ascii=False), flush=True)
        process = subprocess.run(argv, cwd=repo, capture_output=True, text=True,
                                 encoding="utf-8", errors="replace", timeout=timeout,
                                 shell=False, check=False)
        (output / filename).write_text(
            "Command: " + json.dumps(argv, ensure_ascii=False) + "\n"
            + process.stdout + process.stderr + f"\nExit code: {process.returncode}\n",
            encoding="utf-8", newline="\n",
        )
        logs.append(filename)
        if process.returncode != 0:
            raise ValueError(f"Command failed with exit {process.returncode}; see {output / filename}")
        return process

    try:
        scope_path = repo / "docs" / "formalization" / "scope.json"
        scope = load_json(scope_path)
        source_path = repo / "paper" / "source.json"
        source = load_json(source_path)
        paper_path = repo / "paper" / "burnett.tex"
        actual_hash = digest(paper_path)
        if actual_hash != source["sha256"] or actual_hash != scope["paper"]["sha256"]:
            raise ValueError("Paper SHA256 does not match the locked source record and scope")
        if paper_path.stat().st_size != source["bytes"]:
            raise ValueError("Paper byte count does not match the locked source record")
        result["paper_hash_verified"] = True
        standard_path = repo / "docs" / "formalization" / "standard.zh-CN.md"
        if scope["standard"]["id"] != "paper-results" or scope["standard"]["version"] != "1.2":
            raise ValueError("Project scope must identify its approved paper-results 1.2 standard")
        if digest(standard_path) != scope["standard"]["document_sha256"]:
            raise ValueError("Standard document SHA256 does not match scope")
        targets = scope.get("targets")
        if not isinstance(targets, list):
            raise ValueError("scope.targets must be an array")
        if not targets and scope.get("status") != "development":
            raise ValueError("An empty paper target list must retain development status")
        for path in (repo / "Burnett.lean", repo / "Burnett" / "Overview.lean", repo / "lakefile.toml"):
            if not path.is_file():
                raise ValueError(f"Required project configuration or entry missing: {path}")
        toolchain_path = repo / "lean-toolchain"
        pin = toolchain_path.read_text(encoding="utf-8").strip()
        expected = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?)", pin)
        if expected is None:
            raise ValueError("Expected a fixed release Lean toolchain")
        lake_version = command([args.lake, "--version"], "lake-version.log")
        lean_version = command([args.lake, "env", "lean", "--version"], "lean-version.log")
        observed = re.search(r"Lean \(version ([^,\s)]+)", lean_version.stdout)
        if observed is None or observed.group(1) != expected.group(1):
            raise ValueError("Actual Lean version does not match lean-toolchain")
        result["runtime"] = {"lake": lake_version.stdout.strip(), "lean": lean_version.stdout.strip(), "toolchain": pin}
        result["paper_target_count"] = len(targets)
        result["scope_status"] = scope.get("status")
        command([args.lake, "build", "Burnett"], "build.log", timeout=build_timeout)
        if targets:
            # The original checker still rejects empty targets. Do not alter it.
            checker = Path(__file__).with_name("check_paper.py")
            command([sys.executable, str(checker), "--repo", str(repo), "--lake", args.lake,
                     "--generated-root", ".project-verification", "--entry-module", "Burnett",
                     "--timeout", str(args.timeout)], "paper-target-check.log")
            target_result = load_json(repo / ".paper-verification" / "result.json")
            if target_result.get("status") != "machine-check-passed":
                raise ValueError("Target checker did not produce machine-check-passed")
            result["target_check_receipt_sha256"] = digest(repo / ".paper-verification" / "result.json")
            result["target_check_input_fingerprint"] = target_result["inputs"]["input_fingerprint"]
            result["status"] = "machine-check-passed"
            result["check_scope"] = "Declared paper targets and their transitive axioms; semantic and complete-coverage review remain separate"
        else:
            result["status"] = "project-setup-passed"
            result["check_scope"] = "Source hash, configuration, pinned runtime and library startup build only; no paper theorem checked"
        dependency_path = repo / "lake-manifest.json"
        manifest = load_json(dependency_path)
        result["dependency_package_count"] = len(manifest.get("packages", []))
        result["input_sha256"] = {
            str(path.relative_to(repo)).replace("\\", "/"): digest(path)
            for path in (paper_path, source_path, scope_path, standard_path, toolchain_path,
                         repo / "lakefile.toml", dependency_path, repo / "Burnett.lean",
                         repo / "Burnett" / "Overview.lean", Path(__file__).resolve(),
                         Path(__file__).with_name("check_paper.py").resolve())
        }
        result.pop("error", None)
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        result["status"] = "failed"
        result["error"] = str(error)
        print(f"ERROR: {error}", file=sys.stderr)
    finally:
        result["finished_at"] = datetime.now(timezone.utc).isoformat()
        result["log_sha256"] = {name: digest(output / name) for name in logs}
        receipt.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(f"{result['status']}: {receipt}", flush=True)
        print("paper_formalization_verified: false", flush=True)
    return 0 if result["status"] in ("project-setup-passed", "machine-check-passed") else 1


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    raise SystemExit(main())
