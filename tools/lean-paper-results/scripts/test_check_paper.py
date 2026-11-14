#!/usr/bin/env python3
"""Behavioral checks using a real local Lean/Lake installation (no mathlib).

Usage: python test_check_paper.py --lake /absolute/path/to/lake --validation-dir DIR
Fixtures and their logs remain under DIR for inspection. No repository is published.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def matches_expectation(returncode: int, data: dict | None, should_pass: bool,
                        stage: str, diagnostics: dict[str, tuple[str, ...]],
                        logs: dict[str, str]) -> bool:
    """Require the intended stage and diagnostic, not merely any failed run."""
    if (returncode == 0) != should_pass:
        return False
    if data is None:
        stage_matches = not should_pass and stage == "output-protection"
    else:
        if data.get("status") != ("machine-check-passed" if should_pass else "failed"):
            return False
        if data.get("paper_hash_verified") is not False or data.get("semantic_correspondence_verified") is not False:
            return False
        build = data.get("build_returncode")
        audit = data.get("audit_returncode")
        stage_matches = {
            "complete": should_pass and build == 0 and audit == 0,
            "preflight": not should_pass and "runtime" not in data and build is None and audit is None,
            "runtime": not should_pass and data.get("runtime", {}).get("toolchain_runtime_match") is False and build is None and audit is None,
            "build": not should_pass and type(build) is int and build != 0 and audit is None,
            "audit": not should_pass and build == 0 and type(audit) is int and audit != 0,
        }.get(stage, False)
    evidence = {**logs, "error": data.get("error", "") if data else ""}
    return stage_matches and all(
        fragment in evidence.get(source, "")
        for source, fragments in diagnostics.items() for fragment in fragments
    )


def protected_snapshot(paths: list[Path]) -> dict:
    """Record bytes and directory entries, including paths that must stay absent."""
    snapshots = {}
    for path in paths:
        if not path.exists():
            snapshots[str(path)] = None
        elif path.is_file():
            snapshots[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
        else:
            snapshots[str(path)] = {
                item.relative_to(path).as_posix(): "directory" if item.is_dir() else hashlib.sha256(item.read_bytes()).hexdigest()
                for item in sorted(path.rglob("*"))
            }
    return snapshots


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--validation-dir", required=True)
    parser.add_argument("--toolchain", default="leanprover/lean4:v4.24.0")
    args = parser.parse_args()
    base = Path(args.validation_dir).resolve()
    base.mkdir(parents=True, exist_ok=True)
    run_dir = Path(tempfile.mkdtemp(prefix="checker-real-", dir=base))
    checker = Path(__file__).with_name("check_paper.py").resolve()
    results = []
    observations = {}

    def fixture(name: str, source: str, declaration: str = "Toy.target") -> Path:
        repo = run_dir / name
        repo.mkdir()
        (repo / "lean-toolchain").write_text(args.toolchain + "\n", encoding="utf-8")
        (repo / "lakefile.toml").write_text('name = "toy"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "Toy"\n', encoding="utf-8")
        (repo / "Toy.lean").write_text(source, encoding="utf-8")
        docs = repo / "docs" / "formalization"
        docs.mkdir(parents=True)
        paper = repo / "paper.txt"
        paper.write_text("A fixture paper; semantic correspondence is intentionally unreviewed.\n", encoding="utf-8")
        manifest = {
            "schema_version": 1,
            "paper": {"title": "Checker fixture", "version": "1", "sha256": hashlib.sha256(paper.read_bytes()).hexdigest()},
            "scope": {"kind": "selected-results", "description": "Fixture theorem only"},
            "targets": [{"claim_id": "T1", "module": "Toy", "declaration": declaration}],
        }
        (docs / "scope.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        setup = subprocess.run([args.lake, "update"], cwd=repo, capture_output=True, text=True, encoding="utf-8", errors="replace", check=False)
        (repo / "setup.log").write_text(setup.stdout + setup.stderr, encoding="utf-8")
        if setup.returncode:
            raise RuntimeError(f"Fixture setup failed: {repo / 'setup.log'}")
        return repo

    def invoke(name: str, repo: Path, should_pass: bool, extra: list[str] | None = None,
               result_expected: bool = True, *, stage: str = "complete",
               diagnostics: dict[str, tuple[str, ...]] | None = None,
               protected_paths: list[Path] | None = None) -> None:
        before = protected_snapshot(protected_paths or [])
        call = subprocess.run([sys.executable, str(checker), "--repo", str(repo), "--lake", args.lake, *(extra or [])], capture_output=True, text=True, encoding="utf-8", errors="replace", check=False)
        log = run_dir / f"{name}.invocation.log"
        log.write_text(call.stdout + call.stderr, encoding="utf-8")
        result_path = repo / ".paper-verification" / "result.json"
        data = None
        receipt_error = None
        if result_expected:
            try:
                receipt = result_path.read_text(encoding="utf-8")
                (run_dir / f"{name}.result.json").write_text(receipt, encoding="utf-8")
                data = json.loads(receipt)
                if not isinstance(data, dict):
                    raise ValueError("result.json must be an object")
            except (OSError, ValueError) as error:
                receipt_error = str(error)
                data = None
        logs = {"invocation": call.stdout + call.stderr}
        for filename in ("build.log", "audit.log", "runtime.log"):
            path = repo / ".paper-verification" / filename
            if result_expected and path.is_file():
                logs[filename] = path.read_text(encoding="utf-8")
                (run_dir / f"{name}.{filename}").write_text(logs[filename], encoding="utf-8")
        protected_unchanged = before == protected_snapshot(protected_paths or [])
        correct = receipt_error is None and protected_unchanged and matches_expectation(call.returncode, data, should_pass, stage, diagnostics or {}, logs)
        observations[name] = (call.returncode, data, logs)
        results.append({"case": name, "expected_machine_pass": should_pass, "expected_stage": stage, "expected_diagnostics": diagnostics or {}, "passed": correct, "exit_code": call.returncode, "build_returncode": data.get("build_returncode") if data else None, "audit_returncode": data.get("audit_returncode") if data else None, "error": data.get("error") if data else receipt_error, "protected_paths_unchanged": protected_unchanged if protected_paths else None, "repo": str(repo), "invocation_log": str(log), "result_snapshot": str(run_dir / f"{name}.result.json") if result_expected else None})
        print(f"{'PASS' if correct else 'FAIL'} {name}: exit {call.returncode}", flush=True)
        if not correct:
            print(call.stdout + call.stderr)

    valid = fixture("valid", "namespace Toy\ntheorem target : True := True.intro\nend Toy\n")
    invoke("valid", valid, True)
    invoke("preflight-failure-invalidates-success", valid, False, ["--manifest", "../outside.json"], stage="preflight", diagnostics={"error": ("Manifest must stay inside repository",)})
    invoke("valid-after-failed-preflight", valid, True)
    # Reuse the very same output directory: a failed run must invalidate prior success.
    (valid / "Toy.lean").write_text("namespace Toy\ntheorem target : False := by\n  exact True.intro\nend Toy\n", encoding="utf-8")
    invoke("failed-rerun-invalidates-success", valid, False, stage="build", diagnostics={"error": ("Lean build failed",), "build.log": ("Type mismatch", "True.intro", "False")})

    wrong_toolchain = fixture("wrong-toolchain", "namespace Toy\ntheorem target : True := True.intro\nend Toy\n")
    (wrong_toolchain / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n", encoding="utf-8")
    invoke("wrong-toolchain", wrong_toolchain, False, stage="runtime", diagnostics={"error": ("Actual Lean version", "does not match lean-toolchain", "v4.35.0")})

    cases = [
        ("indirect-sorry", "namespace Toy\ntheorem helper : True := by sorry\ntheorem target : True := helper\nend Toy\n", "Toy.target", False, ("Target Toy.target depends on disallowed axioms", "sorryAx")),
        ("custom-axiom", "namespace Toy\naxiom magic : True\ntheorem target : True := magic\nend Toy\n", "Toy.target", False, ("Target Toy.target depends on disallowed axioms", "Toy.magic")),
        ("axiom-as-target", "namespace Toy\naxiom target : True\nend Toy\n", "Toy.target", False, ("Target must be a proved theorem, not an axiom or definition: Toy.target",)),
        ("missing-target", "namespace Toy\ntheorem other : True := True.intro\nend Toy\n", "Toy.target", False, ("Target declaration is missing: Toy.target",)),
        ("definition-as-target", "namespace Toy\ndef target : True := True.intro\nend Toy\n", "Toy.target", False, ("Target must be a proved theorem, not an axiom or definition: Toy.target",)),
        ("false-hypothesis-mechanically-passes", "namespace Toy\ntheorem target (hFalse : False) : False := hFalse\nend Toy\n", "Toy.target", True, ()),
        ("unrelated-sorry-outside-target-closure", "namespace Toy\ntheorem draft : False := by sorry\ntheorem target : True := True.intro\nend Toy\n", "Toy.target", True, ()),
    ]
    for name, source, declaration, expected, diagnostic in cases:
        repo = fixture(name, source, declaration)
        invoke(name, repo, expected, stage="complete" if expected else "audit", diagnostics={} if expected else {"error": ("Lean theorem or axiom audit failed",), "audit.log": diagnostic})

    native = fixture("native-decide", "import Lean\nnamespace Toy\ntheorem target : (List.range 10).length = 10 := by native_decide\nend Toy\n")
    invoke("native-decide", native, False, stage="audit", diagnostics={"error": ("Lean theorem or axiom audit failed",), "audit.log": ("Target Toy.target depends on disallowed axioms", "Lean.ofReduceBool", "Lean.trustCompiler")})
    _, native_data, native_logs = observations["native-decide"]
    native_result = native_data or {}
    native_audit = native_logs.get("audit.log", "")
    native_correct_stage = native_result.get("build_returncode") == 0 and type(native_result.get("audit_returncode")) is int and native_result["audit_returncode"] != 0 and "depends on disallowed axioms" in native_audit
    results[-1]["passed"] = results[-1]["passed"] and native_correct_stage
    results[-1]["build_succeeded_and_axiom_audit_rejected"] = native_correct_stage
    if not native_correct_stage:
        print("FAIL native-decide did not reach the expected axiom-audit failure", flush=True)

    for name, edit, diagnostic in (
        ("duplicate-claim", lambda m: m["targets"].append(dict(m["targets"][0], declaration="Toy.other")), "Duplicate claim_id or declaration"),
        ("unsafe-name", lambda m: m["targets"][0].update(declaration="Toy.target\naxiom bad : False"), "targets[0].declaration: only ASCII dotted Lean identifiers supported"),
        ("zero-paper-hash", lambda m: m["paper"].update(sha256="0" * 64), "paper.sha256 is the unconfigured all-zero template value"),
    ):
        repo = fixture(name, "namespace Toy\ntheorem target : True := True.intro\nend Toy\n")
        manifest_path = repo / "docs" / "formalization" / "scope.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        edit(manifest)
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        invoke(name, repo, False, stage="preflight", diagnostics={"error": (diagnostic,)})

    wrong_module = fixture("wrong-defining-module", "namespace Toy\ntheorem target : True := True.intro\nend Toy\n")
    (wrong_module / "Wrapper.lean").write_text("import Toy\n", encoding="utf-8")
    manifest_path = wrong_module / "docs" / "formalization" / "scope.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["targets"][0]["module"] = "Wrapper"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    # Wrapper must be a Lake target so build reaches the provenance check.
    with (wrong_module / "lakefile.toml").open("a", encoding="utf-8") as stream:
        stream.write('\n[[lean_lib]]\nname = "Wrapper"\n')
    invoke("wrong-defining-module", wrong_module, False, stage="audit", diagnostics={"error": ("Lean theorem or axiom audit failed",), "audit.log": ("Target Toy.target is defined in Toy, expected Wrapper",)})

    foreign = fixture("foreign-audit", "namespace Toy\ntheorem target : True := True.intro\nend Toy\n")
    out = foreign / ".paper-verification"
    out.mkdir()
    protected = out / "CheckTargets.lean"
    protected.write_text("-- Existing user audit\n", encoding="utf-8")
    invoke("foreign-audit-not-overwritten", foreign, False, result_expected=False, stage="output-protection", diagnostics={"invocation": ("ERROR: Refusing to overwrite a nonempty output directory without this script's owner marker",)}, protected_paths=[out])

    path_test = fixture("path-boundaries", "namespace Toy\ntheorem target : True := True.intro\nend Toy\n")
    invoke("outside-manifest-rejected", path_test, False, ["--manifest", "../outside.json"], stage="preflight", diagnostics={"error": ("Manifest must stay inside repository",)})
    invoke("outside-output-rejected", path_test, False, ["--output", "../outside-output"], result_expected=False, stage="output-protection", diagnostics={"invocation": ("ERROR: Output must stay inside repository",)}, protected_paths=[path_test / ".paper-verification", run_dir / "outside-output"])
    # A real runtime-mismatch receipt used to satisfy the sorry test's generic
    # nonzero/failed check. It must not replace an axiom-audit rejection now.
    wrong_code, wrong_data, wrong_logs = observations["wrong-toolchain"]
    legacy_would_accept = wrong_code != 0 and (wrong_data or {}).get("status") == "failed"
    wrong_stage_rejected = not matches_expectation(wrong_code, wrong_data, False, "audit", {"error": ("Lean theorem or axiom audit failed",), "audit.log": ("Target Toy.target depends on disallowed axioms", "sorryAx")}, wrong_logs)
    regression = {"case": "runtime-mismatch-cannot-substitute-for-sorry-audit", "passed": legacy_would_accept and wrong_stage_rejected, "legacy_generic_check_would_accept": legacy_would_accept, "stage_and_diagnostic_check_rejected": wrong_stage_rejected, "substitute_receipt": str(run_dir / "wrong-toolchain.result.json")}
    print(f"{'PASS' if regression['passed'] else 'FAIL'} {regression['case']}", flush=True)
    summary = {
        "tested_at": datetime.now(timezone.utc).isoformat(),
        "lake": args.lake,
        "toolchain": args.toolchain,
        "checker_sha256": hashlib.sha256(checker.read_bytes()).hexdigest(),
        "test_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "all_passed": all(item["passed"] for item in results) and regression["passed"],
        "cases": results,
        "expectation_regressions": [regression],
    }
    summary_path = run_dir / "summary.json"
    summary_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Summary: {summary_path}", flush=True)
    return 0 if summary["all_passed"] else 1


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    raise SystemExit(main())
