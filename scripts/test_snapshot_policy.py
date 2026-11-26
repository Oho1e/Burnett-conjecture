#!/usr/bin/env python3
"""Snapshot-boundary regressions; stdlib fast tests, optional real Lean fixtures.

Run ``python scripts/test_snapshot_policy.py`` for the fast suite. Add
``--lake /absolute/path/to/lake --validation-dir /path/to/evidence`` for actual
Core-only Lean/Lake builds and theorem audits. Fixtures, logs and JSON receipts
are retained, including failures; no project Lake cache or source is changed.
The timing-instrumented tests wrap real functions and never replace a build,
audit or boundary-check result with a synthetic success.
"""

from __future__ import annotations

import argparse
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timezone
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import check_paper as checker


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_VALIDATION = ROOT / ".project-verification/maintenance-2026-11-16/snapshot-tests"
VALIDATION: Path | None = None
LAKE: str | None = None
FIXTURES: list[dict[str, str]] = []
LEAN_RUNS: list[dict[str, object]] = []
GENERATED = ".project-verification"
HELPER_V1 = """namespace Helper
def bump (n : Nat) : Nat := n + 1
theorem bump_eq (n : Nat) : bump n = n + 1 := rfl
end Helper
"""
HELPER_V2 = """namespace Helper
def bump (n : Nat) : Nat := 1 + n
theorem bump_eq (n : Nat) : bump n = n + 1 := Nat.add_comm 1 n
end Helper
"""
TOY_HELPER = """import Helper
namespace Toy
theorem target (n : Nat) : Helper.bump n = n + 1 := Helper.bump_eq n
end Toy
"""


def write(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8", newline="\n")


def write_json(path: Path, value: object) -> None:
    write(path, json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def evidence_directory() -> Path:
    global VALIDATION
    if VALIDATION is None:
        DEFAULT_VALIDATION.mkdir(parents=True, exist_ok=True)
        VALIDATION = Path(tempfile.mkdtemp(prefix="unittest-", dir=DEFAULT_VALIDATION)).resolve()
    return VALIDATION


def new_fixture(test_id: str) -> Path:
    base = evidence_directory()
    # Lean's Windows object writer can still encounter MAX_PATH even when
    # Python can create the longer path. Keep room for nested module outputs.
    fixture = Path(tempfile.mkdtemp(prefix=test_id.rsplit(".", 1)[-1][:34] + "-", dir=base)).resolve()
    FIXTURES.append({"test": test_id, "path": str(fixture)})
    return fixture


def minimal_repository(repo: Path) -> None:
    write(repo / "lean-toolchain", "leanprover/lean4:v4.24.0\n")
    write(repo / "lake-manifest.json", '{"version": "1.1.0", "packages": []}\n')
    write(repo / "lakefile.toml", 'name = "snapshot_fixture"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Toy"\n')
    write(repo / "Toy.lean", "namespace Toy\ntheorem target (n : Nat) : n + 0 = n := Nat.add_zero n\nend Toy\n")
    write_json(repo / "scope.json", {
        "schema_version": 1,
        "paper": {"title": "Snapshot regression fixture", "version": "1", "sha256": "1" * 64},
        "scope": {"kind": "selected-results", "description": "Fixture only; no paper theorem claim"},
        "targets": [{"claim_id": "fixture:T1", "module": "Toy", "declaration": "Toy.target"}],
    })
    (repo / GENERATED).mkdir(exist_ok=True)


def git(repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", "-C", str(repo), *args], capture_output=True,
                          text=True, encoding="utf-8", errors="replace", check=True)


def directory_alias(alias: Path, destination: Path) -> bool:
    """Use a real symlink, or Windows junction where symlink privilege is absent."""
    try:
        alias.symlink_to(destination, target_is_directory=True)
        return True
    except OSError:
        if os.name != "nt":
            return False
    result = subprocess.run(["cmd", "/d", "/c", "mklink", "/J", str(alias), str(destination)],
                            capture_output=True, text=True, errors="replace", check=False)
    return result.returncode == 0


class SnapshotPolicyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = new_fixture(self.id())
        minimal_repository(self.repo)
        self.output = self.repo / GENERATED / "checker"
        self.protected = [self.repo / name for name in (
            "scope.json", "lean-toolchain", "lake-manifest.json", "lakefile.toml", "Toy.lean")]
        self.generated = checker.generated_directories(self.repo, [GENERATED], self.protected)

    def snapshot(self, generated=None, entries=()):
        return checker.input_snapshot(self.repo, self.output, self.repo / "scope.json",
                                      self.generated if generated is None else generated, entries)

    def boundary(self, modules, sources=None, raw=None):
        log = self.repo / GENERATED / "synthetic-boundary.log"
        if raw is None:
            raw = checker.DEPENDENCY_MARKER + json.dumps(modules) + "\n"
        write(log, raw)
        return checker.verify_loaded_boundaries(
            log, self.repo, self.output, self.generated,
            self.snapshot()["lean_sources"] if sources is None else sources)

    def module(self, name="Toy", source=None, olean=None):
        return {"module": name, "source": str(source or self.repo / "Toy.lean"),
                "olean": str(olean or self.repo / ".lake/build/lib/lean/Toy.olean")}

    def test_windows_lake_batches_preserve_all_build_targets(self):
        prefix = [r"C:\Lean Tools\lake.exe", "build"]
        targets = [f"Burnett.Analysis.Deeply.Nested.Project.Module{index:04d}" for index in range(700)]
        argv = [*prefix, *targets]
        self.assertGreater(len(subprocess.list2cmdline(argv).encode("utf-16-le")) // 2, 32_767)
        batches = checker.windows_build_batches(argv)
        self.assertGreater(len(batches), 1)
        self.assertEqual([module for batch in batches for module in batch[2:]], targets)
        for batch in batches:
            self.assertEqual(batch[:2], prefix)
            self.assertLess(len(subprocess.list2cmdline(batch).encode("utf-16-le")) // 2, 28_000)
        short = [*prefix, "Burnett"]
        self.assertEqual(checker.windows_build_batches(short), [short])

    def test_generated_probe_add_modify_delete_preserves_project_snapshot(self):
        before = self.snapshot()
        probe = self.repo / GENERATED / "agent-a/Probe.lean"
        log = probe.with_suffix(".log")
        auxiliary = []
        for text in ("def probe : Nat := 1\n", "def probe : Nat := 2\n"):
            write(probe, text)
            write(log, text)
            auxiliary.append({"source": checker.digest(probe), "log": checker.digest(log)})
            write(self.output / "CheckTargets.lean", text)
            write(self.repo / GENERATED / "agent-b/CheckTargets.lean", text)
            self.assertEqual(self.snapshot(), before)
        self.assertNotEqual(auxiliary[0], auxiliary[1])
        probe.unlink()
        self.assertEqual(self.snapshot(), before)
        write_json(self.repo / GENERATED / "auxiliary-hashes.json", auxiliary)

    def test_generated_exclusion_is_opt_in(self):
        write(self.repo / GENERATED / "Probe.lean", "def probe : Nat := 1\n")
        self.assertIn(GENERATED + "/Probe.lean", self.snapshot(generated=())["lean_sources"])
        self.assertNotIn(GENERATED + "/Probe.lean", self.snapshot()["lean_sources"])

    def test_only_exact_root_is_excluded_not_same_name_subdirectory_or_prefix(self):
        write(self.repo / "Ordinary" / GENERATED / "Helper.lean", HELPER_V1)
        write(self.repo / (GENERATED + "-other") / "Helper.lean", HELPER_V1)
        write(self.repo / GENERATED / "Hidden.lean", HELPER_V1)
        sources = self.snapshot()["lean_sources"]
        self.assertIn("Ordinary/" + GENERATED + "/Helper.lean", sources)
        self.assertIn(GENERATED + "-other/Helper.lean", sources)
        self.assertNotIn(GENERATED + "/Hidden.lean", sources)

    def test_other_output_is_not_implicitly_excluded(self):
        write(self.repo / "agents/other/CheckTargets.lean", HELPER_V1)
        self.assertIn("agents/other/CheckTargets.lean", self.snapshot()["lean_sources"])

    def test_untracked_ignored_shared_sources_add_modify_delete_affect_hash(self):
        if shutil.which("git") is None:
            self.skipTest("Git unavailable: cannot establish actual ignored/tracked identities")
        git(self.repo, "init", "--quiet")
        write(self.repo / ".gitignore", "Ignored/\n")
        kinds = {"FreshTarget.lean": "untracked", "Ignored/Helper.lean": "ignored",
                 "Shared/Definitions.lean": "tracked"}
        for relative, kind in kinds.items():
            with self.subTest(relative=relative, kind=kind):
                before = self.snapshot()
                path = self.repo / relative
                write(path, HELPER_V1)
                if kind == "tracked":
                    git(self.repo, "add", "--", relative)
                    self.assertEqual(git(self.repo, "ls-files", "--", relative).stdout.strip(), relative)
                elif kind == "ignored":
                    self.assertEqual(git(self.repo, "check-ignore", "--", relative).stdout.strip(), relative)
                else:
                    self.assertEqual(git(self.repo, "ls-files", "--", relative).stdout.strip(), "")
                added = self.snapshot()
                self.assertEqual(added["lean_sources"][relative], checker.digest(path))
                self.assertNotEqual(before["input_fingerprint"], added["input_fingerprint"])
                write(path, HELPER_V2)  # Both complete, valid Lean alternatives are compiled below.
                changed = self.snapshot()
                self.assertEqual(changed["lean_sources"][relative], checker.digest(path))
                self.assertNotEqual(added["lean_sources"][relative], changed["lean_sources"][relative])
                self.assertNotEqual(added["input_fingerprint"], changed["input_fingerprint"])
                path.unlink()
                removed = self.snapshot()
                self.assertNotIn(relative, removed["lean_sources"])
                self.assertEqual(before, removed)

    def test_git_presence_does_not_change_source_collection(self):
        if shutil.which("git") is None:
            self.skipTest("Git unavailable")
        write(self.repo / "Helper.lean", HELPER_V1)
        before = self.snapshot()
        git(self.repo, "init", "--quiet")
        write(self.repo / ".gitignore", "Helper.lean\n")
        self.assertEqual(git(self.repo, "check-ignore", "Helper.lean").stdout.strip(), "Helper.lean")
        self.assertEqual(before, self.snapshot())

    def test_policy_and_entry_changes_change_input_fingerprint(self):
        baseline = self.snapshot()
        for altered in (self.snapshot(generated=()), self.snapshot(entries=("Toy",))):
            self.assertEqual(baseline["lean_sources"], altered["lean_sources"])
            self.assertNotEqual(baseline["snapshot_policy"], altered["snapshot_policy"])
            self.assertNotEqual(baseline["input_fingerprint"], altered["input_fingerprint"])
        with patch.object(checker, "EXCLUDED_DIRECTORIES", checker.EXCLUDED_DIRECTORIES | {".test-policy"}):
            changed = self.snapshot()
        self.assertEqual(baseline["lean_sources"], changed["lean_sources"])
        self.assertNotEqual(baseline["input_fingerprint"], changed["input_fingerprint"])

    def test_configuration_manifest_and_checker_bytes_are_bound(self):
        for relative in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "scope.json"):
            with self.subTest(input=relative):
                path = self.repo / relative
                original = path.read_bytes()
                before = self.snapshot()
                path.write_bytes(original + b"\n")
                self.assertNotEqual(before["input_fingerprint"], self.snapshot()["input_fingerprint"])
                path.write_bytes(original)
        checker_copy = self.repo / GENERATED / "checker-copy.py"
        write(checker_copy, "# checker v1\n")
        with patch.object(checker, "__file__", str(checker_copy)):
            before = self.snapshot()
            write(checker_copy, "# checker v2\n")
            self.assertNotEqual(before["input_fingerprint"], self.snapshot()["input_fingerprint"])

    def test_generated_root_must_be_dedicated_root_level_directory(self):
        for value in (".", "..", "Ordinary/" + GENERATED, ".git", ".lake", "Toy.lean", "../outside"):
            with self.subTest(value=value), self.assertRaises(checker.CheckError):
                checker.generated_directories(self.repo, [value], self.protected)
        both = checker.generated_directories(self.repo, [GENERATED, GENERATED], self.protected)
        self.assertEqual(both, self.generated)

    def test_generated_root_cannot_contain_config_target_or_entry_source(self):
        for relative in ("config/scope.json", "config/lean-toolchain", "config/lake-manifest.json",
                         "config/lakefile.toml", "config/Toy.lean", "config/Library.lean"):
            with self.subTest(protected=relative), self.assertRaisesRegex(checker.CheckError, "overlaps"):
                checker.generated_directories(self.repo, ["config"], [self.repo / relative])

    def test_real_alias_cannot_be_a_generated_root(self):
        alias = self.repo / "generated-alias"
        if not directory_alias(alias, self.repo / GENERATED):
            self.skipTest("Filesystem does not permit a directory symlink or junction")
        self.assertTrue(checker.path_alias(alias))
        with self.assertRaisesRegex(checker.CheckError, "alias"):
            checker.generated_directories(self.repo, [alias.name], self.protected)

    def test_simulated_reparse_metadata_rejects_generated_root(self):
        # Real junction creation is forbidden in some sandboxes. This exercises
        # the Windows metadata branch without claiming an actual junction test.
        candidate = self.repo / "reported-reparse"
        candidate.mkdir()
        original_lstat = Path.lstat
        reparse_flag = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)

        def reported_metadata(path):
            actual = original_lstat(path)
            if path == candidate:
                return SimpleNamespace(st_mode=actual.st_mode, st_file_attributes=reparse_flag)
            return actual

        with patch.object(Path, "lstat", reported_metadata):
            self.assertTrue(checker.path_alias(candidate))
            with self.assertRaisesRegex(checker.CheckError, "alias"):
                checker.generated_directories(self.repo, [candidate.name], self.protected)
        write_json(self.repo / GENERATED / "simulated-reparse-metadata.json", {
            "simulated": True, "actual_junction_created": False,
            "reported_st_file_attributes": reparse_flag,
            "scope": "Windows reparse metadata branch and generated-root rejection only",
        })

    def test_boundary_accepts_local_source_and_records_it(self):
        result = self.boundary([self.module()])
        self.assertEqual(result["status"], "passed")
        self.assertEqual(result["checked_local_sources"], ["Toy.lean"])
        self.assertEqual(result["loaded_module_count"], 1)

    def test_boundary_rejects_generated_source_or_olean_even_if_other_path_is_normal(self):
        for kind in ("source", "olean"):
            for root in (self.repo / GENERATED, self.output):
                with self.subTest(kind=kind, root=str(root)):
                    module = self.module()
                    module[kind] = str(root / ("Hidden.lean" if kind == "source" else "Hidden.olean"))
                    with self.assertRaisesRegex(checker.CheckError, "generated evidence"):
                        self.boundary([module])

    def test_boundary_rejects_alias_resolving_into_generated_root(self):
        sources_before_alias = self.snapshot()["lean_sources"]
        alias = self.repo / "evidence-alias"
        if not directory_alias(alias, self.repo / GENERATED):
            self.skipTest("Filesystem does not permit a directory symlink or junction")
        with self.assertRaisesRegex(checker.CheckError, "symlinked source directory"):
            self.snapshot()
        with self.assertRaisesRegex(checker.CheckError, "generated evidence"):
            self.boundary([self.module(source=alias / "Hidden.lean")], sources=sources_before_alias)

    def test_boundary_requires_one_complete_marker(self):
        good = checker.DEPENDENCY_MARKER + json.dumps([self.module()]) + "\n"
        for raw in ("No marker\n", good + good, checker.DEPENDENCY_MARKER + "invalid json\n",
                    checker.DEPENDENCY_MARKER + "[]\n", checker.DEPENDENCY_MARKER + "{}\n"):
            with self.subTest(raw=raw), self.assertRaises(checker.CheckError):
                self.boundary(None, raw=raw)

    def test_boundary_rejects_duplicate_and_incomplete_module_entries(self):
        for modules in ([self.module(), self.module()], [None], [{"module": "Toy"}],
                        [self.module(name="")]):
            with self.subTest(modules=modules), self.assertRaises(checker.CheckError):
                self.boundary(modules)

    def test_boundary_rejects_source_absent_from_before_or_changed_since_before(self):
        before = self.snapshot()["lean_sources"]
        write(self.repo / "Helper.lean", HELPER_V1)
        with self.assertRaisesRegex(checker.CheckError, "outside the input snapshot"):
            self.boundary([self.module(name="Helper", source=self.repo / "Helper.lean")], sources=before)
        write(self.repo / "Toy.lean", TOY_HELPER)
        with self.assertRaisesRegex(checker.CheckError, "differs from the input snapshot"):
            self.boundary([self.module()], sources=before)


class RealLeanSnapshotTests(unittest.TestCase):
    """Real subprocess evidence. Every fixture has its own .lake and no packages."""

    def setUp(self) -> None:
        if LAKE is None:
            self.skipTest("Pass --lake to opt into real Lean/Lake fixture tests")
        self.repo = new_fixture(self.id())
        minimal_repository(self.repo)
        self.output = self.repo / GENERATED / "checker"
        self.args = argparse.Namespace(repo=str(self.repo), manifest="scope.json", lake=LAKE,
                                       output=str(self.output), generated_root=[GENERATED],
                                       entry_module=[], timeout=180)
        self.command_log = self.repo / GENERATED / "setup"
        self.command_log.mkdir(parents=True)

    def bootstrap(self) -> None:
        code = checker.command([LAKE, "update"], self.repo, self.command_log / "lake-update.log", 180)
        self.assertEqual(code, 0, (self.command_log / "lake-update.log").read_text(encoding="utf-8"))

    def execute(self, label="run"):
        stream = io.StringIO()
        with redirect_stdout(stream), redirect_stderr(stream):
            code = checker.run(self.args)
        write(self.repo / GENERATED / (label + "-console.log"), stream.getvalue())
        receipt = json.loads((self.output / "result.json").read_text(encoding="utf-8"))
        write_json(self.repo / GENERATED / (label + "-result.json"), receipt)
        LEAN_RUNS.append({"test": self.id(), "label": label, "returncode": code,
                          "receipt": str(self.repo / GENERATED / (label + "-result.json")),
                          "status": receipt["status"], "error": receipt.get("error"),
                          "build_returncode": receipt.get("build_returncode"),
                          "audit_returncode": receipt.get("audit_returncode")})
        return code, receipt

    def assert_real_build_and_audit_passed(self, receipt):
        self.assertEqual(receipt.get("build_returncode"), 0, receipt)
        self.assertEqual(receipt.get("audit_returncode"), 0, receipt)
        self.assertEqual(receipt["runtime"]["lean_version"], "4.24.0")
        self.assertTrue(receipt["runtime"]["toolchain_runtime_match"])

    def helper_repository(self):
        write(self.repo / "Toy.lean", TOY_HELPER)
        write(self.repo / "Helper.lean", HELPER_V1)
        with (self.repo / "lakefile.toml").open("a", encoding="utf-8") as stream:
            stream.write('[[lean_lib]]\nname = "Helper"\n')

    def test_valid_target_passes_with_opt_in_boundary_guard(self):
        self.bootstrap()
        code, receipt = self.execute()
        self.assertEqual(code, 0, receipt)
        self.assertEqual(receipt["status"], "machine-check-passed")
        self.assert_real_build_and_audit_passed(receipt)
        self.assertEqual(receipt["dependency_boundary"]["checked_local_sources"], ["Toy.lean"])
        self.assertNotIn("inputs_after", receipt)

    def test_actual_untracked_ignored_helper_is_loaded_snapshotted_and_valid_edits_hash(self):
        if shutil.which("git") is None:
            self.skipTest("Git unavailable: cannot establish ignored/untracked identities")
        self.helper_repository()
        git(self.repo, "init", "--quiet")
        write(self.repo / ".gitignore", "Helper.lean\n")
        self.assertEqual(git(self.repo, "ls-files", "--", "Helper.lean").stdout, "")
        self.assertEqual(git(self.repo, "check-ignore", "Helper.lean").stdout.strip(), "Helper.lean")
        self.bootstrap()
        code, before = self.execute("helper-v1")
        self.assertEqual(code, 0, before)
        self.assert_real_build_and_audit_passed(before)
        self.assertIn("Helper.lean", before["inputs"]["lean_sources"])
        self.assertIn("Helper.lean", before["dependency_boundary"]["checked_local_sources"])
        write(self.repo / "Helper.lean", HELPER_V2)
        code, after = self.execute("helper-v2")
        self.assertEqual(code, 0, after)
        self.assert_real_build_and_audit_passed(after)
        self.assertEqual(after["inputs"]["lean_sources"]["Helper.lean"], checker.digest(self.repo / "Helper.lean"))
        self.assertNotEqual(before["inputs"]["lean_sources"]["Helper.lean"],
                            after["inputs"]["lean_sources"]["Helper.lean"])
        self.assertNotEqual(before["inputs"]["input_fingerprint"], after["inputs"]["input_fingerprint"])

    def generated_import(self, quoted: bool, entry_only: bool = False):
        module = "«.project-verification».Hidden" if quoted else "Generated.Hidden"
        source = self.repo / GENERATED / "Hidden.lean" if quoted else self.repo / GENERATED / "Generated/Hidden.lean"
        write(source, "namespace Hidden\ntheorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n\nend Hidden\n")
        write(self.repo / "Bridge.lean", f"import {module}\n")
        if entry_only:
            # Toy remains the ordinary independent theorem from the minimal
            # repository. Only the additional library entry imports Hidden.
            self.args.entry_module = ["Bridge"]
            self.assertNotIn("import", (self.repo / "Toy.lean").read_text(encoding="utf-8"))
        else:
            write(self.repo / "Toy.lean", "import Bridge\nnamespace Toy\ntheorem target (n : Nat) : n + 0 = n := Hidden.add_zero n\nend Toy\n")
        library_name = ".project-verification" if quoted else "Generated"
        src_dir = "." if quoted else GENERATED
        with (self.repo / "lakefile.toml").open("a", encoding="utf-8") as stream:
            stream.write(f'[[lean_lib]]\nname = "Bridge"\n[[lean_lib]]\nname = "{library_name}"\nsrcDir = "{src_dir}"\n')
        self.bootstrap()
        code, receipt = self.execute()
        self.assert_real_build_and_audit_passed(receipt)
        if entry_only:
            self.assertIn("Bridge", receipt["build_command"])
            self.assertEqual(receipt["inputs"]["snapshot_policy"]["additional_entry_modules"], ["Bridge"])
            self.assertIn("import Bridge\n", (self.output / "CheckTargets.lean").read_text(encoding="utf-8"))
        self.assertEqual(code, 1, receipt)
        self.assertEqual(receipt["status"], "failed")
        self.assertIn("generated evidence", receipt.get("error", ""))
        self.assertNotIn("inputs_after", receipt)
        self.assertNotIn(source.relative_to(self.repo).as_posix(), receipt["inputs"]["lean_sources"])
        log = (self.output / "audit.log").read_text(encoding="utf-8")
        markers = [line[len(checker.DEPENDENCY_MARKER):] for line in log.splitlines()
                   if line.startswith(checker.DEPENDENCY_MARKER)]
        self.assertEqual(len(markers), 1)
        loaded = json.loads(markers[0])
        self.assertTrue(any(Path(item["source"]).resolve() == source.resolve() for item in loaded), loaded)
        write_json(self.repo / GENERATED / "identified-generated-import.json",
                   {"quoted": quoted, "entry_only": entry_only, "import": module,
                    "source": str(source), "loaded": loaded})

    def test_extra_entry_generated_dependency_rejected_with_normal_target(self):
        self.generated_import(quoted=False, entry_only=True)

    def test_transitive_generated_source_import_rejected_after_real_successful_audit(self):
        self.generated_import(quoted=False)

    def test_quoted_transitive_generated_import_rejected_after_real_successful_audit(self):
        self.generated_import(quoted=True)

    def test_instrumented_valid_loaded_helper_change_rejected_at_final_stability_guard(self):
        self.helper_repository()
        self.bootstrap()
        original_snapshot = checker.input_snapshot
        calls = 0
        injection = {}

        def snapshot_with_change(*args, **kwargs):
            nonlocal calls
            calls += 1
            if calls == 2:
                # The real build, audit and dependency boundary check have already
                # succeeded. Mutate immediately before the actual final snapshot.
                helper = self.repo / "Helper.lean"
                injection.update({"instrumented": True, "stage": "before second input_snapshot",
                                  "before_sha256": checker.digest(helper)})
                write(helper, HELPER_V2)
                injection["after_sha256"] = checker.digest(helper)
            return original_snapshot(*args, **kwargs)

        with patch.object(checker, "input_snapshot", side_effect=snapshot_with_change):
            code, receipt = self.execute("instrumented-stability")
        write_json(self.repo / GENERATED / "timing-instrumentation.json", injection)
        self.assertEqual(calls, 2)
        self.assertEqual(code, 1, receipt)
        self.assert_real_build_and_audit_passed(receipt)
        self.assertEqual(receipt["dependency_boundary"]["status"], "passed")
        self.assertIn("Helper.lean", receipt["dependency_boundary"]["checked_local_sources"])
        self.assertIn("Inputs changed during verification", receipt.get("error", ""))
        self.assertEqual(receipt["inputs"]["lean_sources"]["Helper.lean"], injection["before_sha256"])
        self.assertEqual(receipt["inputs_after"]["lean_sources"]["Helper.lean"], injection["after_sha256"])
        self.assertNotEqual(injection["before_sha256"], injection["after_sha256"])
        # Prove the replacement is still a real valid theorem source, using the
        # same fixed Lake and the real checker after the failed stability run.
        code, valid_after = self.execute("changed-helper-validity")
        self.assertEqual(code, 0, valid_after)
        self.assert_real_build_and_audit_passed(valid_after)

    def test_instrumented_generated_evidence_growth_during_audit_passes(self):
        self.bootstrap()
        original_command = checker.command
        changes = []

        def command_with_generated_growth(argv, repo, log, timeout):
            code = original_command(argv, repo, log, timeout)
            if log.name == "audit.log":
                probe = self.repo / GENERATED / "peer/Probe.lean"
                for value in (HELPER_V1, HELPER_V2):
                    write(probe, value)
                    changes.append(checker.digest(probe))
                probe.unlink()
                write(self.repo / GENERATED / "peer/OtherProbe.lean", HELPER_V1)
            return code

        with patch.object(checker, "command", side_effect=command_with_generated_growth):
            code, receipt = self.execute("instrumented-generated-growth")
        write_json(self.repo / GENERATED / "timing-instrumentation.json",
                   {"instrumented": True, "stage": "after real audit command", "probe_hashes": changes})
        self.assertEqual(code, 0, receipt)
        self.assert_real_build_and_audit_passed(receipt)
        self.assertEqual(receipt["dependency_boundary"]["status"], "passed")
        self.assertEqual(len(changes), 2)
        self.assertNotEqual(changes[0], changes[1])
        self.assertNotIn("inputs_after", receipt)


def main() -> int:
    global LAKE, VALIDATION
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", help="Absolute fixed-SDK Lake executable; enables real Lean tests")
    parser.add_argument("--validation-dir", type=Path, default=DEFAULT_VALIDATION,
                        help="Parent directory for retained unique test runs")
    options = parser.parse_args()
    if options.lake:
        lake = Path(options.lake)
        if not lake.is_absolute() or not lake.is_file():
            parser.error("--lake must be an existing absolute executable path")
        LAKE = str(lake.resolve())
    options.validation_dir.mkdir(parents=True, exist_ok=True)
    VALIDATION = Path(tempfile.mkdtemp(prefix="run-", dir=options.validation_dir)).resolve()
    started = datetime.now(timezone.utc).isoformat()
    checker_before = checker.digest(Path(checker.__file__))
    suite = unittest.TestSuite([
        unittest.defaultTestLoader.loadTestsFromTestCase(SnapshotPolicyTests),
        unittest.defaultTestLoader.loadTestsFromTestCase(RealLeanSnapshotTests),
    ])
    sdk_path = str(Path(LAKE).parent) + os.pathsep + os.environ.get("PATH", "") if LAKE else os.environ.get("PATH", "")
    with patch.dict(os.environ, {"PATH": sdk_path}):
        result = unittest.TextTestRunner(verbosity=2).run(suite)
    summary = {
        "started_at": started, "finished_at": datetime.now(timezone.utc).isoformat(),
        "mode": "fast-and-real-Lean" if LAKE else "fast-only",
        "lake": LAKE, "checker_sha256_before": checker_before,
        "checker_sha256_after": checker.digest(Path(checker.__file__)),
        "tests_run": result.testsRun, "successful": result.wasSuccessful(),
        "failures": [{"test": test.id(), "traceback": detail} for test, detail in result.failures],
        "errors": [{"test": test.id(), "traceback": detail} for test, detail in result.errors],
        "skipped": [{"test": test.id(), "reason": reason} for test, reason in result.skipped],
        "fixture_directories": FIXTURES, "real_lean_runs": LEAN_RUNS,
        "evidence_scope": "Fixtures only, no project build/cache/source modification; timing injection explicitly labelled",
    }
    write_json(VALIDATION / "summary.json", summary)
    print(f"Retained regression evidence: {VALIDATION / 'summary.json'}")
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
