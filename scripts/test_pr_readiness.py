"""Direct offline regression tests for the production PR/policy decision code."""

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from pr_readiness import compare_protection, evaluate_readiness


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/pr_readiness.py"
HEAD, BASE, CANDIDATE, OTHER = (letter * 40 for letter in "abcd")
_DEFAULT = object()


def fixtures():
    """A deliberately different repository/provider proves no project hardcoding."""
    expected = {
        "schema_version": 1, "repository": "example/research", "pr_number": 7,
        "branch": "feature/maintenance", "base_branch": "main", "reviewed_head": HEAD,
        "expected_base": BASE, "expected_candidate": CANDIDATE, "merge_actor": "human",
        "required_check": {
            "context": "project-check", "app_id": 420,
            "workflow_path": ".github/workflows/project-check.yml", "event": "pull_request",
            "steps": ["Check the full paper slice plan", "Prepare pinned Lean", "Check the current project stage"],
            "artifact_prefix": "project-check-evidence-",
        },
    }
    observed = {
        "schema_version": 1, "repository": "example/research", "current_main": BASE,
        "current_pr": {
            "number": 7, "head": {"ref": "feature/maintenance", "sha": HEAD},
            "base": {"ref": "main", "sha": BASE}, "merge_commit_sha": CANDIDATE,
            "draft": False, "merged": False, "state": "open", "mergeable": True, "mergeable_state": "clean",
        },
        "receipt": {
            "schema_version": 1, "repository": "example/research", "pr_number": 7,
            "head": HEAD, "base": BASE, "current_main": BASE, "candidate": CANDIDATE,
            "draft": False, "merged": False,
            "run": {"id": 101, "event": "pull_request", "head_sha": HEAD, "path": ".github/workflows/project-check.yml", "status": "completed", "conclusion": "success"},
            "jobs": [{"name": "project-check", "run_id": 101, "check_run_id": 202, "conclusion": "success", "steps": [{"name": name, "conclusion": "success"} for name in expected["required_check"]["steps"]]}],
            "artifacts": [{"name": "project-check-evidence-" + CANDIDATE, "expired": False}],
            "required_check": {"id": 202, "context": "project-check", "app_id": 420, "head_sha": HEAD, "status": "completed", "conclusion": "success"},
        },
    }
    return expected, observed


def set_path(value, path, replacement):
    for key in path[:-1]:
        value = value[key]
    value[path[-1]] = replacement


class ReadinessTests(unittest.TestCase):
    def setUp(self):
        self.expected, self.observed = fixtures()

    def test_explicit_pending_actor_preserves_user_choice(self):
        self.expected["merge_actor"] = "pending"
        result = evaluate_readiness(self.expected, self.observed)
        self.assertTrue(result["ready"])
        self.assertEqual(result["status"], "checks-passed-awaiting-merge-actor")
        self.assertEqual(result["identity"]["merge_actor"], "pending")
        self.assertIs(result["remote_mutation"], False)
        del self.expected["merge_actor"]
        self.assertFalse(evaluate_readiness(self.expected, self.observed)["ready"])

    def assert_refused(self, observed, path=None, expected=_DEFAULT):
        result = evaluate_readiness(self.expected if expected is _DEFAULT else expected, observed)
        self.assertFalse(result["ready"], result)
        self.assertEqual(result["status"], "not-ready")
        self.assertFalse(result["remote_mutation"])
        self.assertTrue(result["errors"])
        if path:
            self.assertTrue(any(path in e["path"] for e in result["errors"]), result)
        return result

    def test_complete_matching_receipt_is_ready_only_for_human(self):
        before = deepcopy((self.expected, self.observed))
        result = evaluate_readiness(self.expected, self.observed)
        self.assertTrue(result["ready"], result)
        self.assertEqual(result["status"], "ready-for-human-merge")
        self.assertEqual(result["identity"]["merge_actor"], "human")
        self.assertEqual(result["mathematical_confirmation"], "not-evaluated")
        self.assertFalse(result["remote_mutation"])
        self.assertEqual((self.expected, self.observed), before)

    def test_actual_check_head_may_be_merge_candidate_but_run_head_stays_head(self):
        self.observed["receipt"]["required_check"]["head_sha"] = CANDIDATE
        self.assertTrue(evaluate_readiness(self.expected, self.observed)["ready"])
        self.observed["receipt"]["run"]["head_sha"] = CANDIDATE
        self.assert_refused(self.observed, "run.head_sha")

    def test_repository_urls_and_case_are_normalized(self):
        self.observed["repository"] = "https://github.com/Example/Research/"
        self.assertTrue(evaluate_readiness(self.expected, self.observed)["ready"])

    def test_every_review_identity_binding_rejects_wrong_or_old_value(self):
        mutations = [
            (("repository",), "other/repo"),
            (("current_pr", "number"), 2), (("current_pr", "head", "ref"), "old-branch"),
            (("current_pr", "head", "sha"), OTHER), (("current_pr", "base", "ref"), "develop"),
            (("current_pr", "base", "sha"), OTHER), (("current_main",), OTHER),
            (("current_pr", "merge_commit_sha"), OTHER),
            (("receipt", "repository"), "other/repo"), (("receipt", "pr_number"), 2),
            (("receipt", "head"), OTHER), (("receipt", "base"), OTHER),
            (("receipt", "current_main"), OTHER), (("receipt", "candidate"), OTHER),
            (("receipt", "run", "head_sha"), OTHER),
        ]
        for path, wrong in mutations:
            with self.subTest(path=path):
                observed = deepcopy(self.observed)
                set_path(observed, path, wrong)
                self.assert_refused(observed, ".".join(path))

    def test_consistently_moved_base_still_requires_new_explicit_expectation(self):
        for path in (("current_main",), ("current_pr", "base", "sha"), ("receipt", "base"), ("receipt", "current_main")):
            set_path(self.observed, path, OTHER)
        self.assert_refused(self.observed, "current_main")

    def test_draft_merged_closed_or_unmergeable_states_are_refused(self):
        for path, wrong in [
            (("current_pr", "draft"), True), (("receipt", "draft"), True),
            (("current_pr", "merged"), True), (("receipt", "merged"), True),
            (("current_pr", "state"), "closed"), (("current_pr", "mergeable"), False),
            (("current_pr", "mergeable"), None), (("current_pr", "mergeable_state"), "blocked"),
            (("current_pr", "mergeable_state"), "unknown"),
        ]:
            with self.subTest(path=path):
                observed = deepcopy(self.observed)
                set_path(observed, path, wrong)
                self.assert_refused(observed, ".".join(path))

    def test_strings_integers_and_null_are_not_booleans(self):
        paths = [("current_pr", "draft"), ("current_pr", "merged"), ("current_pr", "mergeable"),
                 ("receipt", "draft"), ("receipt", "merged"), ("receipt", "artifacts", 0, "expired")]
        for path in paths:
            for wrong in ("false", "true", "", 0, 1, None):
                with self.subTest(path=path, wrong=wrong):
                    observed = deepcopy(self.observed)
                    set_path(observed, path, wrong)
                    self.assert_refused(observed)

    def test_run_check_provider_and_cross_run_splicing_are_refused(self):
        mutations = [
            (("receipt", "run", "path"), ".github/workflows/unrelated.yml"),
            (("receipt", "run", "event"), "push"), (("receipt", "run", "status"), "in_progress"),
            (("receipt", "run", "conclusion"), "failure"), (("receipt", "required_check", "app_id"), 421),
            (("receipt", "required_check", "context"), "same-looking-check"),
            (("receipt", "required_check", "head_sha"), OTHER),
            (("receipt", "required_check", "status"), "queued"),
            (("receipt", "required_check", "conclusion"), "neutral"),
            (("receipt", "required_check", "id"), 203),
            (("receipt", "jobs", 0, "run_id"), 102),
            (("receipt", "jobs", 0, "check_run_id"), 203),
            (("receipt", "jobs", 0, "conclusion"), "failure"),
        ]
        for path, wrong in mutations:
            with self.subTest(path=path):
                observed = deepcopy(self.observed)
                set_path(observed, path, wrong)
                self.assert_refused(observed)

    def test_each_required_step_must_exist_once_and_succeed(self):
        for i in range(3):
            for conclusion in ("skipped", "neutral", "failure", "cancelled", None):
                with self.subTest(step=i, conclusion=conclusion):
                    observed = deepcopy(self.observed)
                    observed["receipt"]["jobs"][0]["steps"][i]["conclusion"] = conclusion
                    self.assert_refused(observed)
            observed = deepcopy(self.observed)
            observed["receipt"]["jobs"][0]["steps"].pop(i)
            self.assert_refused(observed, "steps")
            observed = deepcopy(self.observed)
            observed["receipt"]["jobs"][0]["steps"].append(deepcopy(observed["receipt"]["jobs"][0]["steps"][i]))
            self.assert_refused(observed, "steps")

    def test_missing_duplicate_and_wrong_job_are_refused(self):
        for jobs in ([], [dict(self.observed["receipt"]["jobs"][0], name="unrelated")], self.observed["receipt"]["jobs"] * 2):
            with self.subTest(jobs=jobs):
                observed = deepcopy(self.observed)
                observed["receipt"]["jobs"] = jobs
                self.assert_refused(observed, "jobs")

    def test_missing_expired_wrong_candidate_or_duplicate_artifact_is_refused(self):
        for artifacts in ([], [{"name": "project-check-evidence-" + HEAD, "expired": False}],
                          [{"name": "project-check-evidence-" + CANDIDATE, "expired": True}],
                          self.observed["receipt"]["artifacts"] * 2):
            with self.subTest(artifacts=artifacts):
                observed = deepcopy(self.observed)
                observed["receipt"]["artifacts"] = artifacts
                self.assert_refused(observed, "artifacts")

    def test_every_required_observation_field_must_be_present(self):
        containers = [(), ("current_pr",), ("current_pr", "head"), ("current_pr", "base"),
                      ("receipt",), ("receipt", "run"), ("receipt", "required_check"),
                      ("receipt", "jobs", 0), ("receipt", "jobs", 0, "steps", 0), ("receipt", "artifacts", 0)]
        for path in containers:
            node = self.observed
            for key in path:
                node = node[key]
            for omitted in node:
                with self.subTest(container=path, omitted=omitted):
                    observed = deepcopy(self.observed)
                    target = observed
                    for key in path:
                        target = target[key]
                    del target[omitted]
                    self.assert_refused(observed)

    def test_unversioned_and_unknown_version_evidence_cannot_pass(self):
        for path in (("schema_version",), ("receipt", "schema_version")):
            for wrong in (None, 2, "1", True, 1.0):
                with self.subTest(path=path, wrong=wrong):
                    observed = deepcopy(self.observed)
                    set_path(observed, path, wrong)
                    self.assert_refused(observed, "schema_version")

    def test_expected_criteria_are_explicit_and_unknown_ones_refused(self):
        for omitted in self.expected:
            with self.subTest(omitted=omitted):
                expected = deepcopy(self.expected)
                del expected[omitted]
                self.assert_refused(self.observed, expected=expected)
        for path, wrong in [(("merge_actor",), "agent"), (("merge_actor",), "unknown"),
                            (("required_check", "steps"), []), (("required_check", "app_id"), True),
                            (("reviewed_head",), "abc"), (("pr_number",), True),
                            (("schema_version",), True), (("new_required_gate",), True),
                            (("required_check", "new_required_gate"), True)]:
            with self.subTest(path=path):
                expected = deepcopy(self.expected)
                set_path(expected, path, wrong)
                self.assert_refused(self.observed, expected=expected)

    def test_malformed_structures_fail_closed_without_exceptions(self):
        for wrong in (None, [], "unknown", True, 1):
            self.assert_refused(wrong)
            self.assert_refused(self.observed, expected=wrong)
        for path in (("current_pr",), ("current_pr", "head"), ("receipt",), ("receipt", "run"),
                     ("receipt", "jobs", 0), ("receipt", "jobs", 0, "steps", 0), ("receipt", "artifacts", 0)):
            with self.subTest(path=path):
                observed = deepcopy(self.observed)
                set_path(observed, path, None)
                self.assert_refused(observed)


class ProtectionTests(unittest.TestCase):
    def setUp(self):
        self.expected = json.loads((ROOT / "docs/formalization/github-settings.json").read_text(encoding="utf-8"))
        self.observed = deepcopy(self.expected)

    def test_actual_project_policy_matches_without_mutation(self):
        before = deepcopy((self.expected, self.observed))
        result = compare_protection(self.expected, self.observed)
        self.assertTrue(result["ready"], result)
        self.assertEqual(result["status"], "policy-matches")
        self.assertEqual((self.expected, self.observed), before)

    def test_generic_repository_and_provider_are_caller_selected(self):
        for policy in (self.expected, self.observed):
            policy["repository"] = "example/research"
            policy["main_protection"]["required_checks"][0]["app_id"] = 420
        self.assertTrue(compare_protection(self.expected, self.observed)["ready"])

    def test_each_actual_policy_field_is_compared(self):
        for group in ("main_protection", "repository_merge_settings"):
            for key, value in self.expected[group].items():
                with self.subTest(group=group, key=key):
                    observed = deepcopy(self.observed)
                    observed[group][key] = not value if type(value) is bool else (value + 1 if type(value) is int else [])
                    result = compare_protection(self.expected, observed)
                    self.assertFalse(result["ready"], result)
                    self.assertTrue(any(key in e["path"] for e in result["errors"]), result)

    def test_old_two_field_predicate_cannot_hide_missing_pr_force_or_checks(self):
        # Actual vulnerability samples: admins and strict remain true throughout.
        for key, bad in (("required_pull_request", False), ("allow_force_pushes", True), ("required_checks", [])):
            with self.subTest(key=key):
                observed = deepcopy(self.observed)
                observed["main_protection"][key] = bad
                self.assertTrue(observed["main_protection"]["enforce_admins"])
                self.assertTrue(observed["main_protection"]["strict_status_checks"])
                self.assertFalse(compare_protection(self.expected, observed)["ready"])

    def test_context_and_provider_both_must_match(self):
        for key, wrong in (("context", "other-check"), ("app_id", 15369), ("app_id", None)):
            with self.subTest(key=key, wrong=wrong):
                observed = deepcopy(self.observed)
                observed["main_protection"]["required_checks"][0][key] = wrong
                self.assertFalse(compare_protection(self.expected, observed)["ready"])

    def test_required_check_order_is_irrelevant_but_duplicates_rejected(self):
        self.expected["main_protection"]["required_checks"].append({"context": "second-check", "app_id": 420})
        self.observed["main_protection"]["required_checks"] = list(reversed(self.expected["main_protection"]["required_checks"]))
        self.assertTrue(compare_protection(self.expected, self.observed)["ready"])
        self.observed["main_protection"]["required_checks"].append(deepcopy(self.observed["main_protection"]["required_checks"][0]))
        self.assertFalse(compare_protection(self.expected, self.observed)["ready"])

    def test_missing_unknown_and_untyped_policy_fields_never_pass(self):
        for group in ("main_protection", "repository_merge_settings"):
            for key, value in self.expected[group].items():
                for wrong in (None, "true", "false", "unknown"):
                    with self.subTest(group=group, key=key, wrong=wrong):
                        observed = deepcopy(self.observed)
                        observed[group][key] = wrong
                        self.assertFalse(compare_protection(self.expected, observed)["ready"])
                observed = deepcopy(self.observed)
                del observed[group][key]
                self.assertFalse(compare_protection(self.expected, observed)["ready"])
            for target in ("expected", "observed"):
                expected, observed = deepcopy(self.expected), deepcopy(self.observed)
                (expected if target == "expected" else observed)[group]["future_required_rule"] = True
                self.assertFalse(compare_protection(expected, observed)["ready"])
        for wrong in (True, "0", -1, 0.0):
            self.observed["main_protection"]["required_approving_review_count"] = wrong
            self.assertFalse(compare_protection(self.expected, self.observed)["ready"])

    def test_repository_visibility_version_and_raw_github_shapes_fail_closed(self):
        for key, wrong in (("repository", "other/repo"), ("visibility", "private"), ("schema_version", 2)):
            observed = deepcopy(self.observed)
            observed[key] = wrong
            self.assertFalse(compare_protection(self.expected, observed)["ready"])
        self.assertFalse(compare_protection(self.expected, {"enforce_admins": {"enabled": True}, "required_status_checks": {"strict": True}})["ready"])


class CLITests(unittest.TestCase):
    def run_cli(self, operation, expected, observed, raw=False):
        with tempfile.TemporaryDirectory(prefix="pr-readiness-test-") as directory:
            expected_path, observed_path = Path(directory) / "expected.json", Path(directory) / "observed.json"
            expected_path.write_text(expected if raw else json.dumps(expected), encoding="utf-8")
            observed_path.write_text(observed if raw else json.dumps(observed), encoding="utf-8")
            result = subprocess.run([sys.executable, "-B", str(SCRIPT), operation, "--expected", str(expected_path), "--observed", str(observed_path)], capture_output=True, text=True, encoding="utf-8", check=False)
            self.assertEqual(result.stderr, "")
            return result.returncode, json.loads(result.stdout)

    def test_cli_reads_explicit_inputs_and_returns_actual_function_result(self):
        expected, observed = fixtures()
        code, result = self.run_cli("readiness", expected, observed)
        self.assertEqual(code, 0)
        self.assertEqual(result, evaluate_readiness(expected, observed))
        observed["current_main"] = OTHER
        code, result = self.run_cli("readiness", expected, observed)
        self.assertEqual(code, 1)
        self.assertEqual(result, evaluate_readiness(expected, observed))

    def test_cli_pending_actor_does_not_claim_human_selection(self):
        expected, observed = fixtures()
        expected["merge_actor"] = "pending"
        code, result = self.run_cli("readiness", expected, observed)
        self.assertEqual(code, 0)
        self.assertEqual(result["status"], "checks-passed-awaiting-merge-actor")
        self.assertEqual(result, evaluate_readiness(expected, observed))
        observed["current_main"] = OTHER
        code, result = self.run_cli("readiness", expected, observed)
        self.assertEqual(code, 1)
        self.assertEqual(result, evaluate_readiness(expected, observed))

    def test_cli_policy_acceptance_and_original_predicate_counterexample(self):
        expected = json.loads((ROOT / "docs/formalization/github-settings.json").read_text(encoding="utf-8"))
        observed = deepcopy(expected)
        code, result = self.run_cli("protection", expected, observed)
        self.assertEqual(code, 0)
        self.assertEqual(result, compare_protection(expected, observed))
        observed["main_protection"]["required_pull_request"] = False
        code, result = self.run_cli("protection", expected, observed)
        self.assertEqual(code, 1)
        self.assertEqual(result, compare_protection(expected, observed))

    def test_cli_bad_json_duplicate_keys_and_non_json_constants_are_structured_errors(self):
        for raw in ("{", '{"schema_version":1,"schema_version":1}', '{"schema_version":NaN}',
                    '{"schema_version":Infinity}', '{"pr_number":1e400}', '{"pr_number":-1e400}'):
            with self.subTest(raw=raw):
                code, result = self.run_cli("readiness", raw, "{}", raw=True)
                self.assertEqual(code, 2)
                self.assertEqual(result["status"], "input-error")
                self.assertFalse(result["ready"])


if __name__ == "__main__":
    unittest.main()
