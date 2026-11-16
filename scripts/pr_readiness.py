"""Offline, fail-closed PR readiness and branch-policy comparisons (schema 1).

Usage: python scripts/pr_readiness.py {readiness,protection} --expected X.json
       --observed Y.json
JSON is read from those two files; the result is written only to stdout. Exit 0
means ready/matching, 1 means refused, and 2 means unreadable/invalid JSON input.
There are no network, Git, merge, filesystem-write, or signature operations.

Readiness expected schema:
  schema_version, repository (owner/repo or GitHub URL), pr_number, branch,
  base_branch, reviewed_head, expected_base, expected_candidate, merge_actor
  ("human" or explicitly "pending"), required_check={context, app_id, workflow_path,
  event ("pull_request"), steps (nonempty names), artifact_prefix}.
All commit IDs must be complete 40-character hexadecimal Git object IDs.

Readiness observed schema:
  schema_version, repository, current_main, current_pr={number, head:{ref,sha},
  base:{ref,sha}, merge_commit_sha, draft, merged, state, mergeable,
  mergeable_state}, receipt={schema_version, repository, pr_number, head, base,
  current_main, candidate, draft, merged, run:{id,event,head_sha,path,status,
  conclusion}, jobs:[{name,run_id,check_run_id,conclusion,steps:[{name,
  conclusion}]}], artifacts:[{name,expired}], required_check:{id,context,
  app_id,head_sha,status,conclusion}}.

The observer must fetch actual run/jobs/artifacts/check-run data, preserving
GitHub values. run.head_sha is the PR head, whereas candidate is the temporary
merge commit checked by this project's default pull_request checkout. The
candidate-named upload binds that checkout evidence; the matching check-run ID
and job.run_id bind provider/check evidence to the selected run. A check-run's
actual head_sha may be the PR head or merge candidate. A legacy unversioned
pr-ci.json is historical input, not an admissible receipt: a new observation
must supply missing provider/run/path/version fields from actual sources.

Protection inputs use the normalized github-settings.json shape: schema_version,
repository, main_protection, repository_merge_settings, and optional visibility.
All documented policy fields are required and compared, including false and
zero values. Historical annotations such as observed_at/main_at_configuration
are not policy. Raw GitHub branch protection must first be normalized explicitly
(e.g. enabled objects to real booleans); absent/unknown fields cannot pass.

These functions assess supplied evidence, not its authenticity or wall-clock
freshness. The caller must collect a current snapshot and refresh it if the PR
or base moves; matching identities are checked here. A ready result authorizes
no operation and makes no mathematical/semantic/human-confirmation assertion.
With merge_actor="pending", successful evidence yields
checks-passed-awaiting-merge-actor: ready means only that supplied machine
conditions match, not that a merge actor has been selected or authorized.
"""

import argparse
import json
import math
from pathlib import Path
import re
import sys


SCHEMA_VERSION = 1
_SHA = re.compile(r"[0-9a-fA-F]{40}\Z")
_REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")
_EXPECTED_KEYS = {
    "schema_version", "repository", "pr_number", "branch", "base_branch",
    "reviewed_head", "expected_base", "expected_candidate", "merge_actor",
    "required_check",
}
_CHECK_KEYS = {"context", "app_id", "workflow_path", "event", "steps", "artifact_prefix"}
_MERGE_KEYS = {
    "allow_squash_merge", "allow_merge_commit", "allow_rebase_merge",
    "allow_auto_merge", "delete_branch_on_merge",
}
_PROTECTION_BOOLS = {
    "required_pull_request", "require_last_push_approval", "strict_status_checks",
    "enforce_admins", "required_linear_history", "allow_force_pushes",
    "allow_deletions", "required_conversation_resolution",
}
_PROTECTION_KEYS = _PROTECTION_BOOLS | {"required_approving_review_count", "required_checks"}
_POLICY_KEYS = {
    "schema_version", "repository", "main_protection", "repository_merge_settings",
    "visibility", "observed_at", "main_at_configuration",
    "independent_review_enforcement", "paper_formalization_verified",
}


class _Validation:
    def __init__(self):
        self.errors = []

    def error(self, code, path, expected=None, actual=None):
        self.errors.append({"code": code, "path": path, "expected": expected, "actual": actual})

    def object(self, value, path, required, allowed=None):
        if not isinstance(value, dict):
            self.error("invalid-type", path, "object", value)
            return {}
        for key in sorted(required - value.keys()):
            self.error("missing-field", path + "." + key, "present")
        if allowed is not None:
            for key in sorted(value.keys() - allowed):
                self.error("unknown-field", path + "." + key, "documented field", value[key])
        return value

    def scalar(self, value, path, kind):
        valid = {
            "string": lambda: isinstance(value, str) and bool(value.strip()),
            "bool": lambda: type(value) is bool,
            "positive-int": lambda: type(value) is int and value > 0,
            "count": lambda: type(value) is int and value >= 0,
            "sha": lambda: isinstance(value, str) and _SHA.fullmatch(value) is not None,
            "repository": lambda: _repository(value) is not None,
        }[kind]()
        if not valid:
            self.error("invalid-type-or-value", path, kind, value)

    def sequence(self, value, path, nonempty=False):
        if not isinstance(value, list) or (nonempty and not value):
            self.error("invalid-type-or-value", path, "nonempty array" if nonempty else "array", value)
            return []
        return value

    def version(self, obj, path):
        if type(obj.get("schema_version")) is not int or obj.get("schema_version") != SCHEMA_VERSION:
            self.error("unsupported-schema", path + ".schema_version", SCHEMA_VERSION, obj.get("schema_version"))

    def equal(self, actual, expected, path):
        if type(actual) is not type(expected) or actual != expected:
            self.error("mismatch", path, expected, actual)


def _repository(value):
    if not isinstance(value, str):
        return None
    name = value.removeprefix("https://github.com/").removesuffix("/")
    return name.casefold() if _REPOSITORY.fullmatch(name) else None


def _fields(v, obj, path, fields):
    for key, kind in fields.items():
        v.scalar(obj.get(key), path + "." + key, kind)


def _result(operation, v, identity=None):
    ok = not v.errors
    result = {
        "schema_version": SCHEMA_VERSION,
        "operation": operation,
        "status": ("ready-for-human-merge" if operation == "readiness" else "policy-matches") if ok else "not-ready",
        "ready": ok,
        "remote_mutation": False,
        "mathematical_confirmation": "not-evaluated",
        "errors": v.errors,
    }
    if identity is not None:
        result["identity"] = identity
    return result


def evaluate_readiness(expected, observed):
    """Return a JSON-ready decision without changing either supplied object.

    Expected is an explicit per-PR review lock, not a guessed repository default.
    Observed is a versioned receipt plus current PR/main observation. Unknown
    expected criteria are rejected rather than silently ignored. Extra observed
    metadata is permitted, but every required field and its type is validated.
    Human handoff or an explicitly undecided actor is supported; neither is
    mathematical confirmation, semantic review, or authorization to merge.
    """
    v = _Validation()
    e = v.object(expected, "expected", _EXPECTED_KEYS, _EXPECTED_KEYS)
    o = v.object(observed, "observed", {"schema_version", "repository", "current_main", "current_pr", "receipt"})
    v.version(e, "expected")
    v.version(o, "observed")
    _fields(v, e, "expected", {
        "repository": "repository", "pr_number": "positive-int", "branch": "string",
        "base_branch": "string", "reviewed_head": "sha", "expected_base": "sha",
        "expected_candidate": "sha", "merge_actor": "string",
    })
    if e.get("merge_actor") not in ("human", "pending"):
        v.error("unsupported-merge-actor", "expected.merge_actor", ["human", "pending"], e.get("merge_actor"))
    c = v.object(e.get("required_check"), "expected.required_check", _CHECK_KEYS, _CHECK_KEYS)
    _fields(v, c, "expected.required_check", {
        "context": "string", "app_id": "positive-int", "workflow_path": "string",
        "event": "string", "artifact_prefix": "string",
    })
    v.equal(c.get("event"), "pull_request", "expected.required_check.event")
    names = v.sequence(c.get("steps"), "expected.required_check.steps", nonempty=True)
    for i, name in enumerate(names):
        v.scalar(name, f"expected.required_check.steps[{i}]", "string")
    if all(isinstance(x, str) for x in names) and len(set(names)) != len(names):
        v.error("duplicate-step", "expected.required_check.steps", "unique names", names)
    _fields(v, o, "observed", {"repository": "repository", "current_main": "sha"})
    p = v.object(o.get("current_pr"), "observed.current_pr", {
        "number", "head", "base", "merge_commit_sha", "draft", "merged", "state", "mergeable", "mergeable_state",
    })
    _fields(v, p, "observed.current_pr", {
        "number": "positive-int", "merge_commit_sha": "sha", "draft": "bool", "merged": "bool",
        "state": "string", "mergeable": "bool", "mergeable_state": "string",
    })
    for key in ("head", "base"):
        branch = v.object(p.get(key), "observed.current_pr." + key, {"ref", "sha"})
        _fields(v, branch, "observed.current_pr." + key, {"ref": "string", "sha": "sha"})
    r = v.object(o.get("receipt"), "observed.receipt", {
        "schema_version", "repository", "pr_number", "head", "base", "current_main", "candidate",
        "draft", "merged", "run", "jobs", "artifacts", "required_check",
    })
    v.version(r, "observed.receipt")
    _fields(v, r, "observed.receipt", {
        "repository": "repository", "pr_number": "positive-int", "head": "sha", "base": "sha",
        "current_main": "sha", "candidate": "sha", "draft": "bool", "merged": "bool",
    })
    run = v.object(r.get("run"), "observed.receipt.run", {"id", "event", "head_sha", "path", "status", "conclusion"})
    _fields(v, run, "observed.receipt.run", {
        "id": "positive-int", "event": "string", "head_sha": "sha", "path": "string", "status": "string", "conclusion": "string",
    })
    check = v.object(r.get("required_check"), "observed.receipt.required_check", {"id", "context", "app_id", "head_sha", "status", "conclusion"})
    _fields(v, check, "observed.receipt.required_check", {
        "id": "positive-int", "context": "string", "app_id": "positive-int", "head_sha": "sha", "status": "string", "conclusion": "string",
    })
    jobs = v.sequence(r.get("jobs"), "observed.receipt.jobs", nonempty=True)
    for i, job in enumerate(jobs):
        path = f"observed.receipt.jobs[{i}]"
        job = v.object(job, path, {"name", "run_id", "check_run_id", "conclusion", "steps"})
        _fields(v, job, path, {"name": "string", "run_id": "positive-int", "check_run_id": "positive-int", "conclusion": "string"})
        for j, step in enumerate(v.sequence(job.get("steps"), path + ".steps")):
            step_path = f"{path}.steps[{j}]"
            step = v.object(step, step_path, {"name", "conclusion"})
            _fields(v, step, step_path, {"name": "string", "conclusion": "string"})
    artifacts = v.sequence(r.get("artifacts"), "observed.receipt.artifacts", nonempty=True)
    for i, artifact in enumerate(artifacts):
        path = f"observed.receipt.artifacts[{i}]"
        artifact = v.object(artifact, path, {"name", "expired"})
        _fields(v, artifact, path, {"name": "string", "expired": "bool"})
    if v.errors:
        return _result("readiness", v)

    for path, actual in (("observed.repository", o["repository"]), ("observed.receipt.repository", r["repository"])):
        v.equal(_repository(actual), _repository(e["repository"]), path)
    for path, actual in (("observed.current_pr.number", p["number"]), ("observed.receipt.pr_number", r["pr_number"])):
        v.equal(actual, e["pr_number"], path)
    v.equal(p["head"]["ref"], e["branch"], "observed.current_pr.head.ref")
    v.equal(p["base"]["ref"], e["base_branch"], "observed.current_pr.base.ref")
    for path, actual in (("observed.current_pr.head.sha", p["head"]["sha"]), ("observed.receipt.head", r["head"]), ("observed.receipt.run.head_sha", run["head_sha"])):
        v.equal(actual, e["reviewed_head"], path)
    for path, actual in (("observed.current_pr.base.sha", p["base"]["sha"]), ("observed.current_main", o["current_main"]), ("observed.receipt.base", r["base"]), ("observed.receipt.current_main", r["current_main"])):
        v.equal(actual, e["expected_base"], path)
    for path, actual in (("observed.current_pr.merge_commit_sha", p["merge_commit_sha"]), ("observed.receipt.candidate", r["candidate"])):
        v.equal(actual, e["expected_candidate"], path)
    for path, actual in (("observed.current_pr.draft", p["draft"]), ("observed.current_pr.merged", p["merged"]), ("observed.receipt.draft", r["draft"]), ("observed.receipt.merged", r["merged"])):
        v.equal(actual, False, path)
    v.equal(p["state"], "open", "observed.current_pr.state")
    v.equal(p["mergeable"], True, "observed.current_pr.mergeable")
    v.equal(p["mergeable_state"], "clean", "observed.current_pr.mergeable_state")
    for key, wanted in (("path", c["workflow_path"]), ("event", c["event"]), ("status", "completed"), ("conclusion", "success")):
        v.equal(run[key], wanted, "observed.receipt.run." + key)
    for key, wanted in (("context", c["context"]), ("app_id", c["app_id"]), ("status", "completed"), ("conclusion", "success")):
        v.equal(check[key], wanted, "observed.receipt.required_check." + key)
    if check["head_sha"] not in (e["reviewed_head"], e["expected_candidate"]):
        v.error("unbound-check-head", "observed.receipt.required_check.head_sha", [e["reviewed_head"], e["expected_candidate"]], check["head_sha"])
    selected = [j for j in jobs if j["name"] == c["context"]]
    if len(selected) != 1:
        v.error("missing-or-ambiguous-job", "observed.receipt.jobs", "exactly one " + c["context"], len(selected))
    else:
        job = selected[0]
        v.equal(job["run_id"], run["id"], "observed.receipt.jobs.required.run_id")
        v.equal(job["check_run_id"], check["id"], "observed.receipt.jobs.required.check_run_id")
        v.equal(job["conclusion"], "success", "observed.receipt.jobs.required.conclusion")
        for name in names:
            steps = [s for s in job["steps"] if s["name"] == name]
            if len(steps) != 1:
                v.error("missing-or-ambiguous-step", "observed.receipt.jobs.required.steps", "exactly one " + name, len(steps))
            else:
                v.equal(steps[0]["conclusion"], "success", "observed.receipt.jobs.required.steps." + name)
    artifact_name = c["artifact_prefix"] + e["expected_candidate"]
    matching = [a for a in artifacts if a["name"] == artifact_name]
    if len(matching) != 1:
        v.error("missing-or-ambiguous-artifact", "observed.receipt.artifacts", "exactly one " + artifact_name, len(matching))
    else:
        v.equal(matching[0]["expired"], False, "observed.receipt.artifacts.required.expired")
    result = _result("readiness", v, {key: e[key] for key in ("repository", "pr_number", "branch", "reviewed_head", "expected_base", "expected_candidate", "merge_actor")})
    if result["ready"] and e["merge_actor"] == "pending":
        result["status"] = "checks-passed-awaiting-merge-actor"
    return result


def _validate_policy(v, value, path):
    obj = v.object(value, path, {"schema_version", "repository", "main_protection", "repository_merge_settings"}, _POLICY_KEYS)
    v.version(obj, path)
    v.scalar(obj.get("repository"), path + ".repository", "repository")
    if "visibility" in obj:
        v.scalar(obj["visibility"], path + ".visibility", "string")
    merge = v.object(obj.get("repository_merge_settings"), path + ".repository_merge_settings", _MERGE_KEYS, _MERGE_KEYS)
    _fields(v, merge, path + ".repository_merge_settings", {key: "bool" for key in _MERGE_KEYS})
    protection = v.object(obj.get("main_protection"), path + ".main_protection", _PROTECTION_KEYS, _PROTECTION_KEYS)
    _fields(v, protection, path + ".main_protection", {key: "bool" for key in _PROTECTION_BOOLS} | {"required_approving_review_count": "count"})
    checks = v.sequence(protection.get("required_checks"), path + ".main_protection.required_checks")
    for i, check in enumerate(checks):
        check_path = f"{path}.main_protection.required_checks[{i}]"
        check = v.object(check, check_path, {"context", "app_id"}, {"context", "app_id"})
        _fields(v, check, check_path, {"context": "string", "app_id": "positive-int"})
    if not v.errors:
        pairs = [(check["context"], check["app_id"]) for check in checks]
        if len(set(pairs)) != len(pairs):
            v.error("duplicate-required-check", path + ".main_protection.required_checks", "unique context/provider pairs", checks)
    return obj


def compare_protection(expected, observed):
    """Compare every normalized policy field, with strict boolean/count types.

    Repository identity, optional expected visibility, all merge settings, and
    all protection fields are compared. Required checks use exact unordered
    context/app_id pairs. Neither repository names nor provider IDs are built
    into the function; use the project's github-settings.json as expected.
    This comparison does not assert that independent mathematical review is
    enforced by GitHub, nor that observed policy remains current afterwards.
    """
    v = _Validation()
    e = _validate_policy(v, expected, "expected")
    o = _validate_policy(v, observed, "observed")
    if v.errors:
        return _result("protection", v)
    v.equal(_repository(o["repository"]), _repository(e["repository"]), "observed.repository")
    if "visibility" in e:
        v.equal(o.get("visibility"), e["visibility"], "observed.visibility")
    for key in sorted(_MERGE_KEYS):
        v.equal(o["repository_merge_settings"][key], e["repository_merge_settings"][key], "observed.repository_merge_settings." + key)
    for key in sorted(_PROTECTION_KEYS - {"required_checks"}):
        v.equal(o["main_protection"][key], e["main_protection"][key], "observed.main_protection." + key)
    pairs = lambda policy: sorted([c["context"], c["app_id"]] for c in policy["main_protection"]["required_checks"])
    v.equal(pairs(o), pairs(e), "observed.main_protection.required_checks")
    return _result("protection", v, {"repository": e["repository"]})


def _load(path):
    def unique_object(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise ValueError("duplicate JSON key: " + key)
            obj[key] = value
        return obj
    def reject_constant(value):
        raise ValueError("non-JSON numeric constant: " + value)
    def finite_float(value):
        number = float(value)
        if not math.isfinite(number):
            raise ValueError("non-finite numeric conversion: " + value)
        return number
    return json.loads(Path(path).read_text(encoding="utf-8-sig"), object_pairs_hook=unique_object,
                      parse_constant=reject_constant, parse_float=finite_float)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("operation", choices=("readiness", "protection"))
    parser.add_argument("--expected", required=True, help="explicit versioned expectation JSON")
    parser.add_argument("--observed", required=True, help="versioned actual observation JSON")
    args = parser.parse_args(argv)
    try:
        expected, observed = _load(args.expected), _load(args.observed)
    except (OSError, ValueError, UnicodeError) as error:
        result = {"schema_version": SCHEMA_VERSION, "operation": args.operation, "status": "input-error", "ready": False, "remote_mutation": False, "errors": [{"code": "input-error", "message": str(error)}]}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 2
    decision = evaluate_readiness if args.operation == "readiness" else compare_protection
    result = decision(expected, observed)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["ready"] else 1


if __name__ == "__main__":
    sys.exit(main())
