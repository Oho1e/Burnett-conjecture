# Maintenance 1.3.1: input snapshots and PR evidence handoff

[Chinese original](maintenance-1.3.1.md)

This round changes engineering tools and documentation; the mathematical standard remains paper-results 1.2. The paper, Lean proofs, 21 mathematical supporting targets, trust decisions, and existing semantic-confirmation scope remain unchanged. The older 1.3 skill package and historical F06 receipts are retained; old fingerprints are not overwritten with new values.

This round stops at a reviewable PR and does not merge it. The user has not yet chosen the future final merge operator. The tool permits an explicit pending record without choosing a human or agent for the user.

## Input snapshots

The normal entry point remains `python scripts/check_project.py --repo .`. The project entry point passes the following to the underlying check_paper:

```text
--generated-root .project-verification --entry-module Burnett
```

The additional generated directory is an explicit root-level boundary; the generic checker gains no such exclusion by default. Reject overlap between this directory and configuration, manifest, or registered module sources. Conservatively include all other project Lean sources, including untracked or Git-ignored sources. Git status does not determine verification inputs. Record the policy and additional entry point in the input fingerprint.

When an exclusion is declared, the actual Lean audit outputs the direct/transitive module paths actually loaded by targets and the additional entry point. Python checks source and olean paths, rejects modules loaded from the generated-evidence directory, and confirms that ordinary local sources are included in the input snapshot with matching content. Growth of temporary evidence no longer affects stability judgments of central inputs; auxiliary probes, audit code, and logs still retain their own hashes.

This guard was tested in this project under pinned Lean 4.24.0 and the default source layout. findLean is a source-search mapping, not proof of compilation provenance for arbitrary multiple srcDir layouts or same-named source roots. The existing trust boundary for the SDK, pinned dependencies, and precompiled caches still requires disclosure under the original policy. Adapt and test layout changes before claiming that this generated-directory convention guarantees complete dependencies in an arbitrary project.

## PR and protection judgments

`scripts/pr_readiness.py` only reads explicit JSON and emits a judgment. It does not access the network, invoke Git, modify files, or merge:

```text
python scripts/pr_readiness.py readiness --expected <本PR版本锁.json> --observed <本轮API观察.json>
python scripts/pr_readiness.py protection --expected docs/formalization/github-policy.json --observed <本轮保护回读.json>
```

Check the two results separately; both must hold at handoff. Readiness binds the repository, PR, branch, reviewed head, current base/main, actual combined candidate, and the CI run, job/check-run identity, actually successful steps, and candidate artifact. Preserve GitHub's original run head_sha rather than rewriting it to the combined candidate SHA to manufacture agreement. Missing fields, stale versions, wrong identities, skipped steps, and invalid artifacts cannot pass.

Compare protection against this project's [expected policy](github-policy.json), checking each agreed field: required PRs, approval count, strict checks and provider, administrator enforcement, no force pushes/deletion, linear history, discussion resolution, and merge method. The old [settings observation](github-settings.json) is historical rather than current evidence. Unknown fields do not pass by default; two booleans do not represent the whole policy. Observers should retain raw API facts and the source of normalization; normalizing fields must not change their meaning.

The pure judgment does not establish that inputs came from a real API or are still current. The coordinator obtains evidence from the current server and refreshes affected parts after head/base changes. It also provides no mathematical review, user confirmation, or authorization for remote operations.

## Final operator and handoff

With an explicit human selection, satisfied machine conditions produce `ready-for-human-merge`; explicit pending produces `checks-passed-awaiting-merge-actor`. The latter only says that the supplied machine conditions agree, not that an operator has been selected or AI merging is permitted. A missing operator field does not default to human.

For a human merge, the agent supplies the PR link, actual head, latest combined CI, independent review, remaining issues, and recommended merge method. The human checks the current version on GitHub and performs Squash and merge. This does not mean the human reviewed every Lean line or grant mathematical certification. Agent execution requires corresponding explicit authorization; this maintenance tool has no merge capability. Under a shared GitHub account, task assignment is a workflow/tool boundary: the platform cannot identify the operator solely from that account.

Before merging, report only readiness/pending status, not completed integration. After an actual merge, check CI for the exact main commit in an observable current session or an authorized later task. Do not create automatic background monitoring to wait for a human click.

## Validation and maintenance frequency

- `scripts/test_pr_readiness.py` directly tests the actual pure functions and CLI, including stale candidates, wrong identities, assembled evidence from different runs, missing/skipped steps, invalid artifacts, protection deviations, pending status, and strict JSON boundaries.
- `scripts/test_snapshot_policy.py` includes fast tests and optional real Core-only Lean fixtures. It directly asserts source sets and valid source changes, and checks that specified guards reject real generated dependencies and changes during execution. Rejecting a bad proof does not replace snapshot-coverage tests.
- The original `test_check_paper.py` continues testing the original rejection behavior for compilation, theorem kind, provenance, and transitive axioms.
- `maintenance-check.yml` runs the maintenance suite only for PR changes on tool-related paths or manual dispatch. Ordinary mathematical deliverables need not repeat the entire maintenance negative suite. Original project-build and slice CI continue.

Actual local/CI commands, skipped items, independent review, and PR state are recorded separately in this round's maintenance report. Distinguish function-level samples, controlled-time injection, real Lean execution, and real GitHub runs; do not extrapolate them to every fault or all mathematical content.
