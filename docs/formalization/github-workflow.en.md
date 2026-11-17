# GitHub branches, PRs, and merging

[Chinese original](github-workflow.md)

On 2026-11-15, the user chose to make this project public. This process governs development deliverables entering `main`. The mathematical standard remains paper-results 1.2; the skill and engineering workflow are version 1.3.1. Entering the main branch does not issue a whole-paper formalization label. Pending trust-policy and author-confirmation states remain unchanged.

## Delivery boundary and final merge operator

The agent completes changes, applicable independent review, actual candidate CI, and the evidence handoff, without merging into main. Under the [goal rules](GOAL.en.md) updated by the user on 2026-11-17, while a ready PR awaits a human merge, automatically advance the next independent branch and PR if subsequent mathematical work does not depend on that PR landing in main. Stop only for an actual dependency block with no independent task, a required user ruling, or a confirmed blocker. This continuation rule adds no permission to merge main, enable auto-merge, or delete branches. Follow an explicit operator assignment and authorization for a new task when one exists.

When the project selects a human final merge, hand over the target branch, reviewed head, latest combined CI, applicable reviews and unresolved issues, and recommended squash method in the existing PR, leaving it unmerged. Do not call readiness completed integration, click or invoke a merge API for the human, or enable auto-merge. If the project explicitly authorizes agent execution, operate on the verified head within that scope. Record the final merge operation, confirmation of mathematical meaning, and whole-paper completion conditions separately.

## Parallel work and PR scope

Create short-lived feature branches from current main around consumable mathematical deliverables, such as a related group of null-cone lemmas. Do not mechanically create branches according to agent count or the 46 slices. Use separate worktrees for tasks requiring different Git checkouts. When sharing a checkout, stay on the same branch, assign file-writing responsibilities explicitly, and let the coordinator stage and commit; individual agents must not switch branches independently.

Unify the minimal interfaces for definitions that are actually shared; consumers may implement in parallel against frozen versions. Use stacked PRs only where a real dependency requires them. After a parent PR is squash-merged, move only the child branch's own increment onto the actual new main and recheck the diff; do not reintroduce the parent's old commits. Implementation, checks, and rolling reverse review of independent tasks continue in parallel. Coordinate the final merge window by dependency order, with the operator determined as above.

Use a draft PR early to show scope and dependencies. Lean code, library entry points, actual target registrations, scope state, and necessary statement records must enter the candidate together as one deliverable. The coordinator integrates central files; do not postpone exposing new targets to the checker until a later cleanup PR. Not every auxiliary lemma in new support code needs registration as a paper target, but explain which reviewed target consumes it. Check independent computations under the original workflow. Check documentation-only or engineering PRs according to their actual impact. Changes without mathematical semantic impact do not need unrelated reverse review; changes to checking capability, scope, or mathematical explanations still require review of the relevant impact.

## Pre-merge checks

1. The PR states the source location, actual declarations and important definitions, assumptions or conditional interfaces, consumers, and remaining work. If it changes the mathematical meaning of the paper or adds a condition, first obtain the necessary user decision for that item; independent work continues.
2. An agent uninvolved in that item's forward implementation independently reads back the frozen source. New engineering rules are reviewed by an agent uninvolved in the changes for behavior and authorization boundaries. Review records retain input identities, findings, and their resolution. Earlier reviews may be reused according to actual differences; recheck only affected declarations and dependencies.
3. GitHub's `project-check` checks the complete project, slice structure, currently registered targets, their provenance, and transitive axioms. A PR run checks out the merge candidate by default; do not replace it with a head-only test and claim that the combination passed. The coordinator also checks new target registration. Green status alone does not judge paper semantics or complete coverage.
4. Record the PR head, target main, candidate commit, key inputs, and CI run. Read current main and the PR head again before merging. When main advances, refresh combined checking and add relevant review if semantics are affected. When an agent is authorized to merge through an API, supply the reviewed head SHA. For a human merge, hand over the specific reviewed head and matching CI. After a version change, update affected evidence before proceeding; an old green result does not replace a current check.
5. Changes to CI, checkers, target inventories, or protection settings receive independent review of the actual diff to confirm the required checks really ran. Even a job with the same name supplied by GitHub Actions could be changed into a no-op; this project does not claim that the platform prevents that modification. Inventory changes cannot remove required results without justification.

## Bilingual delivery

Update the affected Chinese and English documents and PR description together. Check both against the same manuscript, actual Lean declarations, mathematical scope, assumptions, review, and machine status. Keep one set of sources, manifests, and original evidence. Use adjacent `.en.md` reading copies and the English root README.

## Platform protection and coordination duties

The agreed main protection requires PRs; `project-check` supplied by the actual GitHub Actions app, with the branch up to date with its target; administrator enforcement; no force pushes or deletion; linear history; and resolved code discussions. Compare the actual readback against each project requirement. Missing or unknown fields mean insufficient evidence. Checking only administrator enforcement and strictness is not a complete protection pass. The historical [settings readback](github-settings.json) does not replace a current check. This repository uses squash merging and does not enable auto-merge. Branch cleanup follows separate existing authorization; completion of a merge does not itself authorize deletion.

All agents currently share the Oho1e account, so GitHub's required number of approvals from independent accounts is 0, and “require approval of the most recent reviewable push” is not enabled. The PR requirement remains, but a subagent report is not a GitHub Approve. If the user also operates the same account, “a human performs the final merge” is a collaboration rule and tool-behavior boundary; the server cannot identify the operator solely from that account. The coordinator must check independent reports and resolve objections affecting correctness. This requirement and mathematical correspondence are enforced by the workflow. If genuinely independent collaborators join later, approval requirements may be adjusted to their participation; other accounts receive no permission automatically.

This is not GitHub's automatic merge queue. The coordinator prepares ready candidates one at a time in dependency order to prevent agents racing to merge; the actual operator follows the project choice and current authorization. A one-off tool must identify the repository, PR, branch, and reviewed version for that operation. Old scripts retain only their historical purpose. `scripts/pr_readiness.py` performs offline readiness/protection judgments only: it does not merge, replace actual API readbacks, or replace independent mathematical review. Refer new mathematical choices or operations beyond existing remote authorization to the user; do not turn each PR handoff into renewed confirmation of all mathematics or a repeated request for already granted permissions.

Distinguish commands, exit codes, logs, and input versions collected by the actual executor from an agent's account of history. Reports distinguish the real acceptance path, code inspection, offline fault samples, and untested paths. An offline decision test is not an actual GitHub rejection. Run relevant maintenance samples after tool-logic changes according to their impact; do not require every paper to repeat the entire negative suite or fix the number of supervising agents.

## After merging

Until a merge occurs, report “ready, awaiting the final operator's merge,” rather than completed integration. After an actual merge, when observable in the current session or in a later authorized continuation, associate the PR and reviewed head with the actual squash commit, confirm successful push CI for that exact main commit, and then report integration complete and update local main. Do not create automatic background monitoring to wait for a human click. Subsequent tasks can resume from existing PR and run records. Old evidence proves only its bound historical snapshot; actual runs provide machine evidence for new commits. Do not write a commit's own SHA into that commit.

If main CI fails or its result is unknown, suspend further merges, investigate, and repair through a PR on a fix branch. Do not temporarily disable protection or force-push main to restore green status. Successful compilation on main does not eliminate conditional interfaces, undecided trust, or pending author confirmation. Use a whole-paper label only when every completion condition of the mathematical standard is met.

## Official references and actual records

- [Branch protection and required checks](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches)
- [Merge-candidate checkout for PR events](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#pull_request)
- [Squash merging and short-lived branches](https://docs.github.com/en/pull-requests/reference/pull-request-merges)
- [Authors cannot approve their own PRs](https://docs.github.com/en/pull-requests/how-tos/review-pull-requests/approving-a-pull-request-with-required-reviews)

For the actual API readback of protection settings, see the [public visibility and protection record](github-settings.json). GitHub records and this project's review records determine PR and CI execution status; explanatory documents do not replace actual execution.
