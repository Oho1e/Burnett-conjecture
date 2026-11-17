# Parallel delivery and GitHub merges

[Chinese source](github-pr.zh-CN.md)

This is the English counterpart to the skill and engineering workflow 1.3.1. The mathematical standard is `paper-results` 1.2. Apply the relevant parts to each project.

## Authorization and platform settings

Follow the agreed repository, visibility, and operations for this paper. Use existing express authorization. Before a visibility change, verify the tracked files and history against the distribution scope. Resolve out-of-scope material or credentials before publication and continue independent tasks.

For a protected main branch, consider requiring PRs, specified CI and an up-to-date combination, blocking force pushes and deletions, and applying the rule to administrators. Respect an equivalent existing ruleset. Compare actual fields and required check providers with the agreed policy. Report the extent of the comparison and any platform limits precisely. Check the current GitHub plan before changing protection. [GitHub branch protection](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches)

## Branches and parallel ownership

Use short-lived branches for independently useful mathematical deliverables. Establish small shared interfaces when multiple consumers need them. Work from frozen inputs while upstream PRs are pending where possible.

Name the manuscript range, inputs, consumers, writable files, and evidence for each task. Use isolated worktrees or let the coordinator own branch switches with exclusive file ownership. The coordinator integrates shared definitions, dependency locks, manifests, and build outputs. Run independent checks in exclusive directories. Notify affected tasks when inputs change and refresh the affected evidence. Keep witnesses, parameters, and limit order aligned across joint obligations.

## Draft PRs and target registration

Open a draft when a reviewable deliverable exists. Describe its scope, manuscript locations, declarations, open premises, prerequisite PRs, and review/check links. [PR template](../assets/repo-template/.github/pull_request_template.md)

Include the code, library entry, auditable targets, and correct scope/documentation in the same merge candidate. Register auxiliary declarations according to actual paper scope and proof dependency closure. Ordinary engineering and documentation changes need review of their actual impact on check coverage, scope, or mathematical descriptions.

## Independent reading and combination checks

Assign the review of frozen mathematics to someone who did not construct it. Read actual types and definitions back against the paper while ready work continues. Recheck affected meanings after material changes and reuse applicable review on verified proof-only edits. Refresh relevant machine evidence. [Two-way workflow](workflow.en.md)

Verify the combination with latest `main`. Check that the workflow using `pull_request` actually checks the merge candidate rather than only the head. Refresh evidence when the base advances. Match review to actual changes, including changes to checker configuration or the target list. Use read-only CI permissions for ordinary PRs. [PR event and merge candidate](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#pull_request)

## Final merge

The coordinator checks the scope, unresolved issues, applicable review, target registration, and current combination CI. Only final merges need a single serial window. Follow genuine branch dependencies and allow independent work to proceed.

Follow the authorized merge actor. In human-merge mode, hand off the open and ready PR with the base, reviewed head, CI, independent review, open issues, and suggested merge method. Leave auto-merge disabled and the final merge to the human. Where the project expressly delegates merge authority to an agent, verify the head and stay within that authorization. Treat a one-time authorization as scoped to that action.

Math interpretation confirmation and the merge actor are separate. If an account is shared, the task agreement and actual operation determine who merged. The platform account alone does not distinguish actors. Squash merging is generally useful for a short-lived deliverable. Follow the project convention when preserving individual commits matters. Refresh dependent branches against the actual squashed base, verify the diff, and rerun affected checks. [Merge methods](https://docs.github.com/en/pull-requests/reference/pull-request-merges)

## Post-merge evidence and status

Record readiness, actual integration, and native main push CI separately. Check the actual main run when it can be observed. If it fails, diagnose and fix it before further merges. Continue independent implementation and diagnosis as appropriate. Record actual results and keep pending checks pending.

Preserve the PR head, tested base and candidate, manuscript and relevant source/configuration/dependency versions, and review scope. Map a squash commit to its PR and link actual main CI. Use existing evidence records. Distinguish execution receipts from reports of execution. State whether evidence came from the real acceptance path, a code check, or an offline sample. Keep untested paths visible. Avoid recording the SHA of a commit inside a file that is part of that commit.

Explicit conditional interfaces and pending author confirmations may appear on development main. The original standard governs confirmation, trust, and completion. The user decides manuscript ambiguities, extra hypotheses, and changed conclusions.

## Account approval and independent review

Record semantic review and GitHub approval separately. Where reviewers share one account, report the actual separation of roles. A PR author cannot approve their own PR. For a single-account project, PR checks and independent review reports can be required without an unavailable second-account approval. Follow the agreed approver rules in a multi-account project. [GitHub review requirements](https://docs.github.com/en/pull-requests/how-tos/review-pull-requests/approving-a-pull-request-with-required-reviews)
