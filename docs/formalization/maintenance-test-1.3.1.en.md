# Maintenance validation record for 1.3.1

[Chinese original](maintenance-test-1.3.1.md)

This record states only local tests and independent review on 2026-11-16. Remote execution is determined by GitHub Actions for the corresponding PR commit and its handoff receipt. This record neither predicts CI success nor claims that the PR has merged.

See the [maintenance description](maintenance-1.3.1.en.md) for changes and applicability. The mathematical standard remains paper-results 1.2. The paper, all Lean proofs, runtime and dependencies, 21 targets, and mathematical/trust-confirmation states did not change.

## Actually executed

| Check | Result | Supported conclusion |
| --- | --- | --- |
| `scripts/check_project.py --repo .`, pinned Lean 4.24.0 | Passed, 21 targets; 8 project Lean sources | Current project build and target existence, provenance, and transitive-axiom checks passed; not whole-paper verification. |
| `scripts/check_slices.py --repo .`, `scripts/test_slices.py` | Structural check and 17 tests passed | Structure including 46 slices, 86 inventory entries, and 135 links is consistent; semantic completeness is not certified. |
| `scripts/test_pr_readiness.py` | 28 passed | Actual pure-function/CLI acceptance and rejection, including pending status, assembled cross-run evidence, stale candidates, omitted steps, strict JSON, and protection deviations. |
| Additional negative cases written by the independent reviewer | 10 passed | Independent supplementary checks against actual production code, not combined with the preceding row into a single test suite. |
| `scripts/test_snapshot_policy.py --lake <固定lake>` | 23 of 25 passed, 2 skipped | Source sets, valid source changes, root-level exclusions, and actual Lean import boundaries; two actual alias tests were limited by local creation permissions. |
| Original `test_check_paper.py --lake <固定lake>` against the new checker | 20 scenarios and 1 expected regression passed | Original rejection behavior for compilation, theorem kind, provenance, and transitive axioms was preserved. |
| Official `skill-creator/scripts/quick_validate.py` | Standalone skill package and project snapshot both passed | Skill structure is valid; this does not replace behavioral tests. |

Snapshot tests include 7 real Lean test methods, totaling 9 actual checker runs. The during-run mutation inserts a still-compilable source change at a controlled point. The build, Lean audit, boundary check, and final snapshot comparison still invoke the actual implementation. Other tests operate at function level or on simulated paths; they must not all be described as actual filesystem tests. The Windows reparse-metadata simulation did not create a real junction.

The original rejection suite's old baseline and patched version are stored separately. Old-checker results are not counted as a pass for the patch. An initial failure caused by an excessively long fixture path is also retained. Only after shortening the test directory name were the results above obtained.

## Independent review and boundaries

Independent agents separately inspected snapshot design/real Lean boundaries, the pure PR judgment, and textual authorization boundaries, and ran tests directly. Their findings led to entry-point alias checks, rejection of nonfinite JSON numbers, explicit pending state, and consistency fixes to merge responsibilities in the README.

The generated-directory guard was validated under pinned Lean 4.24.0 and the default source layout. `findLean` does not prove compilation provenance for same-named modules across arbitrary multiple source roots. Pinned dependencies, SDK, and caches retain their existing trust boundary. Local skips for real symlinks/junctions require checking in an environment permitting creation; a simulated pass does not replace them. Maintenance CI will run the actual Linux tests, with results recorded separately.

Overstated wording in the old F06 report is addressed by an [appended clarification](f06-report-clarification.en.md), leaving the old sealed report unchanged. Ordinary mathematical PRs retain the original project CI. The maintenance negative suite runs for tool changes rather than imposing a new mandatory process on every slice.

This round stops at a reviewable PR. `merge_actor=pending` neither selects the final operator nor authorizes AI merging. There is no post-merge main CI evidence; the project remains development and whole-paper label conditions are unmet.

## First remote run and corrections

The first PR3 maintenance CI exited 2 when invoking snapshot tests: the workflow supplied `--lake lake`, but the test entry point required an existing absolute SDK path, so no test methods ran. The original job log is retained and does not count as a Linux regression pass. The workflow was narrowly changed to `--lake "$(elan which lake)"`, resolving the executable from the pinned toolchain. Neither test logic nor the production checker was relaxed. Actual results for the corrected commit are recorded in the PR handoff receipt; the old commit's green project CI is not a result for the new candidate.

The second Linux run actually executed 25 tests. Alias cases previously skipped on Windows exposed a fixture-order error: taking a new snapshot before calling the import-boundary guard correctly triggered the earlier symlink source scan, producing a different error from the expected one. The test was changed to save the source snapshot before creating the alias, then separately assert source-scan rejection of the alias and import-guard rejection of a path resolving into the generated directory. No regex or production check was relaxed. The second failed artifact is retained. The new test was synchronized to both the standalone skill package and repository snapshot; the final Linux result still belongs to the new candidate.
