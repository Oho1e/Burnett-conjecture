# Paper formalization goal and continuation rules

[简体中文](GOAL.zh-CN.md)

This file records the project's standing goal. The current mathematical status is recorded in `scope.json` and the evidence applicable to the current version.

Follow the work plan to formalize all formal results of the locked paper, the designated key unnumbered results, and their necessary dependencies in Lean. Apply trust policy A, independent reverse review and actual machine checks. Use the approved paper version, scope and standard.

The user added the automatic continuation rule on November 17, 2026. Once a pull request is ready for human merge, proceed with the next independent pull request unless it requires the preceding one to land on `main`.

- Save the reviewed revision and handoff evidence after the applicable independent review, full candidate verification, and CI and artifact checks for the combination with current `main`.
- Use the dependency graph to find ready work. Start independent work from an applicable verified `main` and continue implementation, review, and PR preparation. Create PRs for substantive changes.
- If a successor requires a preceding merge, look for other independent work. Save the evidence and wait if nothing independent is executable, a mathematical decision requires the user, or a blocker is confirmed. Address routine compilation and cache problems as part of the work.
- The user performs the final merge into `main`. Agent operations exclude merging into `main`, enabling auto-merge, force-pushing, deleting branches, and publishing verification tags.
- When `main` advances, verify its actual new revision and push CI. Refresh affected candidates, scope records, and combination checks. Reuse prior source reviews only where still applicable. The coordinator resolves conflicts in shared records.

Historical handoffs may document a wait for human merge under earlier rules. Keep the goal open while its completion requirements are unmet. PR readiness, reviewer agreement, and green CI are each evidence of their own scope.

## Bilingual delivery

On November 18, 2026, the user asked to backfill bilingual documentation and then continue the formalization in bilingual mode. Each subsequent PR updates the affected Chinese and English explanations together. Cover its mathematical results, assumptions, scope changes, review, actual checks, and handoff status. Use the English README as the entrance for submission and external readers.

Keep one copy of the Lean sources, scripts, machine manifests, and original verification artifacts. Both languages refer to the same `scope.json`, `slices.json`, manuscript, and machine receipts. Keep declaration names, result IDs, versions, mathematical meanings, and statuses consistent. Preserve frozen logs, hashes, and historical versions as recorded. Translations explain the original evidence.

The English slice view records the manifest hash. When a slice interface changes, update the affected English passages and hash and regenerate the Chinese view using the existing script.

`AGENTS.md` and `tools/lean-paper-results/SKILL.md` each remain the single operative entry point. Adjacent English reading copies use `.en.md`. `README.md` is the English entrance, and `README.zh-CN.md` is the Chinese counterpart. Resolve wording differences against the locked manuscript, the actual Lean types, and the approved project decisions, then update both languages.
