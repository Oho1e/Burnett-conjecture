# Multi-agent parallel work: project rules and trial run

[Chinese original](parallel-workflow.md)

The user wants to reduce total duration by starting multiple subagents simultaneously. This document retains an earlier trial with “main-agent integration and shared builds, two independent proof implementations, and rolling review in free slots.” Current mathematical progress is recorded in scope. Adjust parallelism to ready tasks and actual tool capacity; do not turn a historical environment's agent capacity into a universal skill quota.

## Historical trial: real quadratic expansion and null-cone cross terms

| Task | Mathematical deliverable | Exclusive writes |
| --- | --- | --- |
| Full B expansion | Real symmetric component identity at paper lines 447–448, with an actual Lean proof | `Burnett/Algebra/QuadraticExpansion.lean` |
| Null kernel and gauge cross terms | Ricci-kernel equivalence for nonzero ξ with s=0, and gauge cross-term cancellation for the real bilinear F | `Burnett/Algebra/NullKernel.lean` |
| Main agent | Shared definitions, versions and build coordination, final interface assembly, central inventories, CI, and reports | Shared definitions and central project records |
| Rolling review | Independently read back frozen actual types and important definitions, then compare with the paper | The reviewer's own evidence directory |

Both implementations shared `RicciSymbol.lean` and `QuadraticDefs.lean`. The latter added only definitions for symmetry, ordered fourfold contraction, tensor square, and the real bilinear physical form. Complex Hermitian extension and null-cone quotient positivity remained subsequent obligations. The null-kernel branch did not assume the other branch's B expansion or the unfinished Hermitian extension.

The main agent first built the shared definitions once, then recorded source hashes and the pinned SDK import environment. Implementation agents read that version directly and checked Lean in separate source files and private output directories. The main agent coordinated public `.lake` build outputs and dependency changes. If a shared version needed changes, affected tasks were notified first, then relevant proofs and checks were refreshed according to the actual diff. Only definitions needed for that round were unified; branches retained room to organize their own auxiliary lemmas.

## Current parallel arrangement

1. Select tasks whose inputs are actually available from existing slices and progress, considering which downstream blocks they will remove. Explain definition, proof, and application edges separately; do not create unnecessary waiting by following paper order.
2. Prioritize parallel work for independently deliverable tasks with separate write responsibilities. Task packets reuse the paper, interfaces, and consumers, adding only the current objective, write ownership, and evidence destination.
3. The coordinator integrates shared mathematical definitions and central records. Branches submit actual new declarations, check results, and still-missing inputs without upgrading the parent item's status themselves.
4. Serialize only builds that contend for the same output or change the same dependency. Checks in exclusive directories reading frozen public dependencies may run in parallel. Whether isolation is worthwhile depends on preparation and integration costs.
5. Once a result is checkable, hand it to an agent uninvolved in its forward construction for independent readback while other implementations continue. Reuse earlier reviews according to input applicability, and recheck affected parts after important definition changes.
6. When a branch finishes, awaits input, or finds an interface mismatch, select another ready task. A joint closure task must still check the same parameters, witnesses, and all conclusions of coupled estimates.
7. After integrating the relevant deliverable scope, the coordinator runs complete candidate checks, actual target/axiom audits, central scope updates, and this project's authorized remote CI. Multiple local passes do not replace checking the combination. The final merge operator is determined by the [GitHub workflow](github-workflow.en.md); this maintenance round stops at a ready PR, with the long-term default still awaiting the user's choice.

Use saved source snapshots locatable by hash for integration and review, recording the public dependency version. Working files may continue developing. If hashes differ, resolve the version mismatch, obtain the matching snapshot, or re-establish the affected check evidence.

When an agent message or tool call fails, verify artifacts actually saved to disk and their applicable check records, then continue integration and independent review according to actual evidence. Record message status, machine checking, and mathematical status separately.

## Parallel principle in the skill entry point

Skill version 1.3.1 retains this principle; detailed PR integration and handoff arrangements are in the [GitHub workflow](github-workflow.en.md):

> When tasks have ready input interfaces, can be delivered independently, and can avoid shared-write conflicts, prioritize available subagents for parallel progress. The main agent coordinates necessary shared definitions and candidate integration responsibility; final merging follows the project's operator assignment and authorization. Adjust parallelism to task dependencies, actual waiting, and integration cost. Once an implementation is checkable, an agent uninvolved in its construction may perform rolling independent reverse review while other ready work continues.

Detailed assignments, shared-write responsibilities, and PR arrangements belong in workflow references for version 1.3.1; the entry point retains only decision rules. The mathematical standard 1.2, archived older skill packages, and the personal skills directory remain unchanged.

## Assessing actual benefit

Record actual deliverables, preparation of shared definitions, dependency waiting, checking/integration, and rework. The main measure is when machine-checked mathematics with matching semantics becomes available to a joint closure point. Without a comparable serial baseline, do not report a speedup factor or estimate whole-paper completion from agent, file, or theorem counts.

F06 is a potential bottleneck shared by several downstream dependencies. The graph has no reliable duration estimates, so outgoing-edge count alone cannot establish the global critical path. If shared definitions repeatedly change or branches frequently wait on each other, adjust the task boundary or reduce parallelism at that point. If the bottleneck shifts to F05 or an external analysis interface, adjust later scheduling accordingly.

In this trial, one working file continued changing after its hash was published. Copy verification detected the mismatch, and work resumed from the saved frozen v1. In another branch, the final reply encountered a tool error after source and actual compilation were complete; the main agent retained the artifacts and check evidence and sent them for independent review. Both cases resumed from actual versions without treating message status as mathematical status.

## Mathematical deliverables from that trial

The two implementation branches completed the full real B expansion, null-kernel equivalence, and real gauge cross-term cancellation. The main agent derived the real null-cone B formula in the combined module. Four new main targets had actual Lean proofs, giving nine registered supporting targets together with the original five. Independent readback and the combined library build passed. Plain mathematical explanations and version evidence appear in `docs/statements/quadratic-real-algebra.md` and `quadratic-real-algebra-review.md`.

This shows that the trial's task split and rolling handoff could run; it does not establish a speedup factor. At that time F06 general polarization, complex Hermitian extension, and physical quotient positivity remained open. For the later real mixed deliverable, see the [actual statement](../statements/real-polarization.en.md); consult scope for current remaining obligations. Skill version 1.3.1 retains the parallel principle and refines PR handoff without treating the historical trial as a test of every path in the new workflow.
