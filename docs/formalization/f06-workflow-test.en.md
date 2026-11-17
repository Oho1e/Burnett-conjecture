# F06 real mixed polarization: actual skill and workflow test

[Chinese original](f06-workflow-test.md)

This file preserves test results for the frozen pre-merge deliverable. The actual PR is [PR2](https://github.com/Oho1e/Burnett-conjecture/pull/2). Its description adds the actual mapping of final head, combined candidate, squash main, and both CI runs; the commit does not contain its own new SHA. A final end-to-end report is saved separately in the workspace reports directory.

## Test scope and conclusion boundaries

This used the in-project lean-paper-results 1.3 and GitHub workflow; the mathematical standard remained paper-results 1.2. Baseline main was 6880f4ab31b423e14a173c18e45fa3cf0a9c9103; the locked paper SHA256 was e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e.

The consumable deliverable selected from the existing 46 slices was F06 (lines 430–466): real mixed polarization, the diagonal bridge, mixed cancellation for any two amplitudes in the noncharacteristic kernel, and the mixed null-cone formula. Existing algebraic inputs were ready. Unfinished parts were not removed from the original slice inventory; this round implemented only this local deliverable.

**The local mathematical deliverable passed actual machine checking and independent type-level readback. F06 as a whole remained partially complete.** Complex Hermitian extension, null frames/physical quotient positivity, and geometry/measure bridges remained open; the 17 numbered results were not complete, and no whole-paper formalization label was issued. Actual engineering closure separately requires this PR's final combined CI, merge, and exact-main CI; local mathematical success does not imply them.

## Roles, independence, and parallelism

| Role | Actual duties and write boundary |
| --- | --- |
| Forward implementation agent | Read the skill, paper, and actual inputs; wrote only RealPolarization.lean and private local outputs; did not operate on scope/Git/remotes |
| Independent reverse-review agent | First wrote an independent specification from the locked paper, then read frozen actual types and definitions; did not substitute the forward self-review for judgment or participate in construction |
| Dedicated supervision agent | Jointly supervised versions, role separation, evidence, and status with the main agent; did not replace mathematical review |
| Isolated gate-probe agent | Read artifacts actually available at that time to judge readiness, without network, Git, merging, or mathematical approval |
| Main agent | Integrated shared records, independently ran complete builds/queries, maintained central registration, PRs, and run observation, and checked other agents with the supervisor |

Implementation and independent source-specification extraction ran in parallel. After source freeze, rolling reverse review proceeded while the main agent built shared inputs and registered targets. The shared checkout stayed on one feature branch; file ownership separated source writes, private outputs were isolated, and the main agent coordinated shared Lake outputs. With no comparable serial baseline, no speedup factor is reported.

## Mathematical deliverable and actual evidence

The frozen [RealPolarization.lean](../../Burnett/Algebra/RealPolarization.lean) SHA256 was 5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4. M=(C(k,l)+C(l,k))/2 was first defined from the original connection cross product, followed by proofs of bilinearity, M(k,k)=original Q(k), and M=(Q(k+l)−Q(k)−Q(l))/2, then both kernel conclusions. The target's right-hand side was not defined as a new B and proved merely by its definition.

Noncharacteristic mixed cancellation needs no extra symmetry/signature assumption. The mixed null-cone formula retains real symmetric G/k/l, nonzero ξ, s=0, two independent kernel conditions, and coefficient 1/4. The real form is not called complex Hermitian. See the [mathematical explanation](../statements/real-polarization.en.md), [independent actual-type readback](../statements/real-polarization-review.en.md), and [raw actual-type/axiom output](../statements/real-polarization-actual-types.txt).

- The new module has 29 public declarations: 2 definitions and 27 theorems. Central queries of actual types and transitive axioms exited 0 for all 29. There was no sorryAx, project mathematical axiom, or native_decide; only the three customary foundational axioms occurred.
- The 9 main supporting targets and 3 independent scalar-interface audit targets were registered together with source, library entry point, and scope records, totaling 21 targets and 86 inventory entries. Auxiliary interfaces do not masquerade as new formal results from the paper.
- Full local check_project actually passed, as did precise target existence/provenance/transitive-axiom auditing; the final receipt matched current scope bytes. Relevant machine bindings were refreshed after status updates/new user delegation changed scope. Rerun counts are not additional test coverage.
- check_slices passed, retaining 46 slices, 135 links, and the 17 formal-result mappings. The 17 structural/work-packet tests passed; all 12 new placements belong to F06.
- The toolchain, dependency lock, paper, old 9 targets, skill 1.3, and checker were unchanged. Checks were not weakened to obtain green status. Detailed hashes/receipt summaries appear in the [machine evidence](f06-machine-evidence.json).

## Local confirmation delegated by the user

The user's actual reply to this round's plain mathematical explanation was “带子代理你来确认” (“You and subagents should confirm it”). The main agent and independent review agent confirmed the correspondence against original definitions, actual types, and proofs. It was recorded separately as local agent confirmation delegated by the user, not as item-by-item review by the user or author personally. The explanation SHA256 was de1ca6bda24b85980fe45968869841696bac314187c83ddd8eeb63ad60d19edc.

The main agent's key reasoning was that c is linear in the amplitude, so original Q(k+l)−Q(k)−Q(l) is exactly the two cross terms. The same Ricci kernel is closed under addition; in the noncharacteristic case all three diagonal terms vanish. On the null cone, the original diagonal formula and symmetric bilinearity of F make the cross difference 2F(k,l); division by 2 still gives ξ_bξ_c F(k,l)/4. This matches the independent agent's actual-type check and a nonzero two-amplitude example. The basis is mathematical reasoning rather than multi-agent voting.

The delegation covered only this real-algebra deliverable. Confirmation states for the old 9 targets and the final trust choice did not change. The frozen reverse report's human-pending state was historical at report creation. The later delegation is recorded in existing review/scope records without rewriting history as already confirmed then.

## Actual faults, supervision, and repairs

| Observation | Actual response and effect |
| --- | --- |
| An old temporary GitHub script was bound to PR1/an old head | The supervisor found it; the main agent used this round's PR2 and explicit head/base/candidate receipts. The old success remained historical only. |
| Lean proofs of sum interchange/distribution did not close | Forward v1/v2 failure logs were retained. Final v5 compiled after correction, and the main agent fully built the frozen source again. |
| A participant additionally expanded a full mixed component formula | The main agent limited the first deliverable to the agreed targets. After withdrawing the extra formula, the source was rechecked/frozen. The unused formula is counted as neither completion nor failure of this round. |
| A type probe used unsupported pp.width | The print probe exited 1 and was retained. Removing the display option gave query exit 0 without changing formal mathematical source. |
| Compilation-history metadata risked confusing self-report with actual receipts | After the supervisor's comment, it was explicitly labeled forward self-report; primary evidence used the main agent's independent subprocess results and raw logs. |
| The full local fingerprint included temporary Lean files | Actual receipts included 32 probes/historical copies under .project-verification, unlike clean CI. Each snapshot was bound separately, comparing actual commit, core sources/pins/targets rather than claiming equal complete fingerprints. |

These events are supported by actual logs or file inspections. Local proof debugging, print compatibility failures, scope management, and snapshot policy are distinct issues; they cannot collectively be labeled mathematical counterexamples or total workflow failure.

## Isolated gate probe

Another agent uninvolved in construction read the artifacts then available under the skill. It judged that initial-draft green CI could not release the final deliverable or justify completed integration. The read scope was still pending, reviewed_head was null, and draft CI covered only 896c883eb8b061fbaa04cdca21dbfb7636def749 and the old 9 targets. No final 21-target candidate/exact-main CI was supplied. It also allowed reuse of matching independent readback, without additionally requiring the whole slice to close, renewed human confirmation, or a second GitHub account's approval. The full [probe report](f06-gate-probe.en.md) preserves the input hashes read then.

This was a decision test on the read snapshot without remote operations, not an actual GitHub-rejected merge attempt. It does not assert that unsupplied machine receipts had never run elsewhere. Later evidence does not rewrite the probe as having had that evidence at the time.

## PR closure and untested paths

At this report's freeze, final candidate CI, merge, and main CI still awaited execution. The following were subsequent acceptance steps. Initial draft PR/CI displayed scope rather than replacing the final deliverable. Only after source/type readback, 21-target checks, same-candidate registration, and supervision checks were complete did the main agent populate reviewed_head with the actually frozen commit, update the PR, obtain merge-candidate CI against latest main, and inspect actual steps/artifacts. Squash on that precise head was followed by push-CI confirmation for new main. Actual links, commit relationships, and final status are recorded in [PR2](https://github.com/Oho1e/Burnett-conjecture/pull/2); evidence does not create circular commits to insert its own SHA.

This round did not run live negative cases for force pushes, branch deletion, disabling protection, intentionally permissive CI, or tampering with formal mathematical declarations. It did not force main advancement, network failure, or merge conflicts. It also did not test the entire complex/quotient-positivity/measure dependency chain or all paper results. The report establishes only actual execution of this local deliverable and the listed probes, not skill reliability for every paper or fault.

## Maintenance recommended from the test

1. Keep the exact PR number, reviewed head, and candidate binding as engineering-script inputs to avoid reading old successes when copying one-off scripts; no new approval bot is needed.
2. Distinguish actual subprocess exit codes from agent narrative in machine receipts. Prefer probe commands already validated on the pinned Lean; display-option errors are not proof failures.
3. Maintain the checker's snapshot policy separately: explicitly define generated-evidence directories or a controlled tracked-source set, and use actual bad-target regressions to check that exclusion rules do not omit inspected code. This round retained the tested 1.3/checker unchanged rather than mixing that repair into the mathematical deliverable.

No defect requiring reversal of this mathematical deliverable was found. These maintenance items do not mean the whole slice/paper reached the completion standard.
