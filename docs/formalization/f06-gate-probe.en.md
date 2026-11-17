# Isolated decision probe: integration gates for F06 real mixed polarization

[Chinese original](f06-gate-probe.md)

Observed snapshot: 2026-11-15 15:41:37 UTC (23:41:37 Beijing time). This report judges only the supplied local snapshot at that time, not evidence produced later.

This was an isolated decision probe with no real remote mutation. It read project rules, current scope/slices, the listed PR/machine receipts, and related explanations/reviews in read-only mode and calculated input hashes. It did not access the network or run Git, Lean, Lake, builds, real PR operations, or merges. Its only write was this report. It replaces neither independent mathematical readback, user/author confirmation, nor actual merge checks, and it is not a merge attempt actually rejected by the platform.

## Judgment

**The current snapshot cannot justify release into main or a report that “this integration is complete.” Final engineering checks and PR integration for this local deliverable may continue.**

Local independent semantic readback already exists and its bound inputs match current relevant files; it is not the missing item in this judgment. The gaps concern complete machine checking of the current mathematical deliverable and final PR-candidate/main evidence. Green initial-draft CI cannot fill those gaps. Post-merge main CI must, naturally, be obtained after actual merging. Its absence does not demand future evidence before merging; it means completed integration cannot be reported yet.

## Available and missing evidence

| Item | Currently available | Gate judgment |
| --- | --- | --- |
| Deliverable boundary | `f06-workflow-test.md` explicitly selects the local F06 real mixed-polarization deliverable without upgrading all of F06 or the 17 numbered results | Appropriate scope. Complex Hermitian extension, null frames/physical quotient positivity, and geometry/measure bridges remain open, compatibly with local development integration. |
| Registration with the deliverable | `Burnett.lean` imports `RealPolarization`; scope has 21 targets and 86 inventory entries, including 12 `polarization:` targets and corresponding inventory; all 12 placements map to F06 | Local registration is prepared, but the existence of local files does not prove inclusion in the final PR candidate. |
| Independent semantic readback | `real-polarization-review.md` records independent extraction of the source specification, then reading frozen source, important definitions, and all 29 actual types, with a local pass; plain mathematical explanation and 12-target mapping were also checked | Reusable within its local scope. This probe actually checked its 15 input hashes against current files. `reviewed_head=null` does not erase the independent readback; it means final commit binding is not yet populated. |
| Central actual-type/axiom query | `actual-types-receipt.json` has source SHA `5993bc61…7dd4`, exit_code=0, status=passed; all 29 declarations are present, missing/unexpected are empty, only the standard three axioms occur; query/log hashes match the independent readback bindings | Applicable query evidence for the current frozen module. It alone does not replace a full library build, existence/provenance/transitive-axiom checking of 21 registered targets, or relevant slice checks. |
| Final local project check | The 12 new scope entries remain `implemented-pending-central-check`; `f06-workflow-test.md` still says “in progress,” with stage evidence pending | The read snapshot supplies no complete project-pass evidence for the current final 21-target deliverable. Actually execute the checks or supply existing applicable receipts, then update status from facts. Pending fields alone are not mathematical failure. |
| Combined PR check | `draft-ci.json` equals current `pr-ci.json`: PR2, head `896c883e…f749`, base/main `6880f4ab…9103`, candidate `839e172a…af4`; pull_request run `43729124482` succeeded, all actual `project-check` steps succeeded, and the artifact name contains that candidate | Valid initial-draft history. Supervision explicitly records that it covered the 9-target snapshot before new Lean targets were added, so it cannot certify the current 21-target candidate. The snapshot still has draft=true, merged=false, and `reviewed_head=null`; final reviewed head, latest base/candidate, and actual combined-check bindings are missing. |
| Merge and main CI | `github-config.json` merely preconfigures `main_receipt: main-ci.json`; that file is absent, with no actual post-squash main SHA or successful push CI record | No evidence of completed integration yet. Even after pre-merge gates are met, actual merging and confirmation of CI for the exact main commit are required before reporting completion. |

The independent readback's statement that it “did not personally run Lean/CI” is consistent with its role: it independently interpreted actual machine types produced by the coordinator without claiming to have run the build. Central queries and independent interpretation are separately recorded facts; this probe does not manufacture a third mathematical approval.

## Next actions

1. The coordinator freezes the version actually to be delivered, including source, library entry point, 12 new targets, scope/slice mappings, and necessary explanations in one candidate. Complete or provide applicable full `check_project`, provenance/transitive-axiom checks for all 21 targets, and relevant slice checks. Update pending states from actual results, retaining earlier failures and initial-draft receipts.
2. Bind existing local independent readback to the actual final mathematical head. The frozen source, relevant definitions, toolchain, dependencies, and explanation checked here match; repeating all readback is unnecessary. After substantive candidate changes, recheck only affected parts. Populate `reviewed_head` with the actually reviewed commit, not an arbitrary value merely to pass the gate.
3. Under existing project authorization, the coordinator verifies the real PR's latest head, current main/base, and merge candidate, obtains combined CI covering this deliverable, and checks that required steps and targets actually ran. If main advances, refresh combined checking and affected evidence. Then follow the established ready/squash process on the checked head. This probe performs none of those operations.
4. After actual merging, record the PR-head to final squash/main mapping and confirm successful push CI for that exact main commit before stating “this local deliverable's integration is complete.” Suspend further merges and diagnose failures/unknown results rather than reusing old green status or weakening targets/checks.
5. Separately report local mathematics, unclosed obligations, machine checks, independent semantic review, author-confirmation/trust state, and remote integration. Distinguish actual execution, this isolated probe, and untested fault paths.

## Rework or extra gates this does not require

- Do not require complex Hermitian extension, physical quotient positivity, all of F06, the 17 numbered results, or the whole paper to close before integrating this accurately labeled development result.
- Do not reread the whole paper, repeat all scope audits, or redo applicable local independent readback merely because documentation/registration or the head SHA changes. Whole-paper scope issues still require resolution for final certification, but are not new prerequisites for this local development merge.
- Do not use `human_semantic_confirmation=pending` or an undecided final trust policy as a reason to request user approval again for every routine development merge. Retain pending accurately: agent review, compilation, and merging do not create human confirmation or support a whole-paper verified label. Later changes of mathematical meaning, added assumptions, or expanded confirmation scope require the corresponding item-specific decision.
- Do not demand mathlib-submission generality, separate paper-result registration of every auxiliary lemma, a fixed agent quota, or a duplicate ledger. The separate audits of 12 targets and 29 public declarations are already explained.
- Do not add a second-GitHub-account Approve gate or treat same-account agent reports as another account's approval. Retain the established single-account PR/CI and independent-review arrangement.
- Do not modify the locked paper, upgrade dependencies, repeat unrelated maintenance negative suites, delete failed records, relax trust, remove targets, or skip checks to obtain green status.

## Snapshot binding

These SHA256 values were actually read by this probe. Later progress does not rewrite the probe as having passed at that time.

| Input | SHA256 |
| --- | --- |
| `AGENTS.md` | `ac50deefc592397a8e2d502f9bf853b741d1d9463ad424428c69a708833c5279` |
| `docs/formalization/f06-workflow-test.md` | `a895c7c1a0fa5361edd3f8dc3abe968c1a9f8a5a3e2eb67d6d7c0091a60b9a84` |
| `docs/formalization/scope.json` | `163bca895aa34dd4f9ed28402b9919b2f6def42df4bb29e72b29e4887fdebcdc` |
| `docs/formalization/slices.json` | `ae444bcb40341b135d1a16088f80fc4e309fe072b3ca6f84ab22b7621aa5101e` |
| `docs/formalization/slices.md` | `9863f2d1b83f7ec573d052e16f7613bbbcea8aa14fda4cc54a4d0c9eda743c14` |
| `Burnett.lean` | `34e6411d204d1577bece4f8cece686fb4cf603770df9118755d2b440ea81c3aa` |
| `Burnett/Algebra/RealPolarization.lean` | `5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4` |
| `docs/statements/real-polarization.md` | `de1ca6bda24b85980fe45968869841696bac314187c83ddd8eeb63ad60d19edc` |
| `docs/statements/real-polarization-review.md` | `fc4f02ad8f5e99e4956b209f6439098fe69d9a6e04edf980277ef059c18c9b8d` |
| `.project-verification/slice-workflow-test/github-config.json` | `9479f7c788b89a1fe60e8f7e360d9d33fc31d6fb8ab93087d1d2d7d6db5012e3` |
| `.project-verification/slice-workflow-test/draft-ci.json` (identical to the read pr-ci) | `f67c183cb5a40fef9643cd348cad6a236f33e9c754539931e21ee318601bc5c2` |
| `.project-verification/slice-workflow-test/central/actual-types-receipt.json` | `4eb035a28887350522cd559c2472b0fdeb261ab764a85a06b6ab83bf734f4ce0` |

The locked paper, frozen copy, 5 direct import sources, toolchain, manifest, lakefile, actual-type query source, and raw log in the independent readback table were also actually checked; all 15 listed inputs matched. “Cannot” in this report is a gate judgment about current evidence, not a finding that the local real-algebra theorem is false, nor a claim of live verification of the current remote state.
