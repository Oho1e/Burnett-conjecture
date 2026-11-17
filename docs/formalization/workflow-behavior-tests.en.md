# Independent simulated behavior tests of skill v1.3

[Chinese original](workflow-behavior-tests.md)

Test date: 2026-11-15. The subject was `lean-paper-results/SKILL.md` and the references read as needed below. Engineering workflow version was 1.3; the mathematical standard remained `paper-results` 1.2.

This report contains seven simulated decisions, not verification of an actual paper, PR, or CI. It only read skill files and wrote this report. It accessed no network, operated no real Git/repository, ran no Lean, changed no trust policy, and did not confirm for a real author. “May merge” means engineering integration under existing project authorization after its conditions are met. “May certify” concerns the standard's whole-paper `verified` completion statement, not official certification.

## Reference index

- **S**: [SKILL.md](../../tools/lean-paper-results/SKILL.en.md), especially L14–15 (registration with delivery, project authorization/trust), L30 (existing authorization and mathematical-condition decisions), L34–38 (independent review, inherited confirmation, development merging, completion).
- **R**: [standard.zh-CN.md](../../tools/lean-paper-results/references/standard.en.md), L9–20 (scope from the paper), L35–41 (development/conditional/verified), L49–51 (fixed versions and green badges).
- **W**: [workflow.zh-CN.md](../../tools/lean-paper-results/references/workflow.en.md), L23–31 (local/remote authorization), L58–70 (independent reverse review, scope/machine evidence), L74–80 (change impact/inherited confirmation), L88 (latest combined/main CI).
- **P**: [github-pr.zh-CN.md](../../tools/lean-paper-results/references/github-pr.en.md), L7–9 (authorization/actual protection), L19–23 (same-candidate registration/checking capability), L27–31 (incremental review/latest combination/check coverage), L35–45 (merge window/final-main CI/development states), L49 (account approval).
- **E**: [engineering.zh-CN.md](../../tools/lean-paper-results/references/engineering.en.md), L29–33 (remote authorization/local checks), L54–59 (targets/inventories/build coverage), L63–73 (checker capability/actual execution/version evidence).
- **T**: [trust.zh-CN.md](../../tools/lean-paper-results/references/trust.en.md), L3 (project decisions/pending), L20–24 (conditional deliverables/three-axiom configuration/trust extensions).

Key passages include: P L45 permits accurately labeled conditional interfaces or pending author confirmation on the development main line; P L21 disallows merging code first and postponing registration to a cleanup PR; P L31 disallows accepting weakened checking merely because a PR is green; W L77 allows verified proof-only changes to inherit semantic conclusions/author confirmation; P L49 distinguishes independent agent review from GitHub Approve. The decisions below apply these operational rules rather than treating a public example as authorization for another project.

## A: Publication and merging authorized; two supporting lemmas checked; author/trust pending

**Actual next step.** The coordinator checks the two lemmas' deliverable scope, library entry point/necessary registration, input bindings of existing independent review, and whether the stated successful CI actually covers the merge candidate on latest main. Retain “author confirmation pending; trust policy pending” accurately. If routine checks hold and no genuine unresolved mathematical objection remains, perform the already authorized merge, observe push CI for the final main commit, and then report integration complete. Both lemmas may form one consumable mathematical deliverable: no mechanical one-lemma-per-PR rule or wait for whole-paper completion is needed.

**Merging and certification.** A development merge may proceed. The two pending states alone neither block routine merging nor require repeated publication/merge permission. Whole-paper `verified` cannot be claimed: all-result coverage is unspecified, and trust choice/author confirmation are incomplete. Candidate-CI success reports only its actual machine-checking scope. Pending alone does not imply an additional unproved mathematical premise, so do not automatically label every result `conditional`; separately report proofs, unproved interfaces, machine evidence, semantics, confirmation, and publication.

**Decision authority.** The coordinator executes authorized engineering integration. The user chooses final project trust; the user or author actually confirms the plain mathematical explanation. If pending conceals ambiguity, added assumptions, or a changed conclusion, that item first needs a user decision rather than bypass as “ordinary pending.”

**Review scope.** Both lemmas, necessary definitions/dependencies, affected consumers, registration, and the current combination. A local merge does not force a repeated whole-paper semantic audit. A whole-paper completion statement still requires independent scope review, closure of all results, and remaining completion evidence.

**References.** S L30, L34–38; R L35–41; T L3, L20–22; P L13, L21, L35–45.

## B: Project B authorizes only local formalization; the skill includes project A's public example

**Actual next step.** Continue B's local source locking, result inventory, proofs, independent review, and reproduction under B's own rules/trust decisions. Do not create a remote repository, push, publish, change visibility, or copy A's owner/name, publication permission, or pending states into B's decisions. The example may inform engineering organization.

**Merging and certification.** Remote PR merging is unauthorized. Local work/integration may continue under B's authorization. Lack of remote authorization alone does not prevent a future accurate local completion statement, but the scenario provides no closure, coverage, or confirmation evidence, so certification is unavailable now. If remote publication later becomes necessary, first prepare concrete reviewable files/scope and obtain the corresponding authorization. Current local work need not await an unrequested remote task.

**Decision authority.** The user chooses B's remote target, visibility, and distribution scope; the coordinator performs authorized local work. Reuse B's explicit trust policy rather than resetting it to pending from the skill's historical ending.

**Review scope.** B's locked paper, inventory, implementation, and pinned local environment. A's example supplies neither mathematical evidence nor authorization for B.

**References.** S L13–15, L30; W L23–31, L84; P L3, L7; E L7, L29–31, L73; T L3.

## C: Main changes a shared measure definition after review; PR head unchanged; old CI green

**Actual next step.** Retain old review/CI as facts about the old snapshot. Refresh the combined candidate against latest main and inspect the measure-definition change. Identify affected actual types, definition expansions, instances, implicit parameters, notation/conventions, and consumers, then renew relevant independent semantic and machine checks. If impact is unclear, record concrete doubts and investigate first while independent work continues.

**Merging and certification.** Unchanged head plus old green status cannot justify merging or certification of the new combination. After the latest combination passes applicable checks and objections are resolved, merge under original authorization and confirm final-main CI. Pending revalidation of evidence applicability does not automatically change the original mathematical status to `conditional`.

**Decision authority.** The coordinator organizes refresh/impact identification; an independent reviewer checks affected meaning. Submit only new or materially changed mathematical meaning for user/author confirmation. If the explanation is verified unchanged and earlier confirmation covers it, inherit confirmation without asking again about the whole paper.

**Review scope.** The shared measure definition, affected results, and related interfaces. Impact may extend beyond direct dependencies visible in textual signatures or an axiom graph, but does not automatically require whole-paper rereview. Update candidate base/head, key definitions, and machine/semantic bindings.

**References.** W L70, L74–80; P L27–29, L35, L41–43.

## D: A new theorem is absent from the library entry point and stated scope.targets; the other nine targets are green

**Actual next step.** Determine from its paper role and actual dependencies whether the new theorem is an independent paper result, necessary auxiliary declaration, or explicitly unrelated exploration. For a new formal result in this deliverable, put code, effective import/build entry, accurate registration, and scope explanation in the same merge candidate, then run actual build/target/transitive-axiom checks covering it and independent reverse review. Do not merge code first and defer registration to a cleanup PR.

**Merging and certification.** Under the natural reading as a new paper result, the current candidate is unacceptable: nine green targets do not cover the tenth. A genuinely auxiliary declaration need not be a separate final target, but actual inclusion in a reviewed target's dependency closure or equivalent direct/dependency checking still needs evidence. The scenario supplies none, so coverage cannot be inferred. Any uncovered formal result prevents whole-paper completion; deleting a target cannot repair that.

**Decision authority.** The coordinator integrates central imports, targets, and scope in one candidate; independent review checks correspondence. Refer substantive ambiguity in the paper role to the user. An explicit formal result cannot be downgraded by an agent. New mathematical explanation outside earlier confirmation scope needs user/author confirmation.

**Review scope.** The new result/dependencies, related consumers, inventory-to-paper correspondence, and combined checking of nine old targets plus this deliverable. Verified unchanged semantic evidence for old targets may be reused rather than mechanically rereviewed.

**References.** R L9–20, L41; S L14, L22; P L21, L27, L31; E L54–59, L63, L67; W L62, L80.

## E: All agents share Oho1e, but a GitHub Approve is proposed as mandatory

**Actual next step.** Check the PR-author account and actual project requirements. If Oho1e authored the PR, multiple agents cannot use that same account to approve their own PR. Do not fabricate another account's approval or call an independent report GitHub Approve. For an unadopted design, use feasible PR/required-CI/independent-mathematical-review records rather than adding an unsatisfiable second-account gate.

**Merging and certification.** If one Approve is already an explicit project requirement or active platform gate, it cannot be bypassed before fulfillment or an authorized change decision. If merely a new agent suggestion, correct it and proceed under actual rules/original merge authorization. An unmet account gate is not a mathematical error; conversely, Approve replaces none of author confirmation, independent semantics, machine evidence, or whole-paper coverage and cannot justify certification.

**Decision authority.** The coordinator may correct their own unadopted infeasible suggestion. A user/authorized project owner decides changes to established approval requirements; agents cannot override them automatically. Only a genuinely different account reviewer can supply that actual platform approval. Independent agents continue separately identified mathematical review.

**Review scope.** Account identities, PR author, actual rules/required checks, and role records; no unrelated mathematical audit needs repeating.

**References.** S L36; P L9, L35, L49. This judges the skill text without live GitHub verification.

## F: Proof-only change; types, definitions, explanation, trust configuration checked unchanged; original author confirmation covers the target

**Actual next step.** Record applicability checks supplied by the scenario and the original confirmation scope/explanation version. Refresh affected builds, transitive-axiom audits, and implementation-input bindings. Obtain actual latest-main combined CI, merge under authorization, and confirm final-main CI. Independent semantic conclusions and author confirmation may be inherited without asking the author again or requiring whole-paper semantic rereview.

**Merging and certification.** The incremental machine checks and routine merge checks suffice for merging. A proof-only change does not by itself invalidate existing whole-paper completion, but the scenario also does not establish that the whole paper was previously verified. Continue a completion statement at an updated fixed version only if the old whole-paper evidence remains applicable and all other conditions hold. If trust remains pending as in A, F's “unchanged trust configuration” does not mean “confirmed policy” or add certification eligibility.

**Decision authority.** The coordinator/reviewer checks actual changes and record applicability and executes existing authorization; the author need not repeat the same mathematical decision. If later checking disproves the scenario's premises, extends trust, or changes meaning, refer only actual changes to the user/author.

**Review scope.** This proof implementation, affected builds/axioms, environment, and combined candidate. Semantic checking establishes the facts of “unchanged and covered,” without recreating every natural-language explanation.

**References.** S L34; W L74, L77, L80; P L27, L29, L41–43; T L3, L22–24.

## G: The same PR replaces actual Lean/axiom project-check with echo successful, yet remains green

**Actual next step.** Reject merging the candidate as it stands, identifying removed checking capability as the cause of green status. Revert the weakening and restore actual build, target existence/provenance, and transitive-axiom audit, or supply reviewed and actually equivalent checks. Inspect the workflow, invoked scripts, target inventory, and execution conditions to establish that the displayed job actually runs these checks on the actual candidate rather than retaining only its name/status.

**Merging and certification.** This permissive candidate cannot merge, be called `machine-check-passed`, or support certification. A retained job name, GitHub Actions provider, and green status describe a status context rather than prove Lean/axiom auditing occurred. The change affects checking capability and cannot evade review by saying engineering-configuration PRs need no mathematical reverse review. Merge authorization does not authorize hollowing out required checks.

**Required evidence.** At minimum: a reviewable restoration/equivalent-check diff; pinned toolchain, dependencies, paper/inventory, and actual code versions; latest main/base, PR head, and actual combined candidate; full commands/exit states and matching logs, actual type/axiom output, and generated results for the build and precise target audit; evidence of coverage of the current deliverable without reduced targets; identifiable actual CI runs/artifacts. Old-version artifacts or echo output cannot fill these fields. Changed checking capability needs targeted effectiveness validation—for example, isolated maintenance tests showing expected bad targets/disallowed axioms fail at the intended stage with the corresponding diagnostic, rather than counting any failure as effective auditing. This simulation runs no such tests. After the repaired candidate passes, final-main CI still needs confirmation.

**Decision authority.** The coordinator/engineering reviewer repairs and verifies checking capability. Unchanged mathematical explanations do not need repeated author confirmation. A genuine proposal to lower project checks, trust, or completion standards requires a specific user decision and accurately relabeled delivery status; a same-named green check cannot silently implement it while retaining full-verification wording.

**Review scope.** Workflow, invoked checkers, relevant conditions/skipped paths, exact target registration, and actual candidate coverage. Applicable semantic conclusions may be reused if mathematical inputs are unchanged. An engineering change does not automatically require whole-paper mathematical rereview.

**References.** P L23, L31, L35, L41; E L63–75; W L66–70; R L37, L51; S L38.

## Real ambiguities not settled by the scenarios

1. **Depth of A's “checked.”** It does not specify independent readback of actual types/important definitions by a nonconstructor, as required by the skill, versus self-review/compilation only. The report assumes the former for its development-merge path. Before real execution, inspect existing evidence and supply only missing parts. One agent's self-review is not independent review. Genuine unresolved objections are also unspecified.
2. **Freshness of A's candidate.** “Candidate CI succeeded” does not identify base/head, checkout method, or coverage, so the next step verifies those facts. C explicitly changes main, preventing reuse of old success for a new candidate.
3. **D's theorem role/configuration field.** Theorem syntax alone does not determine separate final-target registration; its paper role and dependency closure do. `scope.targets` is treated as generic target-registration wording and implemented through the existing equivalent schema's `targets`, not by creating another inventory. A library entry point is not the only possible explicit equivalent build evidence, but none is supplied.
4. **Authority of E's plan and PR authorship.** An unadopted agent proposal, explicit user project requirement, and active platform gate differ. The skill does not automatically override existing requirements. If Oho1e did not author the PR, same-account platform approval may have a different answer; verify rather than invent another account.
5. **Whether F is independent or follows A.** It does not say trust was confirmed or the whole project completed. The scenario-covered semantics/author confirmation can be inherited unconditionally, but certification remains conditional. “Configuration unchanged” differs from “policy confirmed by the user.”
6. **Meaning of certification.** The skill issues no official certification. This report uses only its `verified` state and accurately scoped project deliverable statement; it does not supply a real paper's confirmation or label.

These are primarily missing simulated inputs requiring real records. No irreconcilable rule conflict was found across the seven cases in the read skill. In particular, “development merges may retain pending” and “whole-paper completion requires all confirmations” govern engineering integration and completion statements respectively, without contradiction.

## Read-file snapshots

SHA256 values of files read, locating the decision basis without asserting that an actual paper/project was verified:

| File (relative to lean-paper-results) | SHA256 |
| --- | --- |
| `SKILL.md` | `78C0D23D7B80A30405FFFAF2D624101F5DDE021B6FA0D819A041FEDFDAE9A811` |
| `references/standard.zh-CN.md` | `8CAAD6C9439A86C17567C84BCC065C24A44E11830657FF9996BB13F259CAE2F0` |
| `references/workflow.zh-CN.md` | `D4AE2D10B85CA3CCC0845375BCC1A2E68BE708D624116960F3F88B1553BA2B6F` |
| `references/github-pr.zh-CN.md` | `8F00F5178A83E46109D6D60C70C1887A2A7B3EED9747A992B68A4A6018B8D4D1` |
| `references/engineering.zh-CN.md` | `7008A9708354F96FADFA27AC0B2EB599050CF5592A372C1C40933613C8462951` |
| `references/trust.zh-CN.md` | `594878A86BFE0EC5C2EBCC72740CB95D3E72832B5C1E6D7229EBCCF93875A7ED` |
