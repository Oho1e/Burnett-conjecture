# Review of skill and engineering workflow version 1.3

[Chinese original](workflow-review.md)

Date: 2026-11-15. The mathematical standard remains paper-results 1.2. This task made the project public, revised parallel/PR workflows, and performed independent adversarial review. It added no Lean mathematical proof, changed no trust decision, and supplied no missing author confirmation.

## Actual visibility and protection operations

An independent agent read all 8 pre-publication commits, 97 historical blobs, and metadata. No high-confidence credential, private key, sensitive configuration, or unrelated private material was found. Tracked absolute paths were project SDK and reproduction-command paths. Pattern scanning cannot guarantee the absence of all sensitive content, but no concrete issue requiring suspension of publication was found.

After explicit user authorization, the GitHub API changed Oho1e/Burnett-conjecture to public and read back main protection, the GitHub Actions source constraint, and squash settings. See the [settings record](github-settings.json) for actual fields. Public visibility does not mean whole-paper mathematical verification passed; private-stage records retain their historical facts.

## Local machine evidence

- The new skill directory and in-project snapshot passed the official skill-creator quick_validate. Existing isolated workspace PyYAML was reused; no personal skill or global dependency was installed.
- Project check_project actually passed: the full Burnett library built, and provenance, actual declarations, and transitive axioms of 9 current targets were audited. The result remained machine-check-passed, with paper_formalization_verified false.
- check_slices actually passed, as did 17 slice/work-packet tests. The 46 slices, 135 links, 74 inventory locations, and mapping of 17 numbered results were unchanged.
- Paper bytes, Lean source, toolchain, dependency lock, checker, mathematical standard, and trust document were unchanged. Scope updated only engineering visibility/workflow information; mathematical states and pending issues were not upgraded.
- CI added only main's push filter and checkout without persisted credentials. pull_request continued checking the default merge candidate, retaining the slice, full-project, and target-audit steps. No pull_request_target or write-permission credentials were introduced to execute code under review.

## Adversarial review and scenario tests

Two agents uninvolved in the changes separately reviewed authorization/semantic boundaries and engineering diff/hash consistency; neither found a blocker. The engineering review requested completion of the round's conclusions and input bindings, now supplied. The wording review recommended tightening “documentation-only or engineering PRs merely state that mathematics is unchanged.” It was changed to checking actual impact: no unrelated reverse review when mathematical semantics are unaffected, but relevant review remains necessary for changes to checking capability, scope, or mathematical explanations.

An independent execution agent used the actual skill on seven simulated scenarios: a development merge with pending states, publication authorization for a different project, changes to shared definitions on main, unregistered new targets, same-account approval, inherited confirmation after a proof-only change, and a same-named CI job changed into a no-op. The coordinator checked the results individually; all retained the required boundaries. See the [scenario report](workflow-behavior-tests.en.md) for complete judgments and hashes of read inputs. Target roles, verified depth, and confirmation scope unspecified by a scenario were left pending rather than invented as satisfied.

Platform readbacks, document review, simulated behavior, and actual PR/CI runs are recorded separately. These seven are simulated decision tests, not seven actual GitHub rejections. Direct-push/force-push rejection was not tested, and no genuine author confirmation was impersonated. The results cannot justify whole-paper mathematical certification.

## Version binding

Skill/engineering workflow 1.3 and mathematical standard 1.2 are recorded separately. The standard SHA256 remains 8caad6c9439a86c17567c84bcc065c24a44e11830657ff9996bb13f259cae2f0; the paper SHA256 remains e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e. Key deliverable inputs are separately bound in [workflow input hashes](workflow-inputs.json). A new commit identifier containing this file itself is not recorded within the repository.

Actual PRs, tested heads/combined candidates, squash commits, and post-merge CI are determined by the corresponding GitHub runs and PR records. Post-merge evidence will not create circular commits merely to insert the same file's own SHA.
