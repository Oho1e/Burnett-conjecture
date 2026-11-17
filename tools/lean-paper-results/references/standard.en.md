# paper-results: standard version 1.2

[Chinese original](standard.zh-CN.md)

This English reading copy describes the same standard. Use the approved source document and its actual SHA256 for each project binding.

Saved on 2026-11-15. This standard is an independent working scheme for formalizing a paper intended for submission. It is not a certification rule issued by a journal or by Lean. It does not supersede the stricter whole-text version saved separately.

## Coverage

| Object | Requirement under this standard |
| --- | --- |
| Theorems, propositions, lemmas, and corollaries in the main text and appendices | Include all of them; do not automatically exclude a result because the main theorem does not use it. |
| Key unnumbered mathematical assertions stated as independent results | Include them; leaving a difficult assertion unnumbered must not evade coverage. |
| Definitions, technical facts, and cited results needed by the above results | Represent them accurately and include them in the proof dependencies; existing formal proofs may be reused. |
| Expansions, substitutions, rearrangements, and routine calculations within proofs | Carry them out in actual Lean proof blocks; a separate theorem for every line is unnecessary. |
| Background facts, examples, counterexamples, and remarks | Include them if they are formal results, actual dependencies, or explicitly claimed to have been verified; otherwise they do not automatically become verification targets. |
| Historical narrative, motivation, physical interpretation, and incidental discussion unrelated to the targets | Apply normal scholarly quality checks; do not automatically create formalization tasks. |
| An optional alternative proof route | It may be omitted from formalization; do not claim that the omitted route has therefore been verified. |
| Conjectures and open questions explicitly identified in the paper | Preserve their stated epistemic status rather than presenting them as proved. Refer ambiguity about their relation to the deliverable statement to the author. |

A “formal result” is determined by the mathematical assertion it makes in the paper, not merely by the name of its environment. If it is unclear whether a remark contains an independent contribution, present the source passage and reasons for the user to decide. Do not downgrade a result to explanatory material merely to reduce the workload.

Check the inventory of formal results item by item against the source; do not reconstruct it from the repository's existing theorem list. Repeated statements of the same result may be consolidated. Dependencies, special cases, and corollaries must have identifiable, checkable Lean proof ownership.

## Four independent dimensions

| Dimension | Choice in this version |
| --- | --- |
| Coverage | All formal mathematical results and necessary dependencies, rather than every mathematical sentence in the whole text. |
| Proof route | Verify the propositions; alternative proofs are allowed. Certification of every route in the paper is not the default. |
| Mathematical and computational trust | Closing all dependencies is the recommended completion goal. The project records determine the specific trust decision; the current tooling implements only the standard three-axiom configuration. |
| Engineering quality and confirmation | Reproducible code specialized to the paper; mathlib submission quality is not required by default. Independent agent review is followed by user/author confirmation. |

Selecting this version does not automatically approve an undecided extension of trust, authorize changes to the paper, install a skill, or publish anything remotely.

## Completion and progress

- `development`: definitions, proofs, or the correspondence with the paper remain in progress.
- `conditional`: a formal derivation exists, but additional unproved mathematical premises or unresolved interpretive issues remain.
- `verified`: all formal results and dependencies are closed under the confirmed policy, semantic differences are resolved, and actual machine evidence, independent review, and author confirmation are complete.

While a project's final trust policy is undecided, tools and proofs may continue to be used, but completion statements must not say that the user has accepted that configuration. Follow an explicit project choice directly; pending wording in a template or another conversation does not override it. If the final deliverable retains unformalized literature premises, it may receive only an explicit conditional statement. Save the corresponding standard separately or revise it through a user decision; do not silently retain the wording for closed completion.

This version does not issue a completion label for the whole scheme when only the main theorem is complete. Partial completion may be reported precisely as progress. When a missing formal result is discovered, continue repairing it or record the obstacle; do not automatically remove it from the inventory.

## Deliverable statement and label

Once every condition is met, the statement may read:

> All theorems, propositions, lemmas, and corollaries in this version of the paper, together with the key unnumbered results listed in the inventory, have been formalized in Lean 4. The accompanying code repository records the correspondence with the paper, trust statement, pinned versions, and reproduction method.

Example label: `Lean verified — all formal results`. Link the fixed paper version, fixed code commit, and complete correspondence inventory. Avoid saying only that “everything in the entire paper has been verified,” because this standard does not by default cover unrelated discussion or all optional proofs.

This is a scope statement made by the project itself. It does not mean that a general mathematical physics journal independently reviewed all the code. A green build badge on the default branch reports only the mechanical checking status.

## Version binding

The project manifest must record `standard.id: paper-results`, `standard.version: "1.2"`, and the actual SHA256 of this standard document. Titles, templates, and the project manifest must use the same version number; do not use version 1 to denote this revision.

Version 1.2 retains the mathematical coverage and completion goal of version 1.1, clarifies incremental review, inherited confirmation, and GitHub project integration, and strengthens attribution of failure reasons in maintenance tests. Substantive changes to the requirements require a separately saved version. Switching an existing paper project to another version requires an explicit user decision and a record of the impact. Publishing this version does not automatically change the requirements of other standards.
