# Lean paper formalization: full result coverage

[Chinese operative skill entry point](SKILL.md)

This is the English reading copy of the version 1.3.1 skill and engineering workflow. It uses the scope, trust policy, and completion requirements of the `paper-results` standard version 1.2. Read the standard first and consult the two-way workflow for the current task. The scope is all formal results and their necessary dependencies. [Standard](references/standard.en.md) · [Two-way workflow](references/workflow.en.md)

## Entry points

- **Start, resume, or revise a proof.** Verify the manuscript version, scope, and actual progress. If relying on prior work or review, check that its evidence applies to current inputs. Assess changes using the two-way workflow.
- **Create or integrate a GitHub project.** Confirm the repository and existing authorization. Incorporate the repository template and `scripts/check_paper.py` as needed, reusing equivalent configuration. [Engineering guide](references/engineering.en.md)
- **Work in parallel or deliver through a PR.** Organize branches by mathematical deliverable. Integrate code, imports, target registration, and status in the same candidate. Apply independent review and combination checks to the actual proposed merge. Follow the project's agreed visibility, protection, and merge authority. In human merge mode, hand off the ready PR to the human. [Parallel delivery and GitHub merges](references/github-pr.en.md)
- **Set trust policy or draft a completion statement.** Use confirmed project decisions. Keep undecided policy explicitly open. Project instructions take priority over bundled checker settings and records from unrelated projects. [Trust policy](references/trust.en.md)
- **Explain the publication rationale.** Distinguish journal requirements, community examples, and recommendations in this standard. [Sources](references/sources.en.md)

## Scope of work

1. Lock the manuscript version and file hash. List all formal results in the text and appendices, including theorems, propositions, lemmas, corollaries, and important unnumbered assertions stated as independent results.
2. Include the definitions, technical facts, and cited results actually needed for their Lean proofs. Reuse suitable library proofs.
3. Include background, examples, or optional material when it is itself a formal result, is needed by a proof, or is expressly claimed as verified. Ask the user to decide materially ambiguous cases.
4. Construct the Lean declarations and proofs from the paper. Independently read the mathematical content of the actual Lean types and key definitions back against the paper. Check objects, assumptions, quantifiers, dependence of constants, and every conclusion.
5. Use explicit theorem parameters or structure fields for temporary unproved inputs. Mark these as conditional interfaces. Close extra premises using only manuscript assumptions before claiming the original result. A conclusion, global solution, or key estimate supplied by the caller remains an assumption.
6. Alternative proofs are permitted with the same claim and necessary assumptions. When asked to verify a particular proof route, track that route separately from alternative Lean proofs of the same result.
7. Paper-specific Lean code is acceptable. It must build reproducibly, represent the paper accurately, and provide closed proofs under the agreed trust policy. Mathlib's upstream generality, naming, API design, and lint suite are optional here.

## User decisions and collaboration

In a project with bilingual delivery, update the affected Chinese and English explanations in the same PR. Keep one set of Lean sources, targets, and original evidence. Use the actual declarations, locked manuscript, and shared receipts to check mathematical scope, assumptions, and status in both languages. Use a single operative entry point for each workflow specification.

Deliver to the location authorized for the task. A standalone skill or template carries no additional installation, repository, or publication authority. Use existing authorization for the specified remote and proceed with independent local work when a remote is undecided. Present ambiguities or added mathematical assumptions individually, with their consequences. Wait for the user's choice before locking the affected model and proceed on independent tasks.

Divide work by mathematical dependency. Keep responsibility for coupled estimates and bootstrap closure together. Delegate independent ready work with separate write ownership when possible. The coordinator owns essential shared interfaces and final integration. Assign independent reverse review of frozen results to agents who did not construct them. Adjust parallelism to dependencies and integration cost.

For a completion statement, use an independent reading of actual types and important definitions and compare it with the manuscript and forward implementation notes. Independently compare the list of formal results in the locked paper with the current inventory in both directions. Reuse a scope review or author confirmation only when its scope and the corresponding actual meanings still apply. Ask the user or author to confirm new or materially changed meanings or an expanded scope. Record the actual confirmer, scope, and identifiable explanation version. A self-review can support draft work.

Development `main` may include explicitly marked conditional interfaces or results pending author confirmation. Ordinary integration follows the agreed project authorization. The user decides manuscript ambiguities, added assumptions, or changes to conclusions. Record independent agent review separately from GitHub account approval.

A completion statement covers the formal results and their necessary dependencies as defined by the standard. The checker reports `machine-check-passed`. Full completion also requires the trust decision, coverage, semantic correspondence, checks, and applicable version evidence. Report the mathematical result, open interfaces, machine checks, semantic review, and publication status separately. Explain material differences to an author in ordinary mathematical language.
