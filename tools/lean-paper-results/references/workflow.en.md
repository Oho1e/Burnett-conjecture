# Forward implementation and reverse verification

[Chinese source](workflow.zh-CN.md)

Engineering workflow 1.3.1 uses the scope and completion requirements of `paper-results` 1.2. [Standard](standard.en.md)

```text
Locked paper and result list → project setup → mathematical statements → Lean proofs
          ↑                                                             ↓
          └── compare with the paper ← independent reading ← actual types and definitions
```

Work backward from each goal to its dependencies and implement them in dependency order. Review mathematical correspondence separately.

## 1. Lock the manuscript and inventory its results

At intake, read the main text, appendices, actual sources, and repository instructions. Record the version, SHA256 hashes, Lean toolchain, and dependency lock. Preserve the file list and hashes for a multi-file manuscript. On continuation, reuse applicable intake evidence and read the passages affected by the task or by changes. Fill any gaps in the prior scope review.

Enumerate all formal results and important unnumbered assertions. Judge whether a remark or example is itself a result or a necessary dependency. Describe excluded categories concisely. Present substantial ambiguities to the user with the actual text. Record the standard in the existing `docs/formalization/scope.json` or equivalent.

## 2. Set up or integrate a GitHub paper project

Identify the local project directory, repository owner/name, and visibility. Reuse a suitable project. Work locally if remote operations are outside scope. Proceed with existing authorization. Report missing remote or login details while working on independent tasks.

Use a mathematical module hierarchy, statement documents, pinned dependencies, and CI, as in the reference project. Give the README the paper version, scope, status, build commands, and review links. Statement documents preserve full context and actual Lean types. [Engineering guide](engineering.en.md)

When the manuscript snapshot, entry point, configuration, and accurate status are ready, use the applicable authorization to establish or bind the remote, push the actual version, verify visibility, and observe CI. Record the URL, pinned commit, and run in the existing evidence record. Keep credentials and caches out of the repository. An initialization build is possible before the first proof. Describe its actual scope.

Visibility and protection are project decisions. Check actual platform settings for a PR workflow. Test one important representative result from definitions through proof, review, and build. Keep the final scope at all formal results. [Parallel PR delivery](github-pr.en.md)

## 3. Work backward from results to required interfaces

Identify analytic, geometric, algebraic, and existence results needed by the main and independent results. Check actual signatures in the pinned library. Distinguish reusable formal proofs, bridges to prove, and open external inputs.

Organize modules by mathematical mechanism. Coordinate coupled estimates and bootstrap closure as a common task. A priori estimates for a given solution use only the needed theory. A claimed existence result requires its local theory, continuation, and other proof dependencies to be accounted for.

## 4. Construct declarations and proofs

Record the manuscript locator, full mathematical statement, Lean name and actual type, and sources of technical conditions. Check:

- Objects, measures, norms, boundary directions, signs, and solution concepts.
- Quantifier order, dependence of constants, and uniformity in time and parameters.
- Regularity, integrability, finiteness, support, endpoints, and instance parameters.
- All existence, uniqueness, continuous dependence, and decay conclusions stated by the paper.

Present materially ambiguous conditions such as “sufficiently smooth” to the user before locking their formal model. Continue independent work. Use explicit conditional interfaces where necessary, with consumers and remaining obligations. Close added premises from manuscript assumptions before claiming the original result. A theorem that assumes the required conclusion or estimate is a conditional derivation even if its axiom audit passes.

Reuse library proofs and alternative arguments. Keep every formal lemma in scope even if an alternative argument no longer uses it. Parallelize ready tasks with exclusive write ownership and separate outputs. The coordinator stabilizes essential shared interfaces and integrates the scope, target registry, and shared build. Assign frozen results for independent review as they become ready. Serialize the final merge window and keep responsibility for coupled obligations together.

## 5. Independently read the formalization back against the paper

Have a reviewer derive the mathematical meaning from actual Lean types and key definitions before comparing with the paper and forward notes. Consult the paper's notation as needed. Examine implicit and section parameters, typeclasses, and structure fields.

Check for smooth solutions used in place of weak solutions, finite time in place of global time, constants chosen separately for each time, almost-everywhere conclusions in place of pointwise ones, and defaults for total derivatives or integrals. Test consistency of new hypothesis bundles on relevant data. The zero solution alone gives little evidence on the intended nonzero-data model.

Independently inventory formal results from the locked paper and appendix, then compare both ways with the existing inventory. Record omissions, unmatched entries, and proof ownership for grouped mappings. Reuse older inventories after verifying the manuscript version and coverage and checking that current mappings retain the results. Target any review gaps. Ask the user or paper author to confirm the mathematical interpretation and record the scope, identifiable explanation version, and items still pending. Confirmation can cover a well-defined set in one decision.

## 6. Verify the machine results and record completion evidence

Build registered targets and required modules. Audit their transitive axioms. Check definitions and standalone calculations outside target dependencies by examining their actual implementations and dependencies. Compilation of an entry import alone leaves such checks to the project. Record coverage, trust, and semantic review independently of machine status. [Review template](../assets/repo-template/docs/formalization/review.en.md)

Bind semantic evidence to the manuscript, implementation, inventory, toolchain, and dependencies using hashes or equivalent version records. Keep reproducible local content snapshots and actual run evidence. Record CI and releases by actual run and fixed commit. An evidence file cannot contain the hash of the commit that includes it.

### Evidence after changes

Compare applicable bindings and assess the effects of the actual changes. A changed hash locates a change. Preserve history and mark affected evidence as applicable to its old inputs when appropriate.

- For material changes to a statement, essential definition, paper claim, or mathematical interpretation, review the affected results and interfaces. Consider actual types, definitions, instances, implicit parameters, notation, and conventions. If the impact is unclear, isolate the issue and continue independent work.
- For proof-only edits, retain prior semantic review and author confirmation when actual types, essential definitions, and meaning are verified unchanged and trust still matches. Refresh the relevant build, axiom audit, and input binding.
- For wording or layout edits with the same meaning, scope, and implementation, update the record. For a toolchain or dependency change, recreate relevant machine evidence under the pin and check implications for interpretation. Dependency upgrades require applicable project authorization.
- If old evidence lacks usable bindings, look for the actual versions, source records, a local reproduction, or focused independent review. Record remaining evidence gaps and continue implementation and review. Use only applicable evidence for final claims.
- Carry forward author confirmation when the actual meaning and scope match. Ask the author only about new or changed mathematical interpretations or additional scope. When the applicability is uncertain, check the prior record.

Use the existing inventory or review for definition coverage and additional query locations. Deliver locally or remotely as authorized. A remote or PR can precede mathematical completion. The final verification label requires all completion conditions. Preserve old-version facts and record new versions and applicable evidence.

## 7. Integrate through a PR and verify the main branch

Bind work, review, and checks to the actual candidate. Verify its combination with latest `main`. In human-merge mode hand off a ready PR, then verify actual push CI after the merge when observed or on an authorized continuation. If main CI fails, investigate and fix the failure before further merges. Independent implementation can continue. Record PR readiness, merge, main CI, and whole-paper status separately. [PR workflow](github-pr.en.md)
