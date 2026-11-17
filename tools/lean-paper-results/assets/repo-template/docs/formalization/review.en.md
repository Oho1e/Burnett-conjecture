# Formalization review record

[Chinese template](review.md)

Fill out the record for the current project.

## Manuscript and standard

- Actual manuscript version, full-text access, and SHA256 for the source or multi-file inventory.
- Selected standard: `paper-results` 1.2. Record the standard SHA256 in agreement with `scope.json`.
- Inventory of formal results, key unnumbered claims, and necessary definitions and dependencies. Record substantive scope ambiguities and the user's decisions.
- Final trust decision: pending until approved. The bundled checker supports the three usual basic axioms.

## Independent reverse review

Record the reviewer and their independence from implementation.

| Manuscript result | Mathematical reading from actual types and definitions | Differences and resolution | Status |
| --- | --- | --- | --- |
| T1 | Fill in | Review pending | development |

Record the actual confirming user or author, date, scope, identifiable explanation version or location, conclusion, and outstanding items. Confirm a well-defined set together if appropriate. When reusing a prior confirmation, record why it still applies.

## Machine evidence and input binding

Record the actual source, scope, standard, toolchain, and Lake manifest hashes or equivalent fingerprint. Record the actual runtime, target build, transitive axiom audit, and logs. Include separate evidence for standalone definitions and calculations outside target dependency closures.

After a change, record the changed inputs, affected results, pending checks, and the basis for carrying forward existing review or confirmation. Preserve historical evidence and distinguish an outdated receipt from an additional unproved premise.

Record open issues and conditional interfaces.

## Completion statement draft

Suggested wording after all completion conditions are met: All formal mathematical results and their necessary dependencies in this manuscript version have been formalized.

State the coverage boundary for background prose, examples, and optional proof routes. Record fixed paper and code versions, the result inventory, reproduction instructions, and trust policy. Use actual content snapshots and evidence locally, then record actual CI if enabled. A public label binds a fixed paper version and code commit. The record itself does not contain its own commit hash.

Publication status: workspace materials only until an actual publication is recorded.
