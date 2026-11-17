# Clarification of F06 report wording (2026-11-16)

[Chinese original](f06-report-clarification.md)

The original test report, API receipts, and verification inventory retain their historical bytes. The following clarification does not rewrite historical runs, commit identifiers, or mathematical results.

1. The report's “protection remained effective” should be read precisely as follows: main CI success was observed after merging, and administrator enforcement, strictness, and the specified check list were read back. The old observer used only the first two booleans to form protection_active; that receipt did not compare every field of this project's complete protection policy. This does not prove the full policy was unchanged, nor show that live protection actually failed. Version 1.3.1 compares current readback with explicitly expected project fields rather than replacing them with a simplified boolean.
2. “The workflow may continue to the next similar deliverable” was conditional practical advice. The round supplies feasibility evidence for subsequent supervised local deliverables of the same kind with ready dependencies, retaining coordinated integration, independent review, and actual candidate binding. It did not prove that the process is self-sufficient, covers every fault, or makes all of F06 reliable.
3. “A bad-target regression verifies that source is not omitted” requires direct snapshot assertions. Lean's rejection of a bad target does not establish that its source file was included in the fingerprint. Version 1.3.1 separately checks actual source sets, valid content changes, during-run stability, and the original compilation/axiom rejection stages.

See the [maintenance 1.3.1 description](maintenance-1.3.1.en.md) for this round's tool maintenance and boundary at a reviewable PR. This wording clarification changes neither F06's real mixed mathematical deliverable, two actual successful CI runs, local user delegation, nor the still-open complex Hermitian/quotient-positivity/whole-paper scope.
