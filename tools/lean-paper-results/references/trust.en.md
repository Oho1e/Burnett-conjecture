# Trust policy and pending decisions

[Chinese source](trust.zh-CN.md)

Record the project's trust decision before making a final claim. Use the current instructions and project record. Saving a standard, copying a template, and running a checker do not select a trust policy. While the decision is pending, modeling, proofs, conditional interfaces, and checks may continue. Decisions from other projects do not apply automatically.

| Option | Meaning |
| --- | --- |
| A: closed mathematical dependencies | Every needed fact has a formal proof in the pinned library or the project. Alternative proofs are allowed. The final result follows from the manuscript's assumptions. |
| B: explicit literature premises | A result without a formal proof can temporarily be passed as a parameter. The proved conclusion is conditional on that premise. |

Reuse existing mathlib results. Preserve genuine manuscript hypotheses and distinguish them from cited lemmas used in the proof. For a paper claim `H → G` with an unformalized prerequisite `L`, the parameterized result `L → (H → G)` may pass an axiom audit while leaving `L` unproved. Review statement correspondence and close the dependencies separately.

For a global existence result, account for local well-posedness and continuation under the final policy. A priori estimates for a given solution only require existence results actually used or claimed by the paper.

`paper-results` 1.2 recommends closed dependencies for completion and permits B-style interfaces during development. A final result retaining B premises must be described as conditional and requires a separate standard if it is to carry a different completion label.

The checker supports three basic axioms: `propext`, `Classical.choice`, and `Quot.sound`. They provide general logical foundations. Using the checker does not establish that the author approved its policy. Native evaluation such as `native_decide` changes computational trust independently of unformalized mathematical assumptions. If needed, explain its specific dependencies and alternatives, then test the adjusted checker. [Lean axioms](https://lean-lang.org/doc/reference/latest/Axioms/) · [Proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

The recorded skill release made no trust extension, personal skill installation, or remote publication.
