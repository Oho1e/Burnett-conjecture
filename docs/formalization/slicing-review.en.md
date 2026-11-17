# Independent review and revision of whole-paper slices

[Chinese original](slicing-review.md)

Review date: 2026-11-15. Conclusion: retain the 46-slice partition. After the interface-contract and relation corrections below, it remains usable as the working graph for slice-by-slice formalization. The 17 numbered results, 2 user-approved unnumbered targets, and 70 inventory entries are retained. No Lean proof was added or completed.

## Inputs and independence

The baseline was commit `3d8c3ed30ac093aa501f75148e77f8c8e25901b9`; the initial slice-manifest SHA256 was `23da770656c0d46903b122050fd8fdf50c811ef5950410216b653556b9c13a53`. The locked paper is `paper/burnett.tex`, 3475 lines, SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`.

Three fresh-context agents uninvolved in constructing the original slices independently read the paper before comparing the inventory. They did not substitute the preceding draft or review conclusions for their judgment:

| Reviewer | Full reading range | Responsibility |
| --- | --- | --- |
| `slice_review_foundations_fresh` | 1–1591 | F/A boundaries, contracts, and all incoming/outgoing edges; supplementary reading of actual consumers |
| `slice_review_interfaces_fresh` | 1592–3115 | P/V/C/L contracts, cross-slice producers, joint closure, and parameter consistency; supplementary reading of earlier interfaces |
| `slice_review_appendix_coverage_fresh` | 3116–3475 | Formal/unnumbered appendix assertions, scope decisions, tool dependencies, and item-by-item location checks across the paper |

After reaching independent conclusions, the agents exchanged objections. Another agent checked the phase-gap counterexample; A01's energy conclusion was distinguished from an independent whole-space operator norm; and initial inventory history was separated from later scope decisions. After repair, each agent checked only their assigned changes, without presenting confirmatory review as a new proof audit of the entire paper.

## Findings, evidence, and repairs

| ID | Finding and consequence | Repair and confirmation |
| --- | --- | --- |
| SR1 | The A04 phase-gap summary stated only low/high frequency separation, omitting the angular-far support in original lines 921–926 and 1006–1014. A literal implementation would yield a false stronger proposition. V10 already had the actual far condition; no misuse by an existing consumer was found. | State the angular-far low-p piece `L_p(1−N_p)≠0`, the thin cones for three frequencies, and the exact signed phase explicitly. The paper was unchanged. Two agents independently checked the counterexample and repair. |
| SR2 | A01→A04 consumes only the compact Lorentz family and conventions at 530–537; V04→V05 consumes only the test/IR specifications at 2019–2035. Labeling these proof-input would make definition work wait for the entire energy/variational proof. | Change both edges to definition, retaining shared conventions and frozen errors assigned to A03/C01. No mathematical obligation was removed. |
| SR3 | A01's output did not provide P01's required whole-space Calderón operator norm. Although original line 589 has an auxiliary commutator bound, the properly-supported energy lemma alone cannot replace the nonlocal Fourier interface at 1674–1684. | Remove the internal A01→P01 proof edge and corresponding overview arrow. Assign the exact L² requirement for fixed Π∂b with gradient-only `‖∂f‖∞` control to the open P01/EXT-COMM interface, instantiated by P01 itself. Add no global bound on f or second-derivative condition. |
| SR4 | Approved X03/X06 were mandatory in scope, but the initial source-index still called them candidates outside acceptance scope. | Append both user approval and original candidate status, linked to the same scope decision. purpose/intake_status remain the original intake history; historical activity and unproved status were not rewritten. |
| SR5 | Single-slice packets omitted their entries from the shared external-interface table. For example, L01's lifting, measure, and geometry duties were only hinted at indirectly. | Export external interfaces by consumer, preserving pending states and shared-record paths. Add regression coverage for external interfaces and exact source passages of P01/L01/X03/X06. |
| SR6 | The external table omitted X02's Rellich/H⁻¹ (3193), X05's weak-star/weighted lower semicontinuity (3332–3338), and X06's C¹ compactness/ODE limit (3365–3367) and pullback naturality. | Add consumers and precise descriptions of the tools, all still awaiting verification/implementation. No slice responsibility was upgraded to proved. |
| SR7 | Although C04 used subscript notation, its explicit text did not fully exclude δ/ℓ dependence in the final limits. | Make the first constant independent of both δ and ℓ; the latter two may depend on fixed δ but are independent of ℓ. Retain the order n, then ℓ, then δ, without strengthening the paper's target. |
| SR8 | X03 incorrectly said “degree-one moment” and referred generically to the Einstein-specific eq:moment, risking replacement of given T by G(m). | State the second-moment identity with T on the left and `T≠G(m)`. Positive degree-one homogeneity belongs only to transport tests. |
| SR9 | X06's limiting transformed objects were mainly inferred from context. | State B=cos u, the transformed limiting metric, Ricci tensor, and `H_{P_g̃}` explicitly. Retain local uniform convergence, local uniform first-derivative bounds, and the transformed volume weight. |

## Exact counterexample to the omitted phase-gap condition

Take the Minkowski quadratic form and the nonzero null covector $k=(1,1,0,0)$, with

$$
\kappa=1/32,\quad\varepsilon=1/320,\qquad
p=\varepsilon k,\quad q=k,\quad r=-(1+\varepsilon)k.
$$

All three frequencies are nonzero and exactly null, sum to zero, and p is smallest. The low-frequency cutoff argument is

$$
\frac{|p|^2}{\kappa^2(|q|^2+|r|^2)}
=\frac{1024}{205441}<\frac14,
$$

so $L_p=1$. Every projective angular separation is zero, hence $N_p=1$ for any allowed positive δ, and

$$\Delta=q_m(q+p)-q_m(q)=0.$$

This refutes the preceding slice summary after omission of the angular-far condition, not the paper's assertion on far support; the example lies outside far support. The main agent reconstructed it exactly with Fraction, and `.project-verification/slicing-review/check_phase_scope.py` actually exited 0. This check is not a general proof of the far phase-gap theorem.

## Coverage conclusion and remaining boundaries

The 46 slices still cover 3475 lines continuously without overlap. The kinds, labels, and start/end locations of the 17 formal environments agree with the paper; statement/proof/closure mappings fully locate the original argument. Both user-approved unnumbered results remain mandatory and unformalized. Source intersections of all 70 inventory entries are retained. Links were revised from 136 to 135, distinguishing proof, definition, specification, application, and explanation.

No reason was found to repartition the main text, remove difficult results, or add assumptions to the paper. X08's three explanatory candidates and X09's regularity/actual-consumer explanation continue under scope and existing pending records. This round did not silently expand or narrow certification scope.

The 17 structural and packet regression tests actually passed. Inputs, results, and packet samples are saved under `.project-verification/slicing-review/`, `.project-verification/slicing/`, and `.project-verification/slice-packets/`. The paper, Lean sources, pinned dependencies, target registration, trust policy, and author semantic-confirmation states did not change.

This review concerns slice fidelity, relations, and implementation interfaces. Open PDE proofs, exact applicability of external original theorems, actual Lean types, and formal closure of necessary dependencies still require slice-by-slice work. Location coverage, agent agreement, and passing structural tests do not constitute a whole-paper formal-verification label.
