# Independent readback of the local-control deliverable

2026-11-16. The source SHA256 remains `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`. See [local-metric-control.md](local-metric-control.en.md) for the precise explanation and the [bindings](local-metric-control-source-bindings.json) for frozen sources and 24 new support targets.

| Module | Forward construction | Independent readback | Precise scope |
| --- | --- | --- | --- |
| InversePerturbation | N2 | N1 | Actual sup norm, matrix composition, constants 4/16/2/32, actual FiberMetric inverse laws; 20 declarations passed |
| InverseField | N2 | N3 | Explicit matrix inverse, inverse continuity, B from compactness, actual uniform sequence control; 16 declarations and a nondiagonal-block stress example passed |
| InverseSequence | N2 | N3 | Same B and eventual smallness/bounds connected to contravariant and uniform convergence on subtype K; 2 declarations passed |
| BackgroundConnection | N2 | N3 | Local C¹ gives actual ambient-fderiv jet/Γ continuity, compactness gives G; 8 declarations passed |
| ConnectionError | N1 | N3 | Actual E definition and identity, 6/192, fixed K and uniform convergence; 14 declarations passed |
| PerturbationJet | N1 | N3 | norm8 and raw→J→E consumers, with original-r interface explicitly open; 8 declarations passed |
| ConnectionErrorSequence | N1 | N3 | Actual final local-coordinate assembly 17b524, complete source and all 3 theorem types/axioms exit0, eliminating intermediate B/G/J/small/hcΓ premises |
| UniformLInfinity | root | N2 | Actual Lp∞/restrict, no finite-total-measure premise, finite upper bound before toReal, explicit MemLp; 3 declarations and boundary examples passed |
| PositiveFunctional | N3 | root | Actual C_c/subspace, positivity, C0 norm, and actual Urysohn local bound; 4 declarations passed |

Independent readback starts from complete frozen source, actual types, and important definitions. An identical hash for an already-reviewed inverse core can serve as a consumer input, but an author summary cannot replace readback. Query counts guard against omitted declarations; they are not article-result counts. All completed Lean and transitive-axiom queries exited 0, using only the three allowed foundational axioms. The original InversePerturbation retains an unused-hB warning, not a mathematical error; its frozen type was not changed merely to clean up the warning.

All nine production sources independently PASS, with no unresolved must-fix issues. Their 78 explicit public declarations (71 theorems, 7 definitions) underwent complete type/transitive-axiom checks: 51 across N3's six-source summary, N1's 20 inverse-core items, N2's 3 Lp∞ items, and root's 4 positive-functional items. Additional stress instances are not counted again as production declarations. The final assembly obtains actual G directly, without the earlier explanatory detour through backgroundConnectionOn continuity; that intermediate path is not a new open obligation.

The nondiagonal stress test confirms off-diagonal inverse entries −1/3 for `[[2,1],[1,2]]⊕I₂`, distinguishing matrix inversion from entrywise reciprocation. UniformLInfinity's zero-bound/empty-set cases were actually checked without a finite-measure instance hiding assumptions. Independent Lean for PositiveFunctional itself exited0; its initial terminal wrapper failed in GBK printing after writing the success receipt. UTF-8 readback later verified all four axiom reports. The original log is preserved, and the wrapper as a whole is not falsely reported as exit0.

The main scope check concerned the source's `D=∇ʳ` and physical-r norm. The final coordinate assembly, general Lp∞ bridge, and positive-functional bound do not replace that unclosed geometric bridge. Explicit inputs of the new general tools are not treated as already satisfied original PDO/admissibility assumptions. F04/F05 parents and the whole paper are not upgraded to proved; new author confirmation is pending.

The user merged PR7 and actual main CI succeeded; the current baseline is d5c3d06. This batch's code/targets/explanations enter one new candidate, whose actual combined checks and remote evidence are obtained separately rather than inheriting the earlier green 176-target result. Final merging remains a human action; subagent reports are not an Approve from another GitHub account.
