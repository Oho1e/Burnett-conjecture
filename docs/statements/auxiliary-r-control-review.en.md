# Independent review of auxiliary-r local control

This document summarizes actual reverse readback of the frozen sources in this batch. Its mathematical explanation is based on actual types, important definitions, and locked source lines 91–105 and 352–389. Complete source hashes and support targets are in the [bindings](auxiliary-r-control-source-bindings.json). User/author semantic confirmation has not been recorded; whole-paper verified remains false.

| Module | Forward implementation | Independent readback | Precise scope |
| --- | --- | --- | --- |
| GramCoordinateBound | N1 | N3 | Actual Gram energy, constructed Hilbert norm, inverse-diagonal coordinate bound |
| CovariantTensorNorm | N2 | N1 | Concrete order-two/three Kronecker tensors, flattening, physical contractions, and compact-set constants |
| LocalAeBound | N3 | N2 | A.e.-to-pointwise on a larger neighborhood, actual volume, F-valued MemLp∞ |
| AuxiliaryConnection | root | N1 | Actual Γr auxiliary derivative, compact uniform connection bound, raw-jet recovery |
| ConnectionErrorLInfinity | root | N3 | Actual E continuity, MemLp∞, and convergence of actual classes for the same E/K |
| AuxiliaryPhysicalBound | root | N3 | Assembly from local physical L∞ to actual uniform/L∞ convergence of E |
| PositiveDensity | N1 | root | Actual positive-density restricted measures and L∞ bridge |
| RiemannianVolume | N2 | root | Actual sqrt(detR) coordinate measure and r consumer |

N1 authored generic Gram but did not construct N2's concrete tensor module; N1's independent scope is limited to the latter, while N3 reviewed generic Gram. N3 authored LocalAeBound and, when reviewing root's E/Physical modules, consumed it only as a frozen dependency independently checked by N2. root did not implement the positive-density or coordinate-volume modules.

Checked stress cases include R=4I, where a pure-coordinate order-three tensor has physical norm3=1/8 but Pi norm=1 and attains the correct comparison factor8. Lean actually refutes the reversed bound using diagonal entries of R⁻¹. Other cases show that an a.e. bound on null K={0} cannot directly give a pointwise bound, and check MemLp∞ for an actual F-valued continuous function when μ(K) is infinite. Stress cases supplement complete source/type checking rather than replacing the general proofs.

Complete readback must cover every explicit public declaration, with additional definition and transitive-axiom queries. Only propext, Classical.choice, and Quot.sound are accepted. sorryAx from unfinished probes and compilation failures are preserved separately as failed history, not accepted receipts. The original InversePerturbation unused-hB warning is retained; no warning-free whole-project claim is made.

These remain local coordinate results. Original manifold charts, identification of geometric D and pushed-forward volume, the physical-r norm of mixed (1,2) errors, and analytic closure of F04 remain unfinished. The original −B sign, earlier confirmation scopes, all 17 numbered and 3 required unnumbered targets, trust policy A, and source bytes are unchanged. New explanations await the required human confirmation; PR merging is development integration only.

All independent complete-source/type/transitive-axiom receipts for the final 8 modules and 85 explicit declarations (15 definitions, 70 theorems) have actual exit0. The table binds actual independent reports; receipt byte hashes are in the source bindings, with original logs and failed history retained in the archive.

| Module | Independent report SHA256 |
| --- | --- |
| GramCoordinateBound | `fc5331ed502b7c9a88d8a39b6ef26a9dd25287c7df6a1d9dfea8ab930029fb30` |
| CovariantTensorNorm | `8fc8d169fe6f93bb240320d0a812a998f460faf30010472d2900773a379d11c5` |
| LocalAeBound | `c476e9bfa21c70e2de25e481e7a1cae9e500ca62252b537cd6f93bee5742f377` |
| AuxiliaryConnection | `bc03caba07537d7eb3bacd8f33745c6960f87702fcfac8c091f7648ea8fd7c03` |
| ConnectionErrorLInfinity | `3cb29cb03d065f2efc78b28826a718949d53ebf0781288c40fac92854b4d4879` |
| AuxiliaryPhysicalBound | `5176a7f60be7dfa9330add3f3482cbf1f6513d20b046213c99d799b975beebe4` |
| PositiveDensity | `e5351bf15f410fae8c48956b6865f76ce5211116268c1aa60d1af1ef991033a9` |
| RiemannianVolume | `fd320129665fa02199de13fb259bc12e0c481335bb6ddbbeaa7abe5db5347645` |

Complete checks, actual merge-candidate CI, and artifact comparison for the 227-target/74-source candidate are performed separately. An older green 200-target result is not evidence for this candidate.

Before commit, CRLF in two new sources was normalized to repository-required LF. The actual normalized bytes are identical, so their mathematical explanations carry over; all 19 declarations were checked again under the current LF sources. The table and source bindings use the new LF receipts. Old reports and the first 227/74 receipt retain their historical identity; the complete candidate is rerun on final LF inputs rather than rewriting old evidence.
