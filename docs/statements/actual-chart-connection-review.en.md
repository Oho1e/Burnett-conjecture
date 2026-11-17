# Independent readback of actual-chart and global-connection support results

All 12 modules and 102 public declarations underwent independent per-source readback of complete definitions and proofs, with actual checks of all types and transitive axioms, using only the three allowed foundational axioms. Declarations with attributes on the same line are counted. Each independent reviewer did not construct the new source reviewed; earlier participation in existing dependencies is recorded separately in the reports.

| Module | Declarations | Independent report SHA256 |
| --- | --- | --- |
| ActualChartSecondJet | 3 | `0e5373ebafec2d9e555b9da09b841df57ae05c58e06610da891c5a8197db38f1` |
| MetricJetNaturality | 11 | `f4acda66d07b813e3ab5366daeb07e4291151898ee542ac78280315c7f7f10b7` |
| ConnectionTermNaturality | 11 | `223935ca64bf9765f5ef2263386f45c238816734c2d503f5cab5473f95172d1c` |
| ChartVectorField | 18 | `69476d2a853dbb0c897f05234d20886d0fb4c81618c419e31c08ac26563666fb` |
| ChartConnectionNaturality | 6 | `03ac69f853821bb5d384394ef3e36494978a53210703b74d0cb7b41801a14435` |
| ManifoldVolumeRegularity | 7 | `6909135423ae5ddbc595bc31352a5b09f82b6627c714c8c1ecedacf4dff53163` |
| SmoothMetricConnection | 7 | `8377071203f35f68427eaae2dd5b2918136d956a52940ad20e757ac5e0b991ea` |
| GlobalCovariantDerivative | 8 | `8a5b8ccea75192a4ab09c80362d401293a26ba21c1f2cf90c23f5642b2534b79` |
| ChartDifferential | 6 | `604f38244454f83c721aad5d2d10aafd0dcc69ddbb2dc6fa7ca28350be09b7da` |
| ChartLieBracket | 6 | `116502ceb9aec909e722a1fa7f804447dee6e0fb947adf64b7d1a7bc55cc91b6` |
| GlobalLeviCivita | 9 | `729bb98988e1dd4b058ce992c8402adf313538887e460a15f31f2387a42a887f` |
| GlobalConnectionLaws | 10 | `0bb37fc9f1aa1722e7b07a12cffa21c491c788eeb1b91f6a1ee26bc15af26659` |

See the [explanation](actual-chart-connection.en.md) for mathematical scope and the [JSON](actual-chart-connection-source-bindings.json) for source/report/receipt byte bindings.

The independent reviews checked the actual chart Hessian rather than a supplied second jet, the complete nonlinear H terms, genuine Matrix inversion, the same-B chart law, and open-set function germs. They cover the two-way bridge between genuine tangent-bundle sections and coordinate smoothness, elimination of the Γ premise from smoothness of global outputs, actual mfderiv, and mathlib's actual manifold Lie bracket.

GlobalConnectionLaws proves algebraic laws for the canonical raw operator without requiring smooth B. Geometric naturality, closure under smoothness, and metric properties still require the original smooth/symmetric/nondegenerate assumptions. The pointwise section and scalar differentiability needed for differentiation remain explicit. Actual positive definiteness of auxiliary r supplies nondegeneracy, without a global smooth frame or uniform D²g_n bound.

The volume conclusions concern geometricMeasure on the base manifold: local finiteness follows from actual smoothness, while open-set positivity additionally requires nondegeneracy. No unproved measure-property field is supplied. Radon regularity, extension to arbitrary maximal-atlas charts, phase-space defect μ, full Lorentz/time orientation, original intrinsic Dh, and the physical cov3 norm remain OPEN. Uniqueness of abstract global connection operators is not claimed.

All 39 new registrations are support targets and do not close F04/F05/the main theorem. The old 285 targets, 356 inventory entries, 92 mathematical leaf sources, article, locks, and earlier confirmations are preserved. Author confirmation of the new explanation is pending; whole-paper verified=false. Complete checks of the 324-target/395-inventory/105-source candidate, actual CI with main, and artifact review require current receipts; an older green result is not extended into a new proof.

Engineering integration review, per-source mathematical review, and human author confirmation are recorded separately; agent actions under the same account are not an Approve from an independent GitHub account. The user performs the final main merge, while independent successor tasks continue under GOAL once the PR is ready.
