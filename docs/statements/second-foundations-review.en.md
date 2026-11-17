# Independent readback of actual types in the second foundations batch

2026-11-16. Source SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`; continued from reviewed first-batch candidate `d143c3709466bd2900e098c573c1691d987226da`. See [second-foundations.md](second-foundations.en.md) for the mathematics and [second-foundations-source-bindings.json](second-foundations-source-bindings.json) for per-file frozen hashes and registration bindings.

## Responsibilities and actual readback

| Module | Forward constructor | Reviewer not involved in that construction | Readback and scope |
| --- | --- | --- | --- |
| SchwartzDensity | N1 | N2 | Genuine complex Lp²(volume) norm density; fixed bump controls whole-space error without finite-total-volume or density premises |
| L2Extension | N1 | N2 | Isometric extension on an actual L² image subspace, surjectivity/inverse and a.e. agreement with both Schwartz integrals; not expanded to general L¹∩L² |
| Projection | N1 | N3 | Actual F⁻¹mF and symbol multiplication, norm/support-energy bounds, with all physical output tails retained |
| SharpProjection | N1 | N3 | Actual indicator projection idempotence/orthogonality; additional actual norm≤1 instance; a.e.-equal symbols give the same operator |
| OffNullProjection | N1 | N3 | Actual parent at3193 passed: same f/w, all χ, fixed δ/symbol, four-component full-space positive L², both cutoff positions and zero frequency; actual sharp/smooth instances checked |
| ConnectionDifference | N2 | N3 | Actual bilinear metrics, inverse direction, Fréchet coordinate derivatives and local assumptions; no connection conclusion hidden in fields |
| CurvatureDifference | root | N2 | Indexwise (1,2) covariant derivative, every Ricci derivative/quadratic term and vacuum signs; actual fderiv difference |
| CurvatureSymbolBridge | root | N2 | New Christoffel on a rank-one jet equals the old symbol; exact Ricci quadratic correction is minus old B, with no extra symmetry/nondegeneracy premise |
| PositiveKernel | N3 | N2 | Actual range≤ker with singular M allowed; independent nonzero example also uses infinite system rows m=ℕ |
| DenseTests | N1 | N2 | Actual unique CLM, convergence at all points and same-C norm bound from explicit uniform opNorm and dense-set convergence; consumes vanishing-error positivity rather than generating PDO/Gårding inputs |

Independent readback is complete for all ten modules, with no unresolved must-fix issue. Complete frozen sources and important definitions were actually recompiled and public types/transitive axioms queried, all exit0 with zero warnings and only the three agreed foundational axioms. Separate actual receipts cover density3, extension20, connection25, curvature14, symbol bridge3, kernel4, and dense extension6. The three projection files additionally have all49 production declarations queried and four independent contraction/sharp-four-component/zero-frequency-smooth instances checked. The five Fourier sources contain72 explicitly named public declarations, including one on the same line as an attribute, which the independent audit checked. Query counts guard against omissions; they are not article-result counts.

## Adversarial concerns and resolutions

- L² extension uses the actual inclusion of an L² subspace. The continuous injection Schwartz→L² is not treated as a uniform embedding, avoiding confusion between the topologies.
- No L² estimate multiplies a whole-space uniform error by total volume; the finite L² norm of a fixed compactly supported bump gives actual control.
- No operator is assumed to annihilate the counterexample sequence. Multipliers are actually constructed from frequency symbols; concrete strong vanishing consumes proved frequency energy of the same witnesses.
- The exact Ricci identity has the opposite quadratic sign to F06 B. Three new Lean theorems establish that sign, which later consumers must retain.
- The kernel lemma does not require an invertible positive density, and finite-dimensional zero compression is not promoted to an a.e. measure conclusion; Gram/covariance conventions still need actual identification.
- Initial bare-line enumeration in forward evidence missed `localizedGradientSchwartz_apply` on the same line as `@[simp]`. Attribute-aware independent enumeration found and actually checked the production theorem. The coordinator required all72 forward queries while retaining the original71 receipt. Production source/proofs were unchanged; central targets still undergo actual Lean existence/source/transitive-axiom checks.

## Status and unclosed obligations

F04 still needs actual coordinate connection fields instantiated from metric-field regularity, uniform metric-inverse and Eₙ estimates, weak Ricci limits, and H⁻¹ compactness. F05 still needs actual PDO tests, a positive functional and the same global bundle-valued measure, a.e. localization, and coordinate naturality. This batch does not prove measures, transport, or the main theorem.

Author confirmation of the new explanations has not been recorded; earlier local delegation does not expand to this batch. Independent subagent reports do not impersonate a human or an Approve from another GitHub account. The final engineering receipts separately verify entry points, target existence/source/axioms, and actual input boundaries; remote candidate/main CI does not inherit an older PR's green status. The whole paper remains `development`, `verified=false`.

PR6 was user-merged as main `b4b27302556c62617798a46a22e744035fcd4602`; push CI43861529888 succeeded, with all137-target/47-source inputs identical to the reviewed version. The original nine sources in this batch are byte-identical to candidate67fa; the whole earlier candidate tree is unchanged after rebasing, so prior mathematical readback carries over through precise hashes. New DenseTests separately passed six forward/independent readbacks, with frozen SHA `6677f6d6de3dcb9228373da086718adcb99c54bca3b2ccde354ef8d15483f887`. Machine/remote evidence for the new scope/base combination is obtained from actual receipts, without rewriting the earlier174-target record.
